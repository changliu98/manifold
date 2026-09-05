#!/usr/bin/env python3
"""Fast black-box semantic regression gate for Manifold.

For each fixture this compiles the source, validates the reference executable
against checked-in observations, decompiles it, recompiles the emitted C, and
compares exact process observations for every stimulus.  The artifact directory
is retained and contains every command's stdout/stderr plus per-variant JSON.
"""

from __future__ import annotations

import argparse
import collections
import concurrent.futures
import datetime as dt
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import time
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_MANIFEST = ROOT / "tests" / "semantic_oracle" / "cases.json"
SANITIZER_RE = re.compile(
    rb"AddressSanitizer|UndefinedBehaviorSanitizer|runtime error:|"
    rb"SUMMARY: (?:AddressSanitizer|UndefinedBehaviorSanitizer)"
)


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def write_json(path: Path, value: object) -> None:
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")


def controlled_env(extra: dict[str, str] | None = None) -> dict[str, str]:
    env = os.environ.copy()
    env["LC_ALL"] = "C"
    env["LANG"] = "C"
    env["TZ"] = "UTC"
    if extra:
        env.update(extra)
    return env


def _bytes(value: bytes | str | None) -> bytes:
    if value is None:
        return b""
    return value if isinstance(value, bytes) else value.encode("utf-8", "surrogateescape")


def run_command(
    command: list[str],
    work: Path,
    tag: str,
    timeout: float,
    *,
    stdin: bytes = b"",
    env_extra: dict[str, str] | None = None,
    cwd: Path | None = None,
) -> dict:
    """Run one command and retain byte-exact streams and invocation metadata."""
    stdout_path = work / f"{tag}.stdout"
    stderr_path = work / f"{tag}.stderr"
    command_path = work / f"{tag}.command.json"
    started = time.monotonic()
    status = "completed"
    returncode = None
    stdout = b""
    stderr = b""
    error = None
    env = controlled_env(env_extra)
    process_cwd = cwd or work
    try:
        proc = subprocess.run(
            command,
            input=stdin,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            cwd=process_cwd,
            env=env,
            timeout=timeout,
            check=False,
        )
        returncode = proc.returncode
        stdout = proc.stdout
        stderr = proc.stderr
    except subprocess.TimeoutExpired as exc:
        status = "timeout"
        stdout = _bytes(exc.stdout)
        stderr = _bytes(exc.stderr)
        error = f"timed out after {timeout:g}s"
    except OSError as exc:
        status = "spawn_error"
        error = str(exc)
        stderr = str(exc).encode("utf-8", "replace")
    seconds = round(time.monotonic() - started, 3)
    stdout_path.write_bytes(stdout)
    stderr_path.write_bytes(stderr)
    invocation = {
        "argv": command,
        "cwd": str(process_cwd),
        "environment_overrides": {
            "LANG": env["LANG"],
            "LC_ALL": env["LC_ALL"],
            "TZ": env["TZ"],
            **(env_extra or {}),
        },
        "stdin_sha256": hashlib.sha256(stdin).hexdigest(),
        "timeout_seconds": timeout,
    }
    write_json(command_path, invocation)
    return {
        "status": status,
        "returncode": returncode,
        "signal": -returncode if returncode is not None and returncode < 0 else None,
        "seconds": seconds,
        "error": error,
        "stdout_path": stdout_path.name,
        "stderr_path": stderr_path.name,
        "command_path": command_path.name,
        "stdout_sha256": hashlib.sha256(stdout).hexdigest(),
        "stderr_sha256": hashlib.sha256(stderr).hexdigest(),
        "stdout_bytes": len(stdout),
        "stderr_bytes": len(stderr),
        "_stdout": stdout,
        "_stderr": stderr,
    }


def public_run(run: dict) -> dict:
    return {key: value for key, value in run.items() if not key.startswith("_")}


def command_succeeded(run: dict, output: Path | None = None) -> bool:
    return (
        run["status"] == "completed"
        and run["returncode"] == 0
        and (output is None or (output.is_file() and output.stat().st_size > 0))
    )


def process_observation(run: dict) -> dict:
    return {
        "returncode": run["returncode"],
        "stdout_sha256": run["stdout_sha256"],
        "stderr_sha256": run["stderr_sha256"],
        "stdout_bytes": run["stdout_bytes"],
        "stderr_bytes": run["stderr_bytes"],
    }


def expected_bytes(expected: dict, key: str) -> bytes:
    value = expected.get(key, "")
    if not isinstance(value, str):
        raise ValueError(f"expected.{key} must be a string")
    return value.encode("utf-8", "surrogateescape")


def observation_mismatches(actual: dict, expected_run: dict) -> list[str]:
    mismatches = []
    if actual["returncode"] != expected_run["returncode"]:
        mismatches.append("returncode")
    if actual["_stdout"] != expected_run["_stdout"]:
        mismatches.append("stdout")
    if actual["_stderr"] != expected_run["_stderr"]:
        mismatches.append("stderr")
    return mismatches


def validate_manifest(path: Path) -> tuple[dict, list[dict]]:
    value = json.loads(path.read_text())
    if value.get("schema_version") != 1:
        raise ValueError("manifest schema_version must be 1")
    cases = value.get("cases")
    if not isinstance(cases, list) or not cases:
        raise ValueError("manifest cases must be a non-empty list")
    seen = set()
    for case in cases:
        name = case.get("name")
        if not isinstance(name, str) or not re.fullmatch(r"[a-z0-9][a-z0-9_-]*", name):
            raise ValueError(f"invalid case name: {name!r}")
        if name in seen:
            raise ValueError(f"duplicate case name: {name}")
        seen.add(name)
        source = path.parent / case.get("source", "")
        if not source.is_file():
            raise ValueError(f"missing source for {name}: {source}")
        runs = case.get("runs")
        if not isinstance(runs, list) or not runs:
            raise ValueError(f"case {name} has no runs")
        run_names = set()
        for stimulus in runs:
            run_name = stimulus.get("name")
            if not isinstance(run_name, str) or not re.fullmatch(
                r"[a-z0-9][a-z0-9_-]*", run_name
            ):
                raise ValueError(f"invalid run name in {name}: {run_name!r}")
            if run_name in run_names:
                raise ValueError(f"duplicate run name in {name}: {run_name}")
            run_names.add(run_name)
            expected = stimulus.get("expected")
            if not isinstance(expected, dict) or not isinstance(
                expected.get("returncode"), int
            ):
                raise ValueError(f"case {name}/{run_name} needs expected.returncode")
            expected_bytes(expected, "stdout")
            expected_bytes(expected, "stderr")
    return value, cases


def compiler_identity(command: str) -> dict:
    resolved = shutil.which(command)
    if resolved is None:
        raise ValueError(f"compiler is absent from PATH: {command}")
    path = Path(resolved).resolve()
    probe = subprocess.run(
        [str(path), "--version"], capture_output=True, text=True, timeout=15, check=False
    )
    return {
        "requested": command,
        "path": str(path),
        "sha256": sha256(path),
        "version": (probe.stdout or probe.stderr).splitlines()[0],
    }


def copy_reference_binary(source: Path, target: Path) -> None:
    shutil.copy2(source, target)
    target.chmod(target.stat().st_mode | 0o111)


def run_fixture(
    case: dict,
    compiler: dict,
    manifest_dir: Path,
    run_root: Path,
    manifold: Path,
    recompiler: dict,
    args: argparse.Namespace,
) -> dict:
    variant_name = f"{case['name']}__{Path(compiler['path']).name}"
    work = run_root / "cases" / variant_name
    work.mkdir(parents=True)
    source = manifest_dir / case["source"]
    local_source = work / "source.c"
    shutil.copy2(source, local_source)
    result = {
        "case": case["name"],
        "description": case.get("description", ""),
        "compiler": compiler["path"],
        "artifact_dir": str(work),
        "source_sha256": sha256(local_source),
        "stimuli_total": len(case["runs"]),
        "stages": {
            "reference_compile": False,
            "reference_fixture_valid": False,
            "decompile": False,
            "recompile": False,
            "behavior_equivalent": None,
        },
        "outcome": None,
    }

    unstripped = work / "reference.unstripped"
    reference = work / "reference.bin"
    compile_target = unstripped if args.strip else reference
    compile_cmd = [
        compiler["path"],
        "-std=gnu11",
        *case.get("cflags", ["-O2"]),
        "-fno-pie",
        "-no-pie",
        "-fno-stack-protector",
        str(local_source),
        "-o",
        str(compile_target),
    ]
    compile_run = run_command(
        compile_cmd, work, "reference_compile", args.compile_timeout
    )
    result["reference_compile"] = public_run(compile_run)
    if not command_succeeded(compile_run, compile_target):
        result["outcome"] = "reference_compile_error"
        write_json(work / "result.json", result)
        return result
    result["stages"]["reference_compile"] = True

    if args.strip:
        copy_reference_binary(unstripped, reference)
        strip_command = shutil.which("strip")
        if strip_command is None:
            result["outcome"] = "fixture_error"
            result["fixture_error"] = "strip requested but strip is absent from PATH"
            write_json(work / "result.json", result)
            return result
        strip_run = run_command(
            [strip_command, "--strip-all", str(reference)],
            work,
            "strip",
            args.compile_timeout,
        )
        result["strip"] = public_run(strip_run)
        if not command_succeeded(strip_run, reference):
            result["outcome"] = "fixture_error"
            write_json(work / "result.json", result)
            return result

    binary_checks = case.get("binary_checks", [])
    if binary_checks:
        objdump = shutil.which("objdump")
        if objdump is None:
            result["outcome"] = "fixture_error"
            result["fixture_error"] = "binary checks require objdump"
            write_json(work / "result.json", result)
            return result
        disassembly = run_command(
            [objdump, "-d", str(reference)],
            work,
            "reference_disassembly",
            args.compile_timeout,
        )
        check_results = []
        text = disassembly["_stdout"].decode("utf-8", "replace")
        for check in binary_checks:
            pattern = check["regex"]
            check_results.append(
                {
                    "description": check.get("description", pattern),
                    "regex": pattern,
                    "matched": re.search(pattern, text, re.MULTILINE) is not None,
                }
            )
        result["binary_checks"] = check_results
        result["reference_disassembly"] = public_run(disassembly)
        if not command_succeeded(disassembly) or not all(
            check["matched"] for check in check_results
        ):
            result["outcome"] = "fixture_error"
            result["fixture_error"] = "compiled binary does not contain the required mechanism"
            write_json(work / "result.json", result)
            return result

    reference_runs = []
    reference_valid = True
    for stimulus in case["runs"]:
        run_name = stimulus["name"]
        run = run_command(
            [str(reference), *stimulus.get("args", [])],
            work,
            f"run_{run_name}_reference",
            args.run_timeout,
            stdin=stimulus.get("stdin", "").encode("utf-8", "surrogateescape"),
        )
        expected = stimulus["expected"]
        expected_run = {
            "returncode": expected["returncode"],
            "_stdout": expected_bytes(expected, "stdout"),
            "_stderr": expected_bytes(expected, "stderr"),
        }
        mismatches = observation_mismatches(run, expected_run)
        valid = run["status"] == "completed" and run["returncode"] is not None and not mismatches
        reference_valid &= valid
        reference_runs.append(
            {
                "name": run_name,
                "valid": valid,
                "fixture_mismatches": mismatches,
                "expected": {
                    "returncode": expected["returncode"],
                    "stdout_sha256": hashlib.sha256(expected_run["_stdout"]).hexdigest(),
                    "stderr_sha256": hashlib.sha256(expected_run["_stderr"]).hexdigest(),
                },
                "actual": public_run(run),
                "_run": run,
            }
        )
    result["reference_runs"] = [
        {key: value for key, value in row.items() if key != "_run"}
        for row in reference_runs
    ]
    if not reference_valid:
        result["outcome"] = "reference_fixture_invalid"
        write_json(work / "result.json", result)
        return result
    result["stages"]["reference_fixture_valid"] = True

    decompiled = work / "decompiled.c"
    decompile_run = run_command(
        [str(manifold), str(reference), str(decompiled)],
        work,
        "decompile",
        args.decompile_timeout,
        env_extra={"RAYON_NUM_THREADS": str(args.rayon_threads)},
    )
    result["decompile"] = public_run(decompile_run)
    if not command_succeeded(decompile_run, decompiled):
        result["outcome"] = "decompile_error"
        write_json(work / "result.json", result)
        return result
    result["stages"]["decompile"] = True
    result["decompiled_sha256"] = sha256(decompiled)

    recovered = work / "recovered.bin"
    recompile_run = run_command(
        [
            recompiler["path"],
            "-std=gnu11",
            "-" + args.recompile_opt,
            "-fno-pie",
            "-no-pie",
            "-fno-stack-protector",
            "-w",
            str(decompiled),
            "-o",
            str(recovered),
        ],
        work,
        "recompile",
        args.compile_timeout,
    )
    result["recompile"] = public_run(recompile_run)
    if not command_succeeded(recompile_run, recovered):
        result["outcome"] = "recompile_error"
        write_json(work / "result.json", result)
        return result
    result["stages"]["recompile"] = True

    recovered_runs = []
    behavior_equivalent = True
    for stimulus, reference_row in zip(case["runs"], reference_runs):
        run_name = stimulus["name"]
        run = run_command(
            [str(recovered), *stimulus.get("args", [])],
            work,
            f"run_{run_name}_recovered",
            args.run_timeout,
            stdin=stimulus.get("stdin", "").encode("utf-8", "surrogateescape"),
        )
        mismatches = observation_mismatches(run, reference_row["_run"])
        equivalent = run["status"] == "completed" and not mismatches
        behavior_equivalent &= equivalent
        recovered_runs.append(
            {
                "name": run_name,
                "equivalent": equivalent,
                "mismatches": mismatches,
                "reference_observation": process_observation(reference_row["_run"]),
                "recovered_observation": process_observation(run),
                "run": public_run(run),
            }
        )
    result["recovered_runs"] = recovered_runs
    result["stages"]["behavior_equivalent"] = behavior_equivalent
    result["outcome"] = "pass" if behavior_equivalent else "behavior_mismatch"

    if args.sanitizers:
        result["sanitizers"] = run_sanitizers(
            case, local_source, decompiled, work, recompiler, args
        )

    write_json(work / "result.json", result)
    return result


def run_sanitizers(
    case: dict,
    source: Path,
    decompiled: Path,
    work: Path,
    compiler: dict,
    args: argparse.Namespace,
) -> dict:
    common = [
        compiler["path"],
        "-std=gnu11",
        "-O1",
        "-g",
        "-fno-pie",
        "-no-pie",
        "-fno-stack-protector",
        "-fno-omit-frame-pointer",
        "-fsanitize=address,undefined",
        "-w",
    ]
    reference = work / "reference.sanitized.bin"
    recovered = work / "recovered.sanitized.bin"
    ref_compile = run_command(
        [*common, str(source), "-o", str(reference)],
        work,
        "sanitizer_reference_compile",
        args.compile_timeout,
    )
    rec_compile = run_command(
        [*common, str(decompiled), "-o", str(recovered)],
        work,
        "sanitizer_recovered_compile",
        args.compile_timeout,
    )
    value = {
        "reference_compile": public_run(ref_compile),
        "recovered_compile": public_run(rec_compile),
        "reference_compiled": command_succeeded(ref_compile, reference),
        "recovered_compiled": command_succeeded(rec_compile, recovered),
        "runs": [],
        "attribution_counts": {},
    }
    if not value["reference_compiled"] or not value["recovered_compiled"]:
        value["status"] = "compile_error"
        return value
    san_env = {
        "ASAN_OPTIONS": "detect_leaks=0:halt_on_error=1:abort_on_error=1:symbolize=0",
        "UBSAN_OPTIONS": "halt_on_error=1:print_stacktrace=0",
    }
    counts = collections.Counter()
    for stimulus in case["runs"]:
        name = stimulus["name"]
        stdin = stimulus.get("stdin", "").encode("utf-8", "surrogateescape")
        ref_run = run_command(
            [str(reference), *stimulus.get("args", [])],
            work,
            f"sanitizer_{name}_reference",
            args.run_timeout,
            stdin=stdin,
            env_extra=san_env,
        )
        rec_run = run_command(
            [str(recovered), *stimulus.get("args", [])],
            work,
            f"sanitizer_{name}_recovered",
            args.run_timeout,
            stdin=stdin,
            env_extra=san_env,
        )
        ref_diag = SANITIZER_RE.search(ref_run["_stderr"]) is not None
        rec_diag = SANITIZER_RE.search(rec_run["_stderr"]) is not None
        if rec_diag and not ref_diag:
            attribution = "recovered_only"
        elif ref_diag and rec_diag:
            attribution = "shared"
        elif ref_diag:
            attribution = "reference_only"
        else:
            attribution = "clean"
        counts[attribution] += 1
        value["runs"].append(
            {
                "name": name,
                "attribution": attribution,
                "reference_diagnostic": ref_diag,
                "recovered_diagnostic": rec_diag,
                "reference": public_run(ref_run),
                "recovered": public_run(rec_run),
            }
        )
    value["status"] = "completed"
    value["attribution_counts"] = dict(sorted(counts.items()))
    return value


def stage_fraction(passed: int, total: int) -> dict:
    return {
        "passed": passed,
        "total": total,
        "rate": round(passed / total, 6) if total else None,
    }


def summarize(results: list[dict]) -> dict:
    fixture_valid = [row for row in results if row["stages"]["reference_fixture_valid"]]
    decompiled = [row for row in fixture_valid if row["stages"]["decompile"]]
    recompiled = [row for row in fixture_valid if row["stages"]["recompile"]]
    equivalent = [
        row for row in fixture_valid if row["stages"]["behavior_equivalent"] is True
    ]
    compared_runs = [
        run
        for row in recompiled
        for run in row.get("recovered_runs", [])
    ]
    equivalent_runs = sum(run["equivalent"] for run in compared_runs)
    outcomes = collections.Counter(row["outcome"] for row in results)
    sanitizer_attribution = collections.Counter()
    sanitizer_variants = 0
    for row in results:
        sanitizer = row.get("sanitizers")
        if sanitizer is not None:
            sanitizer_variants += 1
            sanitizer_attribution.update(sanitizer.get("attribution_counts", {}))
    return {
        "variants": len(results),
        "outcomes": dict(sorted(outcomes.items())),
        "reference_fixture_valid": stage_fraction(len(fixture_valid), len(results)),
        "decompiled": stage_fraction(len(decompiled), len(fixture_valid)),
        "recompiled_end_to_end": stage_fraction(len(recompiled), len(fixture_valid)),
        "behavior_equivalent_end_to_end": stage_fraction(
            len(equivalent), len(fixture_valid)
        ),
        "behavior_equivalent_among_recompiled": stage_fraction(
            len(equivalent), len(recompiled)
        ),
        "stimuli_equivalent_among_compared": stage_fraction(
            equivalent_runs, len(compared_runs)
        ),
        "sanitizer_variants": sanitizer_variants,
        "sanitizer_attribution_stimuli": dict(sorted(sanitizer_attribution.items())),
    }


def resolve_manifold(args: argparse.Namespace, output: Path) -> tuple[Path, dict]:
    if args.manifold:
        executable = Path(args.manifold).expanduser().resolve()
        identity = {"selection": "explicit_binary"}
    else:
        checkout = Path(args.checkout).expanduser().resolve()
        if not (checkout / "Cargo.toml").is_file():
            raise ValueError(f"not a Manifold checkout: {checkout}")
        if args.build_checkout:
            setup = output / "setup"
            setup.mkdir(exist_ok=True)
            build = run_command(
                [
                    "cargo",
                    "build",
                    "--bin",
                    "manifold",
                    "--manifest-path",
                    str(checkout / "Cargo.toml"),
                ],
                setup,
                "cargo_build",
                args.build_timeout,
                env_extra={"CARGO_TARGET_DIR": str(checkout / "target")},
                cwd=checkout,
            )
            if not command_succeeded(build):
                raise ValueError(f"checkout build failed; inspect {setup}")
        executable = checkout / "target" / "debug" / "manifold"
        identity = {
            "selection": "checkout_debug_binary",
            "checkout": str(checkout),
        }
        try:
            identity["git_revision"] = subprocess.run(
                ["git", "-C", str(checkout), "rev-parse", "HEAD"],
                capture_output=True,
                text=True,
                timeout=10,
                check=True,
            ).stdout.strip()
            identity["git_dirty"] = bool(
                subprocess.run(
                    ["git", "-C", str(checkout), "status", "--porcelain"],
                    capture_output=True,
                    text=True,
                    timeout=10,
                    check=True,
                ).stdout
            )
        except (OSError, subprocess.SubprocessError):
            pass
    if not executable.is_file() or not os.access(executable, os.X_OK):
        hint = " (use --build-checkout)" if args.checkout else ""
        raise ValueError(f"Manifold executable not found: {executable}{hint}")
    identity.update(
        {
            "path": str(executable),
            "sha256": sha256(executable),
            "size_bytes": executable.stat().st_size,
        }
    )
    return executable, identity


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    select = parser.add_mutually_exclusive_group(required=False)
    select.add_argument("--manifold", help="path to an already-built Manifold executable")
    select.add_argument("--checkout", help="checkout whose target/debug/manifold should be used")
    parser.add_argument(
        "--build-checkout",
        action="store_true",
        help="incrementally cargo-build --checkout in Debug mode before the gate",
    )
    parser.add_argument("--manifest", type=Path, default=DEFAULT_MANIFEST)
    parser.add_argument("--case", action="append", default=[], help="case name; repeatable")
    parser.add_argument("--compiler", action="append", default=[], help="reference compiler; repeatable (default: gcc)")
    parser.add_argument("--recompiler", default="gcc", help="compiler for recovered C (default: gcc)")
    parser.add_argument("--recompile-opt", choices=["O0", "O1", "O2", "O3"], default="O0",
                        help="optimization level for recovered C (default: O0)")
    parser.add_argument("--output", type=Path, help="new artifact directory (default: retained directory under /tmp)")
    parser.add_argument("--jobs", type=int, default=2)
    parser.add_argument("--rayon-threads", type=int, default=2)
    parser.add_argument("--compile-timeout", type=float, default=30)
    parser.add_argument("--decompile-timeout", type=float, default=120)
    parser.add_argument("--run-timeout", type=float, default=5)
    parser.add_argument("--build-timeout", type=float, default=1800)
    parser.add_argument("--strip", action="store_true", help="strip fixture binaries before observation/decompilation")
    parser.add_argument("--sanitizers", action="store_true", help="attribute ASan/UBSan diagnostics on source vs recovered C")
    parser.add_argument("--list", action="store_true", help="list manifest cases and exit")
    parser.add_argument("--label", default="", help="free-form candidate label stored in summary.json")
    parser.add_argument("--json-stdout", action="store_true", help="print the final summary JSON to stdout")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    try:
        manifest_path = args.manifest.expanduser().resolve()
        manifest, cases = validate_manifest(manifest_path)
        if args.list:
            for case in cases:
                print(f"{case['name']}\t{case.get('description', '')}")
            return 0
        selected = set(args.case)
        unknown = selected - {case["name"] for case in cases}
        if unknown:
            raise ValueError("unknown cases: " + ", ".join(sorted(unknown)))
        if selected:
            cases = [case for case in cases if case["name"] in selected]
        if args.jobs < 1 or args.rayon_threads < 1:
            raise ValueError("--jobs and --rayon-threads must be positive")
        if args.build_checkout and not args.checkout:
            raise ValueError("--build-checkout requires --checkout")
        if not args.manifold and not args.checkout:
            default = ROOT / "target" / "debug" / "manifold"
            args.manifold = str(default)
        if args.output:
            output = args.output.expanduser().resolve()
            if output.exists():
                raise ValueError(f"refusing to overwrite existing output directory: {output}")
        else:
            stamp = dt.datetime.now(dt.timezone.utc).strftime("%Y%m%dT%H%M%SZ")
            output = Path("/tmp") / f"manifold-semantic-oracle-{stamp}-{os.getpid()}"
        output.mkdir(parents=True)
        (output / "cases").mkdir()
        started = dt.datetime.now(dt.timezone.utc)
        manifold_bin, manifold_identity = resolve_manifold(args, output)
        compiler_names = args.compiler or ["gcc"]
        compilers = [compiler_identity(name) for name in compiler_names]
        if len({compiler["path"] for compiler in compilers}) != len(compilers):
            raise ValueError("--compiler entries must resolve to distinct executables")
        recompiler = compiler_identity(args.recompiler)
        tasks = [(case, compiler) for case in cases for compiler in compilers]
        results = []
        with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as pool:
            futures = [
                pool.submit(
                    run_fixture,
                    case,
                    compiler,
                    manifest_path.parent,
                    output,
                    manifold_bin,
                    recompiler,
                    args,
                )
                for case, compiler in tasks
            ]
            for future in concurrent.futures.as_completed(futures):
                results.append(future.result())
        results.sort(key=lambda row: (row["case"], row["compiler"]))
        finished = dt.datetime.now(dt.timezone.utc)
        summary = {
            "schema_version": 1,
            "complete": True,
            "label": args.label,
            "started_at": started.isoformat(),
            "finished_at": finished.isoformat(),
            "elapsed_seconds": round((finished - started).total_seconds(), 3),
            "artifact_dir": str(output),
            "manifest": {
                "path": str(manifest_path),
                "sha256": sha256(manifest_path),
                "suite": manifest.get("suite", ""),
                "selected_cases": [case["name"] for case in cases],
            },
            "configuration": {
                "jobs": args.jobs,
                "rayon_threads": args.rayon_threads,
                "strip": args.strip,
                "sanitizers": args.sanitizers,
                "recompile_opt": args.recompile_opt,
                "compile_timeout_seconds": args.compile_timeout,
                "decompile_timeout_seconds": args.decompile_timeout,
                "run_timeout_seconds": args.run_timeout,
            },
            "manifold": manifold_identity,
            "reference_compilers": compilers,
            "recompiler": recompiler,
            "totals": summarize(results),
            "results": results,
        }
        write_json(output / "summary.json", summary)
        if args.json_stdout:
            print(json.dumps(summary, sort_keys=True))
        else:
            totals = summary["totals"]
            behavior = totals["behavior_equivalent_end_to_end"]
            recompiled = totals["recompiled_end_to_end"]
            stimuli = totals["stimuli_equivalent_among_compared"]
            print(
                f"semantic oracle: behavior {behavior['passed']}/{behavior['total']}; "
                f"recompiled {recompiled['passed']}/{recompiled['total']}; "
                f"stimuli {stimuli['passed']}/{stimuli['total']}"
            )
            print("outcomes: " + json.dumps(totals["outcomes"], sort_keys=True))
            print(f"artifacts: {output}")
            print(f"summary: {output / 'summary.json'}")
        return 0 if all(row["outcome"] == "pass" for row in results) else 1
    except (ValueError, OSError, json.JSONDecodeError) as exc:
        print(f"semantic_oracle.py: error: {exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
