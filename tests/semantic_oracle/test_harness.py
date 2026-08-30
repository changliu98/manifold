import json
import os
import subprocess
import tempfile
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
HARNESS = ROOT / "scripts" / "semantic_oracle.py"


class SemanticOracleHarnessTest(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="semantic_oracle_test_")
        self.work = Path(self.temp.name)
        source = self.work / "source.c"
        source.write_text(
            "#include <unistd.h>\n"
            "int main(int argc, char **argv) {\n"
            "  char out = (char)('A' + argc), err = (char)('x' + argc);\n"
            "  (void)argv; write(1, &out, 1); write(2, &err, 1); return argc + 1;\n"
            "}\n"
        )
        manifest = {
            "schema_version": 1,
            "suite": "harness-self-test",
            "cases": [
                {
                    "name": "probe",
                    "source": "source.c",
                    "cflags": ["-O1"],
                    "runs": [
                        {"name": "zero", "args": [], "expected": {"returncode": 2, "stdout": "B", "stderr": "y"}},
                        {"name": "one", "args": ["x"], "expected": {"returncode": 3, "stdout": "C", "stderr": "z"}},
                    ],
                }
            ],
        }
        self.manifest = self.work / "manifest.json"
        self.manifest.write_text(json.dumps(manifest))
        self.fake = self.work / "fake_manifold.py"
        self.fake.write_text(
            "#!/usr/bin/env python3\n"
            "import os, shutil, sys\n"
            "shutil.copyfile(os.environ['ORACLE_FAKE_C'], sys.argv[2])\n"
        )
        self.fake.chmod(0o755)

    def tearDown(self):
        self.temp.cleanup()

    def run_gate(self, recovered_source):
        candidate = self.work / "candidate.c"
        candidate.write_text(recovered_source)
        output = self.work / ("output_" + str(len(list(self.work.glob("output_*")))))
        env = os.environ.copy()
        env["ORACLE_FAKE_C"] = str(candidate)
        proc = subprocess.run(
            [
                str(HARNESS),
                "--manifold",
                str(self.fake),
                "--manifest",
                str(self.manifest),
                "--output",
                str(output),
                "--jobs",
                "1",
            ],
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            env=env,
            timeout=30,
        )
        return proc, json.loads((output / "summary.json").read_text())

    def test_pass_mismatch_and_recompile_error_are_distinct(self):
        passing = (
            "#include <unistd.h>\n"
            "int main(int argc, char **argv) { char out = 'A' + argc, err = 'x' + argc; "
            "(void)argv; write(1, &out, 1); write(2, &err, 1); return argc + 1; }\n"
        )
        proc, summary = self.run_gate(passing)
        self.assertEqual(proc.returncode, 0, proc.stderr)
        self.assertEqual(summary["totals"]["outcomes"], {"pass": 1})
        self.assertEqual(
            summary["totals"]["behavior_equivalent_end_to_end"]["passed"], 1
        )

        mismatch = "int main(void) { return 99; }\n"
        proc, summary = self.run_gate(mismatch)
        self.assertEqual(proc.returncode, 1)
        self.assertEqual(summary["totals"]["outcomes"], {"behavior_mismatch": 1})
        self.assertEqual(summary["totals"]["recompiled_end_to_end"]["passed"], 1)
        self.assertEqual(
            summary["totals"]["behavior_equivalent_end_to_end"]["passed"], 0
        )

        proc, summary = self.run_gate("this is not C\n")
        self.assertEqual(proc.returncode, 1)
        self.assertEqual(summary["totals"]["outcomes"], {"recompile_error": 1})
        self.assertEqual(summary["totals"]["recompiled_end_to_end"]["passed"], 0)


if __name__ == "__main__":
    unittest.main()
