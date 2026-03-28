mod debug;
mod decompile;
mod util;
mod x86;
use std::path::PathBuf;
use std::time::Instant;

fn fmt_elapsed(d: std::time::Duration) -> String {
    let secs = d.as_secs_f64();
    if secs < 1.0 {
        format!("{:.0}ms", secs * 1000.0)
    } else if secs < 60.0 {
        format!("{:.2}s", secs)
    } else {
        let mins = (secs / 60.0).floor() as u64;
        let rem = secs - (mins as f64 * 60.0);
        format!("{}m {:.2}s", mins, rem)
    }
}

fn print_usage_and_exit() -> ! {
    eprintln!(
        "Usage: manifold <BINARY> [OUTPUT_BASE] [OPTIONS]\n\n\
        	BINARY       - path to the ELF binary to decompile (file path)\n\
        	OUTPUT_BASE  - optional output path (defaults to <BINARY>.light.c)\n\n\
        Options:\n\
        	--trace          generate debug trace files (.debug.yaml, .dataflow.yaml)\n\
        	--dump-ir        dump each IR stage to separate files (.asm, .mach, .linear, etc.)\n\
        	--dump-clight-json   export selected Clight IR as JSON (.clight.json)\n\
        	--measure-rule-times  dump per-pass Ascent rule timing to debug/rule_times/\n\
        	--dump-deps          dump pipeline dependency graph as Graphviz DOT to pipeline.dot"
    );
    std::process::exit(1);
}

fn main() {
    let num_threads = std::env::var("RAYON_NUM_THREADS")
        .ok()
        .and_then(|v| v.parse::<usize>().ok())
        .unwrap_or_else(|| {
            std::thread::available_parallelism()
                .map(|n| n.get())
                .unwrap_or(8)
        });
    rayon::ThreadPoolBuilder::new()
        .num_threads(num_threads)
        .stack_size(64 * 1024 * 1024)
        .build_global()
        .expect("Failed to initialize Rayon global thread pool");

    let args: Vec<String> = std::env::args().collect();
    let mut positional = Vec::new();
    let mut trace_enabled = false;
    let mut measure_rule_times = false;
    let mut dump_ir = false;
    let mut dump_clight_json = false;
    let mut dump_deps = false;

    let mut iter = args.iter().skip(1);
    while let Some(arg) = iter.next() {
        match arg.as_str() {
            "--trace" => trace_enabled = true,
            "--measure-rule-times" => measure_rule_times = true,
            "--dump-ir" => dump_ir = true,
            "--dump-clight-json" => dump_clight_json = true,
            "--dump-deps" => dump_deps = true,
            s if s.starts_with('-') => {
                eprintln!("Unknown option: {}", s);
            }
            _ => positional.push(arg),
        }
    }

    // --dump-deps can run without a binary input
    if dump_deps {
        let (summary, detailed) = debug::pipeline_dot::dump_pipeline_deps();
        if let Err(e) = std::fs::write("pipeline.dot", &summary) {
            eprintln!("Failed to write pipeline.dot: {}", e);
            std::process::exit(1);
        }
        if let Err(e) = std::fs::write("pipeline-detailed.dot", &detailed) {
            eprintln!("Failed to write pipeline-detailed.dot: {}", e);
            std::process::exit(1);
        }
        println!("Pipeline dependency graph written to: pipeline.dot (summary), pipeline-detailed.dot (with internal rule deps)");
        if positional.is_empty() {
            std::process::exit(0);
        }
    }

    if positional.is_empty() || positional.len() > 2 {
        print_usage_and_exit();
    }

    let input_path = PathBuf::from(&positional[0]);
    if !input_path.exists() {
        eprintln!("Provided path does not exist: {}", input_path.display());
        print_usage_and_exit();
    }

    let explicit_output = positional.len() == 2;
    let out_file_path: PathBuf = positional.get(1).map(PathBuf::from).unwrap_or_else(|| {
        let mut s = input_path.to_string_lossy().into_owned();
        s.push_str(".light.c");
        PathBuf::from(s)
    });

    let total_start = Instant::now();

    let load_start = Instant::now();
    let mut prog = decompile::elevator::DecompileDB::default();

    if !input_path.is_file() {
        eprintln!("Error: input path must be a binary file.");
        print_usage_and_exit();
    }

    println!("Disassembling binary: {}", input_path.display());
    decompile::disassembly::load_from_binary(&mut prog, &input_path);
    decompile::disassembly::load_preset(&mut prog);

    let load_elapsed = load_start.elapsed();
    println!("  Loading/disassembly: {}", fmt_elapsed(load_elapsed));

    let pipeline_start = Instant::now();
    println!("Started");
    prog.run_pipeline(&input_path, trace_enabled, measure_rule_times);
    let pipeline_elapsed = pipeline_start.elapsed();
    println!("  Pipeline: {}", fmt_elapsed(pipeline_elapsed));

    if measure_rule_times && !prog.rule_time_reports.is_empty() {
        let dir = PathBuf::from("debug/rule_times");
        std::fs::create_dir_all(&dir).ok();
        for (pass_name, summary) in &prog.rule_time_reports {
            let sanitized = pass_name.replace("::", "_");
            let path = dir.join(format!("{}.txt", sanitized));
            if let Err(e) = std::fs::write(&path, summary) {
                eprintln!("Failed to write rule times for {}: {}", pass_name, e);
            }
        }
        println!("Rule timing reports written to: debug/rule_times/");
    }

    if dump_ir {
        let canonical = crate::decompile::passes::clight_select::derive_canonical_path(
            out_file_path.to_str().unwrap_or("output.light.c"),
        );
        let base = canonical.trim_end_matches(".light.c");
        println!("Dumping IR stages to {}.{{asm,mach,linear,ltl,rtl,cminor,csharpminor,clight}}", base);
        if let Err(e) = crate::debug::ir_dump::dump_all_ir(&prog, base) {
            eprintln!("Failed to dump IR: {}", e);
        }
    }

    if dump_clight_json {
        let canonical = crate::decompile::passes::clight_select::derive_canonical_path(
            out_file_path.to_str().unwrap_or("output.light.c"),
        );
        let json_path = crate::decompile::passes::clight_select::derive_with_suffix(&canonical, ".clight.json");
        match crate::debug::clight_export::export_clight_json(&prog, &json_path) {
            Ok(()) => println!("Clight IR exported to: {}", json_path),
            Err(e) => eprintln!("Failed to export Clight JSON: {}", e),
        }
    }

    let write_start = Instant::now();
    if let Some(parent_dir) = out_file_path.parent() {
        if !parent_dir.as_os_str().is_empty() {
            std::fs::create_dir_all(parent_dir).ok();
        }
    }
    println!("Writing output files");

    let out_file_str = out_file_path.to_str().unwrap_or("output.light.c");

    if trace_enabled {
        let canonical = crate::decompile::passes::clight_select::derive_canonical_path(out_file_str);
        let lost_out_path = crate::decompile::passes::clight_select::derive_with_suffix(&canonical, ".lost.yaml");
        if let Err(e) = crate::debug::lost_dump::dump_lost(&prog, &lost_out_path) {
            eprintln!("Failed to generate lost statement dump: {}", e);
        } else {
            println!("Lost statement dump written to: {}", lost_out_path);
        }
    }

    if trace_enabled {
        let canonical = crate::decompile::passes::clight_select::derive_canonical_path(out_file_str);
        let debug_out_path = crate::decompile::passes::clight_select::derive_with_suffix(&canonical, ".debug.yaml");
        let dataflow_out_path = crate::decompile::passes::clight_select::derive_with_suffix(&canonical, ".dataflow.yaml");

        if let Err(e) = crate::debug::debug_dump::dump_debug(
            &prog,
            input_path.to_str().expect("Invalid input path"),
            &debug_out_path,
        ) {
            eprintln!("Failed to generate debug info: {}", e);
        } else {
            println!("Debug info written to: {}", debug_out_path);
        }

        if let Err(e) = crate::debug::dataflow_dump::dump_dataflow(
            &prog,
            input_path.to_str().expect("Invalid input path"),
            &dataflow_out_path,
        ) {
            eprintln!("Failed to generate dataflow info: {}", e);
        } else {
            println!("Dataflow info written to: {}", dataflow_out_path);
        }
    }

    let raw_tu = prog
        .cast_raw_translation_unit
        .as_ref()
        .expect("ClightEmitPass must produce cast_raw_translation_unit");
    let optimized_tu = prog
        .cast_optimized_translation_unit
        .as_ref()
        .expect("ClightEmitPass must produce cast_optimized_translation_unit");

    if let Err(err) = write_outputs(
        raw_tu,
        optimized_tu,
        out_file_str,
        explicit_output,
        trace_enabled,
    ) {
        eprintln!("Failed to emit decompilation results: {err}");
    } else {
        println!(
            "Decompilation results written to: {}",
            out_file_path.display()
        );
    }

    let write_elapsed = write_start.elapsed();
    let total_elapsed = total_start.elapsed();

    println!("\n=== Timing Summary ===");
    println!("  Loading/disassembly: {}", fmt_elapsed(load_elapsed));
    println!("  Pipeline:            {}", fmt_elapsed(pipeline_elapsed));
    println!("  Writing output:      {}", fmt_elapsed(write_elapsed));
    println!("  -------------------------");
    println!("  Total:               {}", fmt_elapsed(total_elapsed));
}

fn write_outputs(
    raw_tu: &crate::decompile::passes::c_pass::TranslationUnit,
    optimized_tu: &crate::decompile::passes::c_pass::TranslationUnit,
    output_path: &str,
    explicit_output: bool,
    trace_enabled: bool,
) -> std::io::Result<()> {
    use std::fs::File;
    use std::io::Write;

    let canonical_path = crate::decompile::passes::clight_select::derive_canonical_path(output_path);

    if trace_enabled {
        let light_c_source = crate::decompile::passes::c_pass::print_translation_unit(raw_tu);
        {
            let mut file = File::create(&canonical_path)?;
            file.write_all(light_c_source.as_bytes())?;
            file.flush()?;
        }
        println!("Clight C written to: {}", canonical_path);
    }

    let optimized_c_path = if explicit_output {
        output_path.to_string()
    } else {
        crate::decompile::passes::clight_select::derive_optimized_c_path(&canonical_path)
    };
    let optimized_c_source = crate::decompile::passes::c_pass::print_translation_unit(optimized_tu);
    {
        let mut file = File::create(&optimized_c_path)?;
        file.write_all(optimized_c_source.as_bytes())?;
        file.flush()?;
    }
    println!("Optimized C source written to: {}", optimized_c_path);

    Ok(())
}
