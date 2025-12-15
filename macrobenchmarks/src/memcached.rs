// Microbenchmarks
//
//
// MIT License
//
// Copyright (c) 2025 Copyright (c) 2025 Paper #409 Authors, ASPLOS'26.
//
// Permission is hereby granted, free of charge, to any person obtaining a copy
// of this software and associated documentation files (the "Software"), to deal
// in the Software without restriction, including without limitation the rights
// to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
// copies of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:
//
// The above copyright notice and this permission notice shall be included in all
// copies or substantial portions of the Software.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
// AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
// LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
// OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
// SOFTWARE.

use std::env;
use std::path::PathBuf;
use std::process::{Child, Command};
use std::fs::File;
use std::io::BufReader;
use serde_json::Value;
// use serde_json::{Result as SResult, Value};

use chrono::prelude::*;


const CONFIG_TEST_TIME: usize = 60; // seconds



#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum RunConfiguration {
    Linux,
    Velosiraptor,
    Verified,
    VerifiedNoReclaim,
}

impl RunConfiguration {
    pub fn mod_name(&self) -> &str {
        match self {
            RunConfiguration::Linux => "mmap_mod_linux.ko",
            RunConfiguration::Velosiraptor => "mmap_mod_velosiraptor.ko",
            RunConfiguration::Verified => "mmap_mod_verified.ko",
            RunConfiguration::VerifiedNoReclaim => "mmap_mod_verified_noreclaim.ko",
        }
    }

    pub fn build_opt_name(&self) -> &str {
        match self {
            RunConfiguration::Linux => "linux",
            RunConfiguration::Velosiraptor => "velosiraptor",
            RunConfiguration::Verified => "verified",
            RunConfiguration::VerifiedNoReclaim => "verified_noreclaim",
        }
    }

    pub fn jemalloc_name(&self) -> &str {
        match self {
            RunConfiguration::Linux => "libjemalloc_linux.so",
            RunConfiguration::Velosiraptor => "libjemalloc_module.so",
            RunConfiguration::Verified => "libjemalloc_module.so",
            RunConfiguration::VerifiedNoReclaim => "libjemalloc_module.so",
        }
    }

    pub fn as_str(&self) -> &str {
        match self {
            RunConfiguration::Linux => "Linux",
            RunConfiguration::Velosiraptor => "Velosiraptor",
            RunConfiguration::Verified => "\\system",
            RunConfiguration::VerifiedNoReclaim => "\\system+NoReclaim",
        }
    }
}

fn compile_module(module_dir: &PathBuf, dir: &PathBuf, cfg: RunConfiguration) -> Result<(), ()> {
    println!(" - Compiling kernel module in {} ({:?})...", module_dir.display(), cfg);

    if cfg == RunConfiguration::Linux {
        return Ok(());
    }

    // clean
    let build = Command::new("make")
        .args(["clean"])
        .current_dir(module_dir.as_path())
        .output()
        .expect("failed to build the benchmark");

    if !build.status.success() {
        println!("Build failed: {}", String::from_utf8_lossy(&build.stdout));
        println!("Build failed: {}", String::from_utf8_lossy(&build.stderr));
        return Err(());
    }

    // build library
    let build = Command::new("make")
        .current_dir(module_dir.as_path())
        .args(["pre"])
        .env("IMPL", cfg.build_opt_name())
        .output()
        .expect("failed to build the benchmark");

    if !build.status.success() {
        println!("Build failed: {}", String::from_utf8_lossy(&build.stdout));
        println!("Build failed: {}", String::from_utf8_lossy(&build.stderr));
        return Err(());
    }

    // build the module
    let build = Command::new("make")
        .current_dir(module_dir.as_path())
        .env("IMPL", cfg.build_opt_name())
        .output()
        .expect("failed to build the benchmark");

    if !build.status.success() {
        println!("Build failed: {}", String::from_utf8_lossy(&build.stdout));
        println!("Build failed: {}", String::from_utf8_lossy(&build.stderr));
        return Err(());
    }

    // copy
    let src = module_dir.join(cfg.mod_name());
    let dst = dir.join(cfg.mod_name());
    match std::fs::copy(src, dst) {
        Ok(_) => {
            Ok(())
        }
        Err(e) => {
            println!("Failed to copy kernel module: {:?}", e);
            Err(())
        }
    }
}

fn compile_jemalloc(jemalloc_dir: &PathBuf, dir: &PathBuf, cfg: RunConfiguration) -> Result<(), ()> {
    println!(" - Compiling jemalloc in {}...", jemalloc_dir.display());

    let extra_flags = if cfg == RunConfiguration::Linux {
        "-DCONFIG_DONT_USE_MMAP_MODULE"
    } else {
        "-DCONFIG_USE_MMAP_MODULE"
    };

    let build = Command::new("./autogen.sh")
        .env("EXTRA_CXXFLAGS", extra_flags)
        .env("EXTRA_CFLAGS", extra_flags)
        .current_dir(jemalloc_dir.as_path())
        .output()
        .expect("failed to build the benchmark");

    if !build.status.success() {
        println!("Build failed: {}", String::from_utf8_lossy(&build.stdout));
        println!("Build failed: {}", String::from_utf8_lossy(&build.stderr));
        return Err(());
    }

    let build = Command::new("./configure")
        .env("EXTRA_CXXFLAGS", extra_flags)
        .env("EXTRA_CFLAGS", extra_flags)
        .current_dir(jemalloc_dir.as_path())
        .output()
        .expect("failed to build the benchmark");

    if !build.status.success() {
        println!("Build failed: {}", String::from_utf8_lossy(&build.stdout));
        println!("Build failed: {}", String::from_utf8_lossy(&build.stderr));
        return Err(());
    }

    // clean
    let build = Command::new("make")
        .args(["clean"])
        .current_dir(jemalloc_dir.as_path())
        .output()
        .expect("failed to build the benchmark");

    if !build.status.success() {
        println!("Build failed: {}", String::from_utf8_lossy(&build.stdout));
        println!("Build failed: {}", String::from_utf8_lossy(&build.stderr));
        return Err(());
    }


    // build the module
    let build = Command::new("make")
        .current_dir(jemalloc_dir.as_path())
        .arg("-j")
        .env("IMPL", cfg.build_opt_name())
        .output()
        .expect("failed to build the benchmark");

    if !build.status.success() {
        println!("Build failed: {}", String::from_utf8_lossy(&build.stdout));
        println!("Build failed: {}", String::from_utf8_lossy(&build.stderr));
        return Err(());
    }

    // copy
    let src = jemalloc_dir.join("lib/libjemalloc.so");
    let dst = dir.join(cfg.jemalloc_name());
    match std::fs::copy(src, dst) {
        Ok(_) => {
            Ok(())
        }
        Err(e) => {
            println!("Failed to copy kernel module: {:?}", e);
            Err(())
        }
    }
}

fn get_memcached(dir: &PathBuf) -> Result<PathBuf, ()> {
    let memcached_dir = dir.join("memcached");
    if !memcached_dir.exists() {
        println!(" - Cloning memcached...");

        Command::new("git")
            .args(["clone", "https://github.com/memcached/memcached.git"])
            .current_dir(dir.as_path())
            .output()
            .expect("failed to build clone memcached");

        Command::new("git")
            .args(["checkout", "62b3447380d3fd547e432d1128d94cd12f2e6852"])
            .current_dir(dir.as_path())
            .output()
            .expect("failed to build clone memcached");

        let status = Command::new("./autogen.sh")
            .current_dir(memcached_dir.as_path())
            .output()
            .expect("failed to auto configure memcached");

        if !status.status.success() {
            println!(
                "autogen.sh failed: {}",
                String::from_utf8_lossy(&status.stderr)
            );
            return Err(());
        }

        let status = Command::new("./configure")
            .current_dir(memcached_dir.as_path())
            .output()
            .expect("failed to auto configure memcached");

        if !status.status.success() {
            println!(
                "configure failed: {}",
                String::from_utf8_lossy(&status.stderr)
            );
            return Err(());
        }
    }

    let status = Command::new("make")
        .arg("-j")
        .current_dir(memcached_dir.as_path())
        .output()
        .expect("failed to auto configure memcached");

    if !status.status.success() {
        println!("make failed: {}", String::from_utf8_lossy(&status.stderr));
        return Err(());
    }

    Ok(memcached_dir.join("memcached"))
}

fn get_memtier(dir: &PathBuf) -> Result<PathBuf, ()> {
    let memtier_dir = dir.join("memtier_benchmark");
    if !memtier_dir.exists() {
        Command::new("git")
            .args([
                "clone",
                "https://github.com/RedisLabs/memtier_benchmark.git",
            ])
            .current_dir(dir.as_path())
            .output()
            .expect("failed to build clone memtier_benchmark");
        let status = Command::new("autoreconf")
            .args(["-ivf"])
            .current_dir(memtier_dir.as_path())
            .output()
            .expect("failed to auto configure memcached");
        if !status.status.success() {
            println!(
                "autoreconf failed: {}",
                String::from_utf8_lossy(&status.stderr)
            );
            return Err(());
        }

        let status = Command::new("./configure")
            .current_dir(memtier_dir.as_path())
            .output()
            .expect("failed to auto configure memcached");
        if !status.status.success() {
            println!(
                "configure failed: {}",
                String::from_utf8_lossy(&status.stderr)
            );
            return Err(());
        }
    }

    let status = Command::new("make")
        .current_dir(memtier_dir.as_path())
        .args(["-j"])
        .output()
        .expect("failed to auto configure memcached");
    if !status.status.success() {
        println!("make failed: {}", String::from_utf8_lossy(&status.stderr));
        return Err(());
    }

    Ok(memtier_dir.join("memtier_benchmark"))
}

fn run_memcached(bin: &PathBuf, dir:&PathBuf, cfg: RunConfiguration) -> std::io::Result<Child> {
    println!("   - running memcached");

    let prog_path = bin.display().to_string();

    let jemalloc_path = dir.join(cfg.jemalloc_name());

    Command::new(prog_path)
        .args(["-c", "4096", "-t", "8", "-m", "4096"])
        .env("LD_PRELOAD", jemalloc_path)
        .spawn()
}


struct BenchData {
    pub set_ops_sec: f64,
    pub set_p50_latency: f64,
    pub set_p99_latency: f64,
    pub get_ops_sec: f64,
    pub get_p50_latency: f64,
    pub get_p99_latency: f64,
}

impl std::fmt::Display for BenchData {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "set_ops_sec: {}, set_p50_latency: {}, set_p99_latency: {}, get_ops_sec: {}, get_p50_latency: {}, get_p99_latency: {}",
            self.set_ops_sec,
            self.set_p50_latency,
            self.set_p99_latency,
            self.get_ops_sec,
            self.get_p50_latency,
            self.get_p99_latency
        )
    }
}


fn run_memtier(bin: &PathBuf) -> Result<BenchData, ()> {

    println!("   - running memtier_benchmark for {} seconds", CONFIG_TEST_TIME);

    let prog_path = bin.display().to_string();

    let output = Command::new(prog_path)
        .args([
            "--hide-histogram",
            "--json-out-file=target/memcached_benchmark_data.json",
            "-p",
            "11211",
            "--protocol=memcache_binary",
            // "-n", "100000", // number of requests
            format!("--test-time={}", CONFIG_TEST_TIME).as_str(), // 20 seconds
            "--ratio=1:10",   // "set:get ratio"
            "-t",
            "8",
        ])
        .output();

    match output {
        Ok(output) => {
            if !output.status.success() {
                println!(
                    "memtier_benchmark failed: {}",
                    String::from_utf8_lossy(&output.stderr)
                );
                return Err(());
            }

            // Open the file in read-only mode with buffer.
            let file = File::open("target/memcached_benchmark_data.json").expect("could not open file");
            let reader = BufReader::new(file);


            let u : Value = serde_json::from_reader(reader).expect("could not parse JSON");

            let runtime = u["ALL STATS"]["Runtime"]["Total duration"].as_u64().unwrap();
            if runtime < CONFIG_TEST_TIME as u64{
                println!("memtier_benchmark failed: test time is less than expected");
                return Err(());
            }

            Ok(BenchData {
                set_ops_sec:     u["ALL STATS"]["Sets"]["Ops/sec"].as_f64().unwrap(),
                set_p50_latency: u["ALL STATS"]["Sets"]["Percentile Latencies"]["p50.00"].as_f64().unwrap(),
                set_p99_latency: u["ALL STATS"]["Sets"]["Percentile Latencies"]["p99.00"].as_f64().unwrap(),
                get_ops_sec:     u["ALL STATS"]["Gets"]["Ops/sec"].as_f64().unwrap(),
                get_p50_latency: u["ALL STATS"]["Gets"]["Percentile Latencies"]["p50.00"].as_f64().unwrap(),
                get_p99_latency: u["ALL STATS"]["Gets"]["Percentile Latencies"]["p99.00"].as_f64().unwrap(),
            })
            }
            Err(e) => {
                println!("memtier_benchmark failed: {}", e);
                Err(())
            }
        }
}

fn main() {
    println!("# Running Benchmark: Memcached");

    let args: Vec<String> = env::args().collect();

    let output = Command::new("git")
        .args(["status", "--porcelain"])
        .output()
        .expect("failed to execute process");

    let is_dirty = !output.stdout.is_empty();
    let build_dirty = env!("VERGEN_GIT_DIRTY") == "true";
    let allow_dirty = args.iter().any(|e| e.as_str() == "--allow-dirty");

    if is_dirty && !allow_dirty {
        println!("ERROR. Git repository is dirty. Terminating.");
        println!("(pass --allow-dirty to ignore)");
        std::process::exit(-1);
    }

    if build_dirty && !allow_dirty {
        println!("ERROR. Executable has been built from a dirty git repository. Terminating.");
        println!("(pass --allow-dirty to ignore)");
        std::process::exit(-1);
    }

    let dir = PathBuf::from("target/memcached");
    if !dir.exists() {
        std::fs::create_dir_all(&dir).expect("failed to create directory");
    }

    let memcached_path = get_memcached(&dir).expect("failed to get memcached");
    let memtier_path = get_memtier(&dir).expect("failed to get memtier");
    let module_dir = PathBuf::from("../linux/module");
    let dir = PathBuf::from("target/memcached");

    // compile the kernel module for all options
    for opt in &[
        RunConfiguration::Linux,
        RunConfiguration::Velosiraptor,
        RunConfiguration::Verified,
        RunConfiguration::VerifiedNoReclaim,
    ] {
        if compile_module(&module_dir, &dir, *opt).is_err() {
            println!("# Benchmark failed");
            return;
        }
    }

    // compile jemalloc for default linux and verified
    let jemalloc_dir = PathBuf::from("../linux/jemalloc");
    if compile_jemalloc(&jemalloc_dir, &dir, RunConfiguration::Linux).is_err() {
        println!("# Benchmark failed");
        return;
    }

    if compile_jemalloc(&jemalloc_dir, &dir, RunConfiguration::Verified).is_err() {
        println!("# Benchmark failed");
        return;
    }

    let mut results = Vec::new();

    for opt in &[
        RunConfiguration::Linux,
        RunConfiguration::Velosiraptor,
        RunConfiguration::Verified,
        RunConfiguration::VerifiedNoReclaim,
    ] {
        let modpath = dir.join(opt.mod_name()).display().to_string();

        println!(" - Running benchmark with {:?}...", opt);
        if *opt != RunConfiguration::Linux {
            println!("   - installing kernel module.");
            let insmod = Command::new("sudo")
                .args(["insmod", modpath.as_str()])
                .output()
                .expect("failed to run install the kernel module");
            if !insmod.status.success() {
                println!("failed to insert the kernel module:");
                println!("    {}", String::from_utf8_lossy(&insmod.stdout));
                println!("    {}", String::from_utf8_lossy(&insmod.stderr));
                continue;
            }
        }

        let mut memcached = run_memcached(&memcached_path, &dir,*opt).expect("failed to run memcached");

        println!("   - waiting 5s for memcached to start...");
        std::thread::sleep(std::time::Duration::from_secs(5));

        match memcached.try_wait() {
            Ok(Some(status)) => println!("Memcached with status {}", status),
            Ok(None) => (),
            Err(e) => println!("Error waiting: {}", e),
        }

        let res = run_memtier(&memtier_path).expect("failed to run memtier");

        results.push((
            *opt, res
        ));

        memcached.kill().expect("failed to kill memcached");

        if *opt != RunConfiguration::Linux {
            println!("   - removing kernel module.");
        // remove the kernel module
        let rmmod = Command::new("sudo")
            .args(["rmmod", modpath.as_str()])
            .output()
            .expect("failed to run install the kernel module");
        if !rmmod.status.success() {
            println!("failed to insert the kernel module:");
            println!("    {}", String::from_utf8_lossy(&rmmod.stdout));
            println!("    {}", String::from_utf8_lossy(&rmmod.stderr));
        }
        }
    }

    let dirty = if is_dirty || build_dirty {
        "-dirty"
    } else {
        ""
    };

    println!("# Completed\n\n");

    println!(
        "% =================================================================================================="
    );
    println!("% Table: Memcached Performance");
    println!(
        "% =================================================================================================="
    );
    println!("% Git Hash:   {}{dirty}", env!("VERGEN_GIT_DESCRIBE"));
    println!("% CPU:        {}", env!("VERGEN_SYSINFO_CPU_BRAND"));
    println!("% OS:         {}", env!("VERGEN_SYSINFO_OS_VERSION"));
    println!("% Date:       {}", Local::now());
    println!(
        "% =================================================================================================="
    );
    println!("%");
    println!("\\begin{{tabular}}{{lrrrrrr}}");
    println!("  \\hline % ---------------------------------------------------------------------------");
    println!("  \\th{{{:<14}}} & \\span{{\\th{{{:^18}}}}} & \\span{{\\th{{{:^18}}}}} \\\\", "Operation", "Get", "Set");
    println!("  \\th{{{:<14}}} & \\th{{{}}} & \\th{{{}}} & \\th{{{}}} & \\th{{{}}} & \\th{{{}}} & \\th{{{}}} \\\\",
                "Code", "Tpt", "P50", "P99", "Tpt", "P50", "P99",);
    println!("  \\hline % ---------------------------------------------------------------------------");
    for (cfg, result) in results.iter() {
        println!("  {:<19} &   {:.0}K/s &   {:.2}ms &   {:.2}ms &    {:.0}K/s &   {:.2}ms &   {:.2}ms \\\\",
            cfg.as_str(), result.get_ops_sec / 1000.0, result.get_p50_latency, result.get_p99_latency, result.set_ops_sec / 1000.0, result.set_p50_latency, result.set_p99_latency);
    }
    println!("  \\hline % ---------------------------------------------------------------------------");
    println!("\\end{{tabular}}");
    println!("%");
    println!(
        "% =================================================================================================="
    );
}
