// Microbenchmarks
//
//
// MIT License
//
// Copyright (c) 2025 Paper #409 Authors, ASPLOS'26.
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

use std::collections::HashMap;
use std::env;
use std::path::PathBuf;
use std::process::Command;

use chrono::prelude::*;

mod bench;
use bench::*;

const ROWS: [&str; 4] = [
    "Linux-x86_64",
    "Velosiraptor-x86_64",
    // "Barrelfish-PTable",
    // "Velosiraptor-PTable",
    "Verified-x86_64",
    "Verified+NoReclaim-x86_64",
];

const COLS: [&str; 3] = ["Map", "Protect", "Unmap"];

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
}

impl std::fmt::Display for RunConfiguration {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            RunConfiguration::Linux => write!(f, "linux"),
            RunConfiguration::Velosiraptor => write!(f, "velosiraptor"),
            RunConfiguration::Verified => write!(f, "verified"),
            RunConfiguration::VerifiedNoReclaim => write!(f, "verified_noreclaim"),
        }
    }
}

fn compile(dir: &PathBuf) -> Result<(), ()> {
    println!(" - Compiling benchmark binary...");

    let _build = Command::new("make")
        .args(["clean"])
        .current_dir(dir.as_path())
        .output()
        .expect("failed to build the benchmark");

    let build = Command::new("make")
        .current_dir(dir.as_path())
        .output()
        .expect("failed to build the benchmark");

    if !build.status.success() {
        println!("Build failed: {}", String::from_utf8_lossy(&build.stdout));
        println!("Build failed: {}", String::from_utf8_lossy(&build.stderr));
        return Err(());
    }

    Ok(())
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

fn run(dir: &PathBuf, cfg: RunConfiguration) -> Result<String, ()> {
    println!(" - Running {cfg} benchmark...");

    let modpath = dir.join(cfg.mod_name()).display().to_string();

    // install the module
    if cfg != RunConfiguration::Linux {
        // install the kernel module
        println!("  - installing the kernel module: {}", modpath.as_str());
        let insmod = Command::new("sudo")
            .args(["insmod", modpath.as_str()])
            .output()
            .expect("failed to run install the kernel module");
        if !insmod.status.success() {
            println!("failed to insert the kernel module:");
            println!("    {}", String::from_utf8_lossy(&insmod.stdout));
            println!("    {}", String::from_utf8_lossy(&insmod.stderr));
            return Err(());
        }
    }

    // run the benchmark
    let run = Command::new("./bench")
        .current_dir(dir.as_path())
        .arg(std::format!("{cfg}"))
        .output()
        .expect("failed to run the benchmark");

    if cfg != RunConfiguration::Linux {
        println!("  - removing the kernel module: {}", modpath.as_str());
        // remove the kernel module
        let rmmod = Command::new("sudo")
            .args(["rmmod", modpath.as_str()])
            .output()
            .expect("failed to run install the kernel module");
        if !rmmod.status.success() {
            println!("failed to insert the kernel module:");
            println!("    {}", String::from_utf8_lossy(&rmmod.stdout));
            println!("    {}", String::from_utf8_lossy(&rmmod.stderr));
            return Err(());
        }
    }

    // check status of the benchmark
    if !run.status.success() {
        println!(
            "    ## Run failed: {}",
            String::from_utf8_lossy(&run.stdout)
        );
        println!(
            "    ## Run failed: {}",
            String::from_utf8_lossy(&run.stderr)
        );
        return Err(());
    }
    Ok(String::from_utf8_lossy(&run.stdout).to_string())
}

struct Measurements {
    measurements: HashMap<String, Stats>,
}

impl Measurements {
    pub fn to_latex(&self) -> String {
        let mut res = String::new();

        res.push_str("  \\hline % --------------------------------------------------------------------------------------------\n");
        res.push_str(&format!("  \\th{{{:<15}}}", "Operation"));
        for col in &COLS {
            res.push_str(&format!(" & \\span{{\\th{{{:^7}}}}}", col));
        }
        res.push_str(" \\\\\n");
        res.push_str(&format!("  \\th{{{:<15}}}", "Code"));
        res.push_str(&format!(
            " & \\th{{{}}} & \\th{{{}}} & \\th{{{}}} & \\th{{{}}} & \\th{{{}}} & \\th{{{}}} \\\\\n",
            "P50", "P99", "P50", "P99", "P50", "P99"
        ));
        let mut prev = "";
        for row in &ROWS {
            let mut parts = row.split('-');
            let env = parts.next().unwrap();
            let cfg = parts.next().unwrap();
            if prev != cfg {
                res.push_str("  \\hline % --------------------------------------------------------------------------------------------\n");
                prev = cfg;
            }
            res.push_str(&format!("  {:<20}", env.replace("Verified", "\\system")));
            for col in &COLS {
                let key = format!("{}-{}", row, col);
                if let Some(v) = self.measurements.get(&key) {
                    res.push_str(&format!(" & {:6}ns & {:6}ns", v.med, v.p99));
                } else {
                    res.push_str(&format!(" & {:6}ns & {:6}ns", "??", "??"));
                }
            }
            res.push_str(" \\\\\n");
        }
        res.push_str("  \\hline % --------------------------------------------------------------------------------------------");

        return res;
    }
}

impl std::fmt::Display for Measurements {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for c in self.measurements.keys() {
            if let Some(v) = self.measurements.get(c) {
                write!(
                    f,
                    "{:<30}  {:6}ns {:6}ns {:6}ns ({})\n",
                    c, v.avg, v.med, v.p99, v.num
                )?;
            } else {
                write!(
                    f,
                    "{:<30}  {:6}ns {:6}ns {:6}ns ({})\n",
                    c, "??", "??", "??", "??"
                )?;
            }
        }
        Ok(())
    }
}

fn parse_results(output: &str) -> Measurements {
    let mut measurements = HashMap::new();

    for line in output.lines() {
        // println!("LINE: {line}");
        let mut parts = line.split(':');

        let label = parts.next().unwrap();
        let values = parts.next().unwrap();

        let latencies: Vec<i64> = values
            .trim()
            .split(' ')
            .map(|x| x.parse::<i64>().unwrap())
            .collect();
        // println!("{latencies:?}");
        measurements.insert(label.to_string(), Stats::from(latencies.as_slice()));
    }

    Measurements { measurements }
}

fn main() {
    println!("# Running Benchmark: System Call Measurements");

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

    let dir = PathBuf::from("src/systemcall");
    if compile(&dir).is_err() {
        println!("# Benchmark failed");
        return;
    }

    let module_dir = PathBuf::from("../linux/module");

    let mut output = String::new();
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

        let output2 = match run(&dir, *opt) {
            Ok(output) => output,
            Err(_) => {
                println!("# Benchmark failed");
                return;
            }
        };
        output.extend(output2.chars());
    }

    let dirty = if is_dirty || build_dirty {
        "-dirty"
    } else {
        ""
    };

    let res = parse_results(&output);

    println!("# Completed\n\n");

    println!(
        "% ====================================================================================================="
    );
    println!("% Table: System Call Performance");
    println!(
        "% ====================================================================================================="
    );
    println!("% Git Hash:   {}{dirty}", env!("VERGEN_GIT_DESCRIBE"));
    println!("% CPU:        {}", env!("VERGEN_SYSINFO_CPU_BRAND"));
    println!("% OS:         {}", env!("VERGEN_SYSINFO_OS_VERSION"));
    println!("% Date:       {}", Local::now());
    println!(
        "% ====================================================================================================="
    );
    println!("%");
    println!("\\begin{{tabular}}{{ccrrrrrr}}");

    let latex_results = res.to_latex();
    println!("{latex_results}");
    println!("\\end{{tabular}}");
    println!("%");
    println!(
        "% ====================================================================================================="
    );
}
