//! Command-line access to the JIT store's configuration and owned files.

use std::process::ExitCode;

/// Management operations on the entire shared JIT object cache.
#[derive(clap::Subcommand)]
pub(crate) enum CacheAction {
    /// Show the directory, configuration, size, and stale temporary file count.
    Info,
    /// Remove all cached objects and temporary files older than 24 hours.
    Clean,
}

/// Executes a cache command without compiling a program. I/O failures print a
/// diagnostic and return status 1; builds without the JIT return status 0.
pub(crate) fn run(action: CacheAction, no_jit_cache: bool) -> ExitCode {
    #[cfg(jit_backend)]
    {
        match run_jit(action, no_jit_cache) {
            Ok(()) => ExitCode::SUCCESS,
            Err(error) => {
                eprintln!("JIT cache: {error}");
                ExitCode::FAILURE
            }
        }
    }
    #[cfg(not(jit_backend))]
    {
        let _ = (action, no_jit_cache);
        println!("This build has no JIT cache.");
        ExitCode::SUCCESS
    }
}

#[cfg(jit_backend)]
fn run_jit(action: CacheAction, no_jit_cache: bool) -> std::io::Result<()> {
    use brass_jit_llvm::{clean_jit_cache, jit_cache_location, jit_cache_usage};

    let Some(location) = jit_cache_location() else {
        println!("JIT cache: disabled (neither XDG_CACHE_HOME nor HOME is set)");
        return Ok(());
    };
    match action {
        CacheAction::Info => {
            let usage = jit_cache_usage(&location)?;
            println!("Directory: {}", location.directory.display());
            let status = if no_jit_cache {
                "disabled (--no-jit-cache)"
            } else if location.enabled {
                "enabled (configuration permits caching)"
            } else {
                "disabled (BRASS_JIT_CACHE=off or 0)"
            };
            println!("Status: {status}");
            println!("Entries: {}", usage.entries);
            println!("Size: {}", human_size(usage.bytes));
            println!("Limit: {}", human_size(location.max_bytes));
            println!("Stale temp files: {}", usage.temp_files);
        }
        CacheAction::Clean => {
            let usage = clean_jit_cache(&location)?;
            println!("Directory: {}", location.directory.display());
            println!("Removed entries: {}", usage.entries);
            println!("Removed size: {}", human_size(usage.bytes));
            println!("Removed stale temp files: {}", usage.temp_files);
        }
    }
    Ok(())
}

#[cfg(jit_backend)]
fn human_size(bytes: u64) -> String {
    let mut size = bytes as f64;
    let mut unit = "B";
    for candidate in ["KiB", "MiB", "GiB", "TiB", "PiB", "EiB"] {
        if size < 1024.0 {
            break;
        }
        size /= 1024.0;
        unit = candidate;
    }
    format!("{size:.2} {unit} ({bytes} bytes)")
}
