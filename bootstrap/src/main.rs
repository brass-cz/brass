pub mod http;
mod llvm;

use std::env;
use std::os::unix::process::CommandExt;
use std::process;

#[tokio::main]
async fn main() -> std::io::Result<()> {
    let llvm_path = env::current_dir()?.join("llvm");
    if !llvm_path.is_dir() {
        llvm::download_llvm(&llvm_path).await.unwrap();
    }

    let args: Vec<_> = env::args().skip(1).collect();
    let mut cmd = process::Command::new(&args[0]);
    cmd.args(&args[1..]).env(llvm::LLVM_SYS_ENV, &llvm_path);
    llvm::configure_linker(&mut cmd, &llvm_path);
    Err(cmd.exec())
}
