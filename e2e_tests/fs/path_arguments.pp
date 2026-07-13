// Every path-taking function in `fs` accepts a `Path` as readily as a string --
// `File.open`, `read_file`, `write_file`, and the directory pair -- and the two
// forms name the same file, so one can write what the other reads.
import fs.{ File, read_file, write_file, create_dir, remove_dir }
import path.{ Path }

fun main() {
    const root = Path.parse("/tmp/prepoly_e2e_fs_path_arguments")
    if root.is_dir() {
        remove_dir(root)!
    }
    create_dir(root)!

    // A `Path` throughout.
    const file = root.join("a.txt")
    write_file(file, "written through a Path")!
    println(read_file(file)!)
    let f = File.open(file, "r")!
    println(f.size()!)
    println(to_text(f.read(7)!)!)
    f.close()!

    // A string throughout, including an append.
    const other = "{root.to_string()}/b.txt"
    write_file(other, "written through a string")!
    let g = File.open(other, "a")!
    g.write(to_bytes("!"))!
    g.close()!
    println(read_file(other)!)

    // The two forms name the same file: written as a `Path`, read as a string.
    println(read_file(file.to_string())!)

    remove_dir(root)!
    println(root.exists())
}
