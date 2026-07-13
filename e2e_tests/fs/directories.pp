// Recursive directory creation and removal, through both argument forms: the
// same call takes a string or a `Path` (the member-presence test in `_as_text`
// decides which arm is compiled, per call site).
import fs.{ create_dir, remove_dir, write_file, read_file }
import path.{ Path }

fun main() {
    const root = "/tmp/prepoly_e2e_directories"
    // A leftover tree from an earlier run would make the case lie, so start clean.
    if Path.parse(root).is_dir() {
        remove_dir(root)!
    }

    // `mkdir -p`: every missing parent is created, from a string.
    create_dir("{root}/a/b/c")!
    println(Path.parse("{root}/a/b/c").is_dir())
    println(Path.parse("{root}/a").is_dir())

    // Creating an existing directory is not an error -- the state it asks for
    // already holds.
    create_dir("{root}/a/b/c")!
    println("recreated")

    // The same function takes a `Path`.
    const nested = Path.parse(root).join(["x", "y"])
    create_dir(nested)!
    println(nested.is_dir())

    // A file in the tree, to prove removal is recursive over contents.
    write_file("{root}/a/b/c/f.txt", "hi")!
    println(read_file("{root}/a/b/c/f.txt")!)

    // Removal takes a `Path` too, and takes the whole tree with it.
    remove_dir(Path.parse(root))!
    println(Path.parse(root).exists())

    // A directory that is not there is an error, not a silent success: a typo
    // in a destructive call must not read as "done".
    match remove_dir("{root}/never_existed") {
        Ok { value } => println("BUG: removing a missing directory succeeded"),
        Err { error } => println("missing directory rejected"),
    }

    // A path that exists as a FILE is not a directory to create.
    const file = "/tmp/prepoly_e2e_directories_file"
    write_file(file, "x")!
    match create_dir(file) {
        Ok { value } => println("BUG: created a directory over a file"),
        Err { error } => println("file in the way rejected"),
    }
}
