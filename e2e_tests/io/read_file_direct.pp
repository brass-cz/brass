fun main() {
    const path = "/tmp/prepoly_e2e_read_file_direct.txt"
    write_file(path, "hello from file\n")!
    const content = read_file(path)!
    print(content)
}
