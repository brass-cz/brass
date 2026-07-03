// The anonymous structure lacks a field the only `display`-declaring type
// requires: the error names the missing constraint AT THE VALUE, not inside
// the method body.
type Person = { name: string, age: int32 }
fun Person.display(self) { println(self.name) }

fun main() {
    let x = { name: "Zoe" }
    x.display()
}
