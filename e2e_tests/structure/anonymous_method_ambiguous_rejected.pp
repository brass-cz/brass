// Two in-scope types declare `display` and the anonymous structure satisfies
// both: the call is ambiguous, reported at the VALUE, and asks for an
// annotation.
type Person = { name: string }
fun Person.display(self) { println("person {self.name}") }

type Robot = { name: string }
fun Robot.display(self) { println("robot {self.name}") }

fun main() {
    let x = { name: "Zoe" }
    x.display()
}
