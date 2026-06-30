// Method return types are inferred even without annotations, so callers get a
// precise static type. Mismatched uses are rejected before
// execution; the matching uses below run.

type Account = {
    owner: string
    balance: int32

    open(owner: string) {
        return Self { owner: owner, balance: 0 }
    }

    deposit(self, amount: int32) {
        self.balance += amount
        return self.balance
    }

    label(self) {
        return "{self.owner}: {self.balance}"
    }
}

fun main() {
    // `open` is a static method whose inferred return type is Account.
    let acc = Account.open("Alice")

    // `deposit` is inferred to return int32.
    let total: int32 = acc.deposit(120)
    println("total = {total}")

    // `label` is inferred to return string.
    let line: string = acc.label()
    println(line)
}
