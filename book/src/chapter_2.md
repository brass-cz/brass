# Chapter 2: Defining types

We can define new types with their fields and methods as follows:

```prepoly
type Person = {
    first_name: string,
    last_name: string,
    display(self) {
        return "{self.first_name} {self.last_name}"
    },
}

fun main() {
    const newton = Person {
        first_name: "Isac",
        last_name: "Newton",
    }
    println("{newton.display()}")
}
```

This program outputs `Isac Newton`.

We can define "OR" types:

```prepoly
type DegreeProgram =
    | Bachelor {
        year: int32,
    }
    | Master {
        year: int32,
    }
    | Doctor {
        year: int32,
    }
```

Using `DegreeProgram` type, we can define `Student` type:

```prepoly
type Student: Person = {
    first_name,
    last_name,
    display(self) {
        return "{self.id}: {self.first_name} {self.last_name}"
    },
    id,
    program: DegreeProgram,
}
```

Here, we wrote the `Person` type on the left of `Student`.
This requires that the `Student` type include all fields of the `Person` type.

Using these definitions, let's write a complete program.
Here we enhance `display` with a `match` expression that formats each `DegreeProgram` variant:

```prepoly
type Person = {
    first_name: string,
    last_name: string,
    display(self) {
        return "{self.first_name} {self.last_name}"
    },
}
type DegreeProgram =
    | Bachelor {
        year: int32,
    }
    | Master {
        year: int32,
    }
    | Doctor {
        year: int32,
    }
type Student: Person = {
    first_name,
    last_name,
    display(self) {
        const program = match self.program {
            Bachelor { year } => "Bachelor {year}",
            Master { year } => "Master {year}",
            Doctor { year } => "Doctor {year}",
        }
        return "{self.id} ({program}): {self.first_name} {self.last_name}"
    },
    id,
    program: DegreeProgram,
}

fun main() {
    const newton = Student {
        first_name: "Isac",
        last_name: "Newton",
        id: 1001,
        program: DegreeProgram.Master { year: 1 },
    }
    println("{newton.display()}")
    println("{newton}")
}
```

Executing this shows the following output:

```
1001 (Master 1): Isac Newton
Student {
    first_name: Isac,
    last_name: Newton,
    id: 1001,
    program: DegreeProgram.Master {
        year: 1,
    },
}
```

In the above example, we didn't write any type annotation for `Student.id`.
So we can write a string as the value of `Student.id`:

```prepoly
const edison = Student {
    first_name: "Thomas",
    last_name: "Edison",
    id: "AL17001",
    program: DegreeProgram.Doctor { year: 3 },
}
println("{edison.display()}")
```

This program can be placed alongside the above `newton` example, and the output is as follows:

```
AL17001 (Doctor 3): Thomas Edison
```

We can use `Person` type if we would like to define a function which receives `Person` and its derivative:

```prepoly
fun print_name(person: Person) {
    println(person.display())
}
print_name(edison)
```
