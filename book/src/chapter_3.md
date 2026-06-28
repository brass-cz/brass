# Chapter 3: Modules

prepoly organizes code into modules: every file is a module, and directories form the module path.
Let's split a program across several files.

First, write `students/types.pp`:

```prepoly
type _Person = {
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

type Student: _Person = {
    first_name,
    last_name,
    display(self) {
        return "{self.id}: {self.first_name} {self.last_name}"
    },
    id,
    program: DegreeProgram,
}
```

Then, write `students.pp`:

```prepoly
import students.types.{ DegreeProgram, Student }

fun get_students() {
    return [
        Student {
            first_name: "Isac",
            last_name: "Newton",
            id: 1001,
            program: DegreeProgram.Master { year: 1 },
        },
        Student {
            first_name: "Thomas",
            last_name: "Edison",
            id: 1002,
            program: DegreeProgram.Doctor { year: 3 },
        },
    ]
}
```

Now we can use these modules in `show_students.pp`:

```prepoly
import students.{ get_students }

println(get_students())
```

Then, execute it:

```bash
prepoly show_students.pp
```

This prints the list of students.

Note that anything you define with a name starting with `_` becomes private to its module.
So you can't use `_Person` outside `students/types.pp`.
