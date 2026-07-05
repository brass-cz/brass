// Library whose `norm` is imported under a rename by rename_not_hijacked.pp.
// Importing from hijacklib keeps that module loaded in the same program.
import hijacklib.{ helper }

fun norm() -> int32 { return helper() + 2 }
