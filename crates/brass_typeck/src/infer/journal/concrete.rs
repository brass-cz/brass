//! Journal payloads whose canonical form is already their recorded form.

use super::*;

/// Only atomic concrete types are shared without solver resolution. Nominals,
/// variables and instance tags keep the ordinary skeleton conversion path.
fn atomic(ty: &Type) -> bool {
    matches!(
        ty,
        Type::Bool | Type::Int(_) | Type::Float(_) | Type::Str | Type::Void | Type::Never
    )
}

/// Whether skeleton construction would leave this observation byte-identical.
/// Tags are excluded because skeletons create their own template identities.
pub(super) fn unchanged(entry: &ElaborationJournalEntry) -> bool {
    match entry {
        ElaborationJournalEntry::Typed { ty, instance, .. } => instance.is_none() && atomic(ty),
        ElaborationJournalEntry::SumView(_, ty)
        | ElaborationJournalEntry::TypeOf(_, ty)
        | ElaborationJournalEntry::TypeTest(_, ty) => atomic(ty),
        ElaborationJournalEntry::NumericCall { instance, .. }
        | ElaborationJournalEntry::FieldsLoop { instance, .. } => instance.is_none(),
        ElaborationJournalEntry::KeyedCall { key, instance, .. } => {
            instance.is_none() && atomic(key)
        }
        ElaborationJournalEntry::InstanceReturn(_, args, ret) => {
            args.iter().all(atomic) && atomic(ret)
        }
        ElaborationJournalEntry::ClosureBinding(var, ty) => atomic(var) && atomic(ty),
        ElaborationJournalEntry::CoReturnLink { left, right } => atomic(left) && atomic(right),
        ElaborationJournalEntry::CoGlobalRead { .. } => true,
        ElaborationJournalEntry::PropKind(..)
        | ElaborationJournalEntry::NullProp(..)
        | ElaborationJournalEntry::SumViewIdentity(..)
        | ElaborationJournalEntry::LiftKind(..)
        | ElaborationJournalEntry::LiftErr(..)
        | ElaborationJournalEntry::TypeName(..)
        | ElaborationJournalEntry::LiteralNominal(..)
        | ElaborationJournalEntry::ViewArg(..) => true,
    }
}
