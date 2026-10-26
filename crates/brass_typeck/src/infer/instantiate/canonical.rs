//! Canonical memo identities and differential result comparison.

use crate::infer::Checker;
use crate::infer::journal::{CanonVar, ElaborationMemoContext, ElaborationMemoKey, MemoFlavor};
use crate::solver::InferenceVarKind;
use brass_hir::{NominalType, Substitution, Type};
use fxhash::FxHashMap as HashMap;

impl Checker<'_> {
    /// Build a key whose open variables depend on first-occurrence structure,
    /// not on the checker's allocation order. Receiver, arguments, and scheme
    /// inputs share one slot namespace so aliases across them remain visible.
    pub(in crate::infer) fn elaboration_memo_key(
        &self,
        kind: &str,
        callable: &str,
        receiver: Option<&Type>,
        arg_types: &[Type],
        scheme_inputs: &[Option<Type>],
    ) -> Option<ElaborationMemoContext> {
        let resolved_receiver = receiver.map(|ty| self.resolve(ty));
        let resolved_args: Vec<_> = arg_types.iter().map(|ty| self.resolve(ty)).collect();
        let resolved_scheme_inputs: Vec<_> = scheme_inputs
            .iter()
            .map(|ty| ty.as_ref().map(|ty| self.resolve(ty)))
            .collect();
        if resolved_receiver
            .iter()
            .chain(resolved_args.iter())
            .chain(resolved_scheme_inputs.iter().flatten())
            .all(brass_hir::is_fully_known)
        {
            return Some(ElaborationMemoContext {
                key: ElaborationMemoKey {
                    flavor: MemoFlavor::Ordinary,
                    callable: format!("{kind}:{callable}"),
                    receiver: resolved_receiver,
                    args: resolved_args,
                    scheme_inputs: resolved_scheme_inputs,
                    canon_vars: Vec::new(),
                },
                inputs: Vec::new(),
            });
        }
        let mut slots = HashMap::default();
        let mut inputs = Vec::new();
        let receiver = match resolved_receiver {
            Some(ty) => Some(self.canonicalize_resolved_memo_type(ty, &mut slots, &mut inputs)?),
            None => None,
        };
        let args = resolved_args
            .into_iter()
            .map(|ty| self.canonicalize_resolved_memo_type(ty, &mut slots, &mut inputs))
            .collect::<Option<Vec<_>>>()?;
        let scheme_inputs = resolved_scheme_inputs
            .into_iter()
            .map(|ty| match ty {
                Some(ty) => self
                    .canonicalize_resolved_memo_type(ty, &mut slots, &mut inputs)
                    .map(Some),
                None => Some(None),
            })
            .collect::<Option<Vec<_>>>()?;
        let canon_vars = inputs.iter().map(|(var, _)| *var).collect();
        Some(ElaborationMemoContext {
            key: ElaborationMemoKey {
                flavor: MemoFlavor::Ordinary,
                callable: format!("{kind}:{callable}"),
                receiver,
                args,
                scheme_inputs,
                canon_vars,
            },
            inputs,
        })
    }

    fn canonicalize_resolved_memo_type(
        &self,
        ty: Type,
        slots: &mut HashMap<u32, CanonVar>,
        inputs: &mut Vec<(CanonVar, Type)>,
    ) -> Option<Type> {
        match ty {
            Type::Unknown(id) => {
                if id == brass_hir::INFER_VAR {
                    return None;
                }
                let kind = self.solver.kind_of(id).unwrap_or(InferenceVarKind::Source);
                if matches!(
                    kind,
                    InferenceVarKind::ErrorOnlyOk | InferenceVarKind::UninhabitedOk
                ) {
                    return None;
                }
                let var = *slots.entry(id).or_insert_with(|| {
                    let var = CanonVar {
                        slot: inputs.len() as u32,
                        kind,
                    };
                    inputs.push((var, Type::Unknown(id)));
                    var
                });
                Some(Type::Unknown(var.slot))
            }
            Type::Array(inner, len) => Some(Type::Array(
                Box::new(self.canonicalize_resolved_memo_type(*inner, slots, inputs)?),
                len,
            )),
            Type::Slice(inner) => Some(Type::Slice(Box::new(
                self.canonicalize_resolved_memo_type(*inner, slots, inputs)?,
            ))),
            Type::Tuple(elements) => Some(Type::Tuple(
                elements
                    .into_iter()
                    .map(|ty| self.canonicalize_resolved_memo_type(ty, slots, inputs))
                    .collect::<Option<Vec<_>>>()?,
            )),
            Type::Fun(params, ret) => Some(Type::Fun(
                params
                    .into_iter()
                    .map(|ty| self.canonicalize_resolved_memo_type(ty, slots, inputs))
                    .collect::<Option<Vec<_>>>()?,
                Box::new(self.canonicalize_resolved_memo_type(*ret, slots, inputs)?),
            )),
            Type::Nullable(inner) => Some(Type::Nullable(Box::new(
                self.canonicalize_resolved_memo_type(*inner, slots, inputs)?,
            ))),
            Type::ConstOf(inner) => Some(Type::ConstOf(Box::new(
                self.canonicalize_resolved_memo_type(*inner, slots, inputs)?,
            ))),
            Type::Mut(inner) => Some(Type::Mut(Box::new(
                self.canonicalize_resolved_memo_type(*inner, slots, inputs)?,
            ))),
            Type::Ref(inner) => Some(Type::Ref(Box::new(
                self.canonicalize_resolved_memo_type(*inner, slots, inputs)?,
            ))),
            Type::Record(nominal) => self
                .canonicalize_resolved_memo_nominal(nominal, slots, inputs)
                .map(Type::Record),
            Type::Sum(nominal) => self
                .canonicalize_resolved_memo_nominal(nominal, slots, inputs)
                .map(Type::Sum),
            resolved => Some(resolved),
        }
    }

    fn canonicalize_resolved_memo_nominal(
        &self,
        nominal: NominalType,
        slots: &mut HashMap<u32, CanonVar>,
        inputs: &mut Vec<(CanonVar, Type)>,
    ) -> Option<NominalType> {
        let mut substitution = Substitution::empty();
        for (name, ty) in nominal.substitution.iter() {
            substitution.insert(
                name,
                self.canonicalize_resolved_memo_type(ty.clone(), slots, inputs)?,
            );
        }
        Some(NominalType::with_substitution(
            nominal.id,
            nominal.name,
            substitution,
        ))
    }

    /// Canonical result structure and variable kinds for differential checks.
    pub(in crate::infer) fn canonical_memo_check_return(
        &self,
        ty: &Type,
    ) -> (Type, Vec<InferenceVarKind>) {
        let resolved = self.resolve(ty);
        let mut slots = HashMap::default();
        let mut inputs = Vec::new();
        if let Some(canonical) =
            self.canonicalize_resolved_memo_type(resolved.clone(), &mut slots, &mut inputs)
        {
            return (
                canonical,
                inputs.into_iter().map(|(var, _)| var.kind).collect(),
            );
        }

        // Error-classified variables are deliberately rejected from memo keys,
        // but can be fresh outputs of an otherwise clean elaboration. Normalize
        // them here so validation compares their structure rather than allocation
        // ids while still comparing their solver kinds.
        let vars: Vec<_> = brass_hir::type_vars(&resolved)
            .into_iter()
            .filter(|id| *id != brass_hir::INFER_VAR)
            .collect();
        let substitution = vars
            .iter()
            .enumerate()
            .map(|(slot, id)| (*id, Type::Unknown(slot as u32)))
            .collect();
        let kinds = vars
            .into_iter()
            .map(|id| self.solver.kind_of(id).unwrap_or(InferenceVarKind::Source))
            .collect();
        (brass_hir::substitute_vars(&resolved, &substitution), kinds)
    }
}
