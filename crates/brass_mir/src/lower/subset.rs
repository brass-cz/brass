//! On-demand MIR bodies and their checker input refresh windows.

use super::*;

/// A partially lowered MIR program for the lazy pipeline. Methods and module
/// initializers are lowered up front -- the checker settles every method body
/// before its first body event, and execution runs every init -- while free
/// functions are lowered one at a time as their checks stream in
/// ([`SubsetLowering::add_function`]). Closure ids are allocated from one
/// counter carried across calls, so a late body's closures never collide
/// with an early one's.
///
/// Constant-array promotion is NOT run: it is a whole-program
/// interprocedural fixpoint (see the `promote` module) and cannot run on a
/// partial call graph, so the literals are constructed at their use sites,
/// exactly as un-promoted code always is.
pub struct SubsetLowering {
    changed_inputs: crate::ChangedInputs,
    reset_inputs: bool,
    /// Currently lowered bodies and the adopted per-instance channel maps.
    pub mir: MirProgram,
    lowered: fxhash::FxHashSet<String>,
    next_closure: u32,
}

impl SubsetLowering {
    /// Lower every method body and module initializer of `program` (with the
    /// channel state current at call time); no free function is lowered yet.
    /// `tables` are the shared HIR-derived tables ([`LowerTables`]), computed
    /// once by the caller and reused across rebuilds.
    pub fn new(program: &Program, tables: &LowerTables, channels: &CheckerChannels) -> Self {
        let ctx = subset_ctx(program, tables, channels, 0);
        let mut mir = MirProgram::default();
        lower_methods_into(&ctx, &mut mir, program);
        for init in &program.inits {
            let body = lower_init(&ctx, init.path.clone(), &init.stmts);
            mir.inits.push(MirInit {
                module: init.path.clone(),
                body,
            });
        }
        let next_closure = ctx.next_closure.get();
        let mut closures = ctx.closures.into_inner();
        closures.sort_by_key(|c| c.id.0);
        mir.closures = closures;
        SubsetLowering {
            changed_inputs: crate::ChangedInputs::default(),
            reset_inputs: true,
            mir,
            lowered: fxhash::FxHashSet::default(),
            next_closure,
        }
    }

    /// Adopt the per-instance channels of `channels` (the checker's state
    /// as of now) for the next monomorphization. Lowered bodies only name
    /// their seed sites, so revised per-instance values need no re-lowering;
    /// they only have to be current when an instance is typed.
    pub fn refresh_instance_channels(&mut self, channels: &CheckerChannels) {
        let mut changes = crate::ChangedInputs::since(self.changed_inputs.epoch);
        changes.epoch = changes
            .epoch
            .checked_add(1)
            .expect("channel epoch exhausted");
        changes.full_reset = true;
        self.refresh_instance_channels_with_changes(channels, changes);
    }

    /// Adopt the channel snapshot with a single merged stream's change window.
    /// A missed epoch or any changed MIR body forces conservative invalidation.
    /// The change window is consumed without copying its recorded keys.
    /// Return contracts remain in the driver's separate mono input bundle.
    pub fn refresh_instance_channels_with_changes(
        &mut self,
        channels: &CheckerChannels,
        changes: crate::ChangedInputs,
    ) {
        self.mir.instance_seeds = channels.instance_seeds.clone();
        self.mir.instance_dispatch = channels.instance_dispatch.clone();
        self.mir.numeric_calls = channels.numeric_calls.clone();
        let reset = self.reset_inputs || changes.base_epoch != self.changed_inputs.epoch;
        self.changed_inputs = changes;
        self.changed_inputs.full_reset |= reset;
        self.reset_inputs = false;
    }

    /// Invalidations from the latest refresh, including conservative MIR resets.
    /// Read after every refresh, even if the channel epoch did not advance.
    /// This record describes inputs, not whether a mono consumer has applied it.
    pub fn changed_inputs(&self) -> &crate::ChangedInputs {
        &self.changed_inputs
    }

    /// Finish a refresh window after appending or replacing MIR bodies.
    /// The returned invalidations include those body edits immediately, and
    /// consume their pending reset so the next channel refresh does not reset
    /// a session a second time for the same edits.
    pub fn finish_changes(&mut self) -> crate::ChangedInputs {
        self.changed_inputs.full_reset |= std::mem::take(&mut self.reset_inputs);
        self.changed_inputs.clone()
    }

    /// Whether free function `symbol`'s body was already added on demand.
    pub fn is_lowered(&self, symbol: &str) -> bool {
        self.lowered.contains(symbol)
    }

    /// Lower free function `symbol`'s body into the program against the
    /// CURRENT channel state. Returns `false` when `symbol` names no function
    /// of `program` or was already lowered -- nothing was added, and a caller
    /// looping on demand should treat a repeat as an unsatisfiable demand
    /// rather than retry forever.
    pub fn add_function(
        &mut self,
        program: &Program,
        tables: &LowerTables,
        symbol: &str,
        channels: &CheckerChannels,
    ) -> bool {
        if self.lowered.contains(symbol) {
            return false;
        }
        let Some(info) = program.functions.get(symbol) else {
            return false;
        };
        let ctx = subset_ctx(program, tables, channels, self.next_closure);
        lower_function_into(&ctx, &mut self.mir, info);
        self.next_closure = ctx.next_closure.get();
        let mut closures = ctx.closures.into_inner();
        closures.sort_by_key(|c| c.id.0);
        self.mir.closures.extend(closures);
        self.reset_inputs = true;
        self.lowered.insert(symbol.to_string());
        true
    }

    /// Re-lower an already-added free function against revised checker
    /// channels without rebuilding methods, initializers, or other functions.
    /// Old closure entries stay unreachable; replacement closures receive new
    /// ids from the shared counter and are appended to the program.
    pub fn refresh_function(
        &mut self,
        program: &Program,
        tables: &LowerTables,
        symbol: &str,
        channels: &CheckerChannels,
    ) -> bool {
        if !self.lowered.contains(symbol) {
            return false;
        }
        let Some(info) = program.functions.get(symbol) else {
            return false;
        };
        let Some(index) = self
            .mir
            .functions
            .iter()
            .position(|function| function.symbol == symbol)
        else {
            return false;
        };
        let ctx = subset_ctx(program, tables, channels, self.next_closure);
        let mut replacement = MirProgram::default();
        lower_function_into(&ctx, &mut replacement, info);
        self.next_closure = ctx.next_closure.get();
        let mut closures = ctx.closures.into_inner();
        closures.sort_by_key(|closure| closure.id.0);
        self.mir.closures.extend(closures);
        self.mir.functions[index] = replacement
            .functions
            .pop()
            .expect("one requested function was lowered");
        self.reset_inputs = true;
        true
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn initial_missing_and_untracked_refreshes_require_a_reset() {
        let program = Program::empty();
        let tables = LowerTables::new(&program);
        let channels = CheckerChannels {
            expr_types: &Default::default(),
            receiver_types: &Default::default(),
            receiver_owners: &Default::default(),
            view_args: &Default::default(),
            numeric_calls: &Default::default(),
            field_calls: &Default::default(),
            sum_views: &Default::default(),
            call_locations: &Default::default(),
            lift_errs: &Default::default(),
            fields_loops: &Default::default(),
            type_names: &Default::default(),
            typeof_types: &Default::default(),
            null_props: &Default::default(),
            type_tests: &Default::default(),
            keyed_dispatch: &Default::default(),
            instance_seeds: &Default::default(),
            instance_dispatch: &Default::default(),
            instance_returns: &Default::default(),
        };
        let mut lowering = SubsetLowering::new(&program, &tables, &channels);
        let mut changes = crate::ChangedInputs::since(0);
        changes.epoch = 1;
        lowering.refresh_instance_channels_with_changes(&channels, changes);
        assert!(lowering.changed_inputs().full_reset);
        let mut next = crate::ChangedInputs::since(1);
        next.epoch = 2;
        next.instance_seeds.remove(Span::new(1, 2));
        lowering.refresh_instance_channels_with_changes(&channels, next.clone());
        assert_eq!(lowering.changed_inputs(), &next);
        // A skipped refresh breaks the epoch chain, even if its map is empty.
        let mut missed = crate::ChangedInputs::since(3);
        missed.epoch = 4;
        lowering.refresh_instance_channels_with_changes(&channels, missed);
        assert!(lowering.changed_inputs().full_reset);
        lowering.refresh_instance_channels(&channels);
        assert!(lowering.changed_inputs().full_reset);
        assert_eq!(lowering.changed_inputs().epoch, 5);
    }
}
