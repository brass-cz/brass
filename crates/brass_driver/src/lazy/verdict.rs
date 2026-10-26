//! Span ownership and held-diagnostic gates.

use super::LazyState;
use crate::{print_diags, render_errors};
use brass_hir::Program;
use brass_parser::Span;
use std::io;

/// Every function and method body's span range, for attributing a
/// diagnostic to the body containing it. Lazy checking HOLDS an error whose
/// span lies inside a body execution never needs; an error inside a needed
/// body -- or outside any body at all (top-level code, declarations,
/// signatures) -- is fatal at the next gate. Method owners are marked needed
/// from the monomorphized batch before native compilation.
pub(super) struct BodySpans {
    ranges: Vec<(String, usize, usize)>,
}

impl BodySpans {
    pub(super) fn new(program: &Program) -> Self {
        // Declarations establish the shared typing environment. Only body
        // diagnostics may be held for an uncalled function; a rejected
        // signature must not reach a caller or native compilation.
        let mut ranges = Vec::new();
        for (symbol, f) in &program.functions {
            let span = f.decl.body.span;
            ranges.push((symbol.clone(), span.lo, span.hi));
        }
        for info in program.types.values() {
            let mut methods: Vec<&brass_hir::MethodInfo> = Vec::new();
            match &info.kind {
                brass_hir::TypeKind::Record { methods: ms, .. } => methods.extend(ms.values()),
                brass_hir::TypeKind::Sum { variants } => {
                    for v in variants {
                        methods.extend(v.methods.values());
                    }
                }
            }
            for m in methods {
                // A reflective `-> infer!` template never runs itself: its
                // diagnostics come from the specializations generated from it,
                // which report at the template's source positions. Owning them
                // by the never-needed template would let a rejected
                // specialization run, so they stay unowned (always fatal).
                if brass_hir::keyed_return(m.decl.ret.as_ref()) {
                    continue;
                }
                if let Some(body) = &m.decl.body {
                    let span = body.span;
                    ranges.push((
                        format!("method:{}:{}", info.symbol, m.decl.name),
                        span.lo,
                        span.hi,
                    ));
                }
            }
        }
        BodySpans { ranges }
    }

    /// The body whose range contains `span`, if any.
    pub(super) fn owner(&self, span: Span) -> Option<&str> {
        tracing::trace!(target: "brass::lazy", lo = span.lo, ranges = ?self.ranges, "owner probe");
        self.ranges
            .iter()
            .find(|(_, lo, hi)| *lo <= span.lo && span.lo < *hi)
            .map(|(symbol, _, _)| symbol.as_str())
    }
}

/// What a gate should do about the held diagnostics.
pub(super) enum FatalVerdict {
    /// Nothing on the needed path: proceed.
    Clean,
    /// Fatal diagnostics were printed: abort with this code.
    Fatal(u8),
    /// A runtime-demanded body discovered a keyed call that requires the
    /// narrow eager fallback.
    NeedsEager,
}

/// Judge the held diagnostics at a gate. A fatal candidate is CONFIRMED
/// before it aborts anything: a keyed (`-> infer!`) program's first pass
/// records provisional errors that its continuation may clear, so the gate
/// waits for the checker thread's final verdict once -- and only once
/// something looked fatal; clean programs
/// never wait here. A confirmed failure reports the complete verdict (see
/// [`LazyState::held_all`]), sorted and deduplicated and rendered like the
/// eager pipeline: the checker has finished by then, and a diagnostic in a
/// body the failed run never reached is as much a part of it as the one that
/// stopped the run.
pub(super) fn judge_fatal(
    lazy: &mut LazyState,
    bodies: &BodySpans,
    sources: &brass_resolve::SourceMap,
) -> FatalVerdict {
    if lazy.fatal(bodies).is_empty() {
        return FatalVerdict::Clean;
    }
    // Wait for the checker thread to finish publishing continuation results.
    // The wait is on its own progress, so its queue must be running.
    lazy.resume_background();
    while !lazy.closed && !lazy.needs_eager {
        lazy.pump_blocking();
    }
    if lazy.needs_eager {
        return FatalVerdict::NeedsEager;
    }
    if lazy.fatal(bodies).is_empty() {
        return FatalVerdict::Clean;
    }
    for line in render_errors(&lazy.held_all(), sources) {
        eprintln!("{line}");
    }
    FatalVerdict::Fatal(1)
}

/// Exit the process if the needed path holds a confirmed fatal diagnostic,
/// printing the checker's complete verdict as [`judge_fatal`] does (reached
/// from JIT code, which cannot unwind, hence `exit`). A keyed call discovered
/// after execution began cannot safely rerun prior side effects, so the
/// narrow demand fallback asks for `--eager`.
pub(super) fn exit_if_fatal(
    lazy: &mut LazyState,
    bodies: &BodySpans,
    sources: &brass_resolve::SourceMap,
) {
    if lazy.fatal(bodies).is_empty() && !lazy.needs_eager {
        return;
    }
    // Wait for the checker thread's final verdict. The wait is on its own
    // progress, so its queue must be running.
    lazy.resume_background();
    while !lazy.closed {
        lazy.pump_blocking();
    }
    use std::io::Write;
    // A runtime specialization fallback cannot replay prior side effects,
    // but it can finish checking. Preserve that source verdict before giving
    // rerun guidance for a program whose continuation checked cleanly. A
    // confirmed failure reports the complete verdict, as at the entry gate.
    let fatal = if lazy.needs_eager || !lazy.fatal(bodies).is_empty() {
        lazy.held_all()
    } else {
        Vec::new()
    };
    if !fatal.is_empty() {
        let _ = io::stdout().flush();
        print_diags(render_errors(&fatal, sources));
        lazy.counters.emit_summary();
        std::process::exit(1);
    }
    if lazy.needs_eager {
        let _ = io::stdout().flush();
        eprintln!(
            "error: a runtime-demanded body requires reflective specialization; rerun with --eager"
        );
        lazy.counters.emit_summary();
        std::process::exit(1);
    }
}
