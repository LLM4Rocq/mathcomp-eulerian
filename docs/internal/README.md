# Historical record (`docs/internal/`)

This folder is a **trace of how the formalization was actually reached**.
Each document was authoritative at some point in the project's life;
none of them is authoritative now. The current authoritative sources are:

- The blueprint at <https://llm4rocq.github.io/mathcomp-eulerian/>
- [`PROOF_STATEMENTS.md`](../../PROOF_STATEMENTS.md) (per-result table)
- [`FORMAL_VS_STANLEY.md`](../../FORMAL_VS_STANLEY.md) (notation glossary)
- The Rocq sources themselves (kernel-checked, axiom-free, all 23 `.v` files
  full-compile to `.vo`)

The files here are kept verbatim — including their stale "current state"
snapshots — because the *path* taken matters: the dead-ends and recoveries
are part of the technical record.

## Reading order (chronological)

| # | File | What it captured |
|---|------|------------------|
| 1 | [`eulerian_mathcomp_plan.md`](eulerian_mathcomp_plan.md) | Original architecture sketch — Layers 0–5 of the Eulerian / β development. Everything below grew from this. |
| 2 | [`AXIOMS_TODO.md`](AXIOMS_TODO.md) | Inventory of the 13 axioms posed during early development and the trail of how each was closed (or, in one case, eliminated as mathematically false). |
| 3 | [`M2_PSI_INFORMAL.md`](M2_PSI_INFORMAL.md) | Stanley §1.6.3 ψᵢ definition + involutivity, paper-style. The mathematical scaffold for `psi_core.v`. |
| 4 | [`M3_COMMUTATIVITY_INFORMAL.md`](M3_COMMUTATIVITY_INFORMAL.md) | Stanley Fact \#1 (commuting involutions), paper-style. Scaffold for `psi_comm.v`. |
| 5 | [`M4_DESCENT_EFFECT_INFORMAL.md`](M4_DESCENT_EFFECT_INFORMAL.md) | Stanley Fact \#2 (descent change under ψᵢ), paper-style. Scaffold for the descent-effect chain in `psi_descent_*`. |
| 6 | [`M5_FACT3_INFORMAL.md`](M5_FACT3_INFORMAL.md) | Stanley Fact \#3 — the M-class multiset identity. Scaffold for `fact3` and `phi_w_support_general` in `psi_cdindex_support.v`. |
| 7 | [`M6_THM163_INFORMAL.md`](M6_THM163_INFORMAL.md) | Stanley Theorem 1.6.3 (cd-index has nonneg coefficients), paper-style. |
| 8 | [`M7_CLOSING_AXIOMS_INFORMAL.md`](M7_CLOSING_AXIOMS_INFORMAL.md) | The mid-project diagnosis that `beta_swap_lt_caseB` (one of the original axioms) was *mathematically false* as stated, with counterexample. The eventual resolution went via the cd-index path (Stanley Prop 1.6.4) rather than per-step swap monotonicity. |
| 9 | [`OPTION_A_PROGRESS.md`](OPTION_A_PROGRESS.md) | Progress log of the Option-A refactor that replaced fuel-Fixpoint induction with structural recursion on `mmtree`. Produced `psi_descent_v2.v` + `psi_descent_thms.v`. |
| 10 | [`NEXT_ITERATION.md`](NEXT_ITERATION.md) | Status note marking Option A complete; describes the original `psi_descent.v` problem and how it was resolved. |
| 11 | [`NEXT_SESSION.md`](NEXT_SESSION.md) | "Formalization complete" status note from the all-axioms-closed milestone. |
| 12 | [`MMTREE_REFACTOR_PLAN.md`](MMTREE_REFACTOR_PLAN.md) | Plan to fix the OOM walls in `psi_cdindex_tree_hlc.v` / `psi_cdindex_tree.v` via a single `mmtree_shape` Opaque-sealed Fixpoint. Successful. |
| 13 | [`BUILD_PLAN.md`](BUILD_PLAN.md) | Build-status snapshot at the `v1-vos-stable` tag (21/21 `.vos`, 18/21 `.vo`). The state before the compile-all push that finished the project. |
| 14 | [`REFACTOR_PLAN.md`](REFACTOR_PLAN.md) | V1 surgical refactor plan for the last 3 `.vo` holdouts. Diagnosed correctly but the proposed surgical fixes hit kernel walls *as stated*; the eventual fix path was different (mathcomp compat + bit-level injectivity argument). |
| 15 | [`REFACTOR_PLAN_V2.md`](REFACTOR_PLAN_V2.md) | V2 tree-native re-architecture, marked **ABANDONED** at its top. Two attempts both hit the kernel wall. The postmortem at the bottom of this doc is part of why we eventually pursued the compile-all path. |
| 16 | [`COMPILE_ALL_REFACTOR_PLAN.md`](COMPILE_ALL_REFACTOR_PLAN.md) | The plan that actually finished the project (May 2026 session). Replaces the kernel-wall narrative with the real diagnosis (mathcomp signature drift) and documents every compat fix. **Marked complete.** |

## What changed between the last historical snapshot and the current state

For most of these documents the relevant state-of-the-world claim was
"21/21 `.vos`, 18/21 `.vo`, 3 holdouts hardware-bound". That snapshot was
correct at the time; it is now obsolete. The compile-all session
([`COMPILE_ALL_REFACTOR_PLAN.md`](COMPILE_ALL_REFACTOR_PLAN.md)) closed
the gap by:

- Recognizing that the supposed "kernel wall" in `psi_cdindex_support.v`
  was actually a missing M-class injectivity argument; closing it via
  bit-level recovery in `psi_cdindex_core.v`.
- Treating `perm_seq_bridge.v`'s `.vo` failures as mathcomp signature
  drift (post-2.5 changes to `sorted_eq`, `mem_head`, `index_inj`, etc.)
  rather than a kernel-cost issue, and applying lemma-by-lemma compat fixes.
- Letting `beta_swap.v` fall out unchanged once `perm_seq_bridge.vo` was
  built.

Result: 23/23 `.v` files compile to `.vo`, headline theorems are
`Closed under the global context`, `coqchk` validates the library.

## Why keep these around

1. **Reproducibility of the journey.** Anyone trying a similar Stanley
   formalization will find here the dead-ends, the false starts, and
   the corrections — not just the polished final form.
2. **Debugging memory.** When a future change breaks something, the
   plans here document the constraints we previously discovered (e.g.,
   tree-shape Opaque-sealing, the `mmtree_shape` refactor).
3. **Honesty about the fact-3 / Fact-#2 chain.** `M7_CLOSING_AXIOMS_INFORMAL.md`
   recording that one originally-stated axiom was *false* — and the eventual
   re-routing through Stanley Prop 1.6.4 — is part of the technical record.

If you only want the math, read the blueprint. If you want to see how a
full Rocq formalization of Stanley §1.6.3 actually got built, read these
files in the order above.
