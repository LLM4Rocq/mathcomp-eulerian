> **Historical document.** Progress log of the 2026-04-24 refactor that
> rewrote five structural lemmas in `psi_descent.v` to do their heavy
> inductive work as **structural recursion on `mmtree nat`** rather than
> strong induction on `size w`.  Result: `psi_descent_v2.v` (151 KB
> `.vo`) + `psi_descent_thms.v` (82 KB `.vo`), both compiling in seconds.
> See [`README.md`](README.md).

# Option A: Structural Recursion on mmtree --- Progress Log

## Goal

Rewrite the 5 structural lemmas in `psi_descent.v` so that the heavy
inductive work is done by **structural recursion on `mmtree nat`** rather
than strong induction on `size w`.  This should produce dramatically
smaller proof terms, enabling full `-vo` compilation.

## Team

| Role | Perspective |
|------|-------------|
| **Mathematician** (Stanley) | Keeps proofs faithful to EC1 section 1.6.3. Every lemma must correspond to an identifiable step in the book. |
| **Rocq Engineer** | Designs the Rocq code: chooses representations, writes definitions, manages proof terms. Watches for kernel blowup. |
| **Devil's Advocate** | Challenges every design choice. Asks: "Will this actually compile? Does the bridge introduce the same blowup? Are we just moving the problem?" |

## Root Cause Analysis

Two independent causes of compilation failure:

### Cause 1: `tree_structure` proof-term blowup

The `tree_structure` lemma proves 5 properties simultaneously
via strong induction `elim=> [|n IH]` with a 3-way case split at
`mm_pos`.  Each recursive step:

1. Carries the full 5-tuple conjunction as IH
2. Triples via `ltngtP i j` case split
3. Each branch unfolds `window_size_cons`, `window_at_cons`,
   `has_left_child_cons` which are themselves proved via
   `fuel_monotone` applications

The proof term grows as O(3^depth * 5) per recursion level, and the
min-max tree can have depth O(n).  Serialization is super-linear in
proof term size.

**Fix**: Structural induction on `mmtree` with opaque bridge lemmas.
Proof terms are O(n) instead of O(3^n).

### Cause 2: `rewrite !index_uniq` exponential tactic search

The descent-effect theorems (`rs_head_max_descent`, `rs_head_min_no_descent`)
used `rewrite !index_uniq ?Hsz_rs ?ltnW //` which causes Rocq to try
every combination of `!` (repeat), `?` (optional), and `//` (solve).
This creates exponentially many attempts.

**Fix**: Replace with explicit `@index_uniq _ 0 0 _ Hlt0 Hu_rs` and
`@index_uniq _ 0 1 _ Hlt1 Hu_rs` applications.

---

## Final Results

| Component | Original | Option A |
|-----------|----------|----------|
| `tree_structure` Qed | 50h+ / 243GB+ (killed) | **8s / <1GB** |
| 5 structural lemmas | never verified | **fully verified (8s)** |
| descent-effect Qeds | never reached | **7s** |
| Full .vo | never produced | **produced: 151KB + 82KB** |
| Total compile time | never finished | **15 seconds** |
| Peak RAM | 243 GB+ (still growing) | **< 1 GB** |
| 0 Admitted? | YES (0 Admitted) | **YES (0 Admitted)** |
| psi_cdindex.v compat | blocked | **compiles with -vos (7s)** |

**Improvement: from never-finishing (50h+, 243GB+) to 15 seconds.**

---

## Architecture

### File structure

- `psi_descent_v2.v` (1121 lines) — core definitions + tree_structure
  - `is_descent_seq`, `has_left_child` definitions (unchanged)
  - `valid_mm` tree validity predicate
  - `valid_mm_build` (mmtree_of_seq_mm produces valid trees)
  - 9 opaque bridge lemmas (ws/wa/hlc x left/right/root)
  - Base-case lemmas (pre_win_lt_max_eq, pre_win_gt_min_eq, xone_desc_eq)
  - `tree_structure_via_tree` (structural induction on mmtree)
  - `tree_structure` (derived via mmtree_of_seq_mmK round-trip)
  - 5 projection lemmas (post_window_extremum, etc.)

- `psi_descent_thms.v` (698 lines) — descent-effect theorems
  - Helper lemmas (elem_in_range, head_min_not_descent, etc.)
  - `descent_psi_interior`, `descent_psi_rboundary`, `descent_psi_lboundary_R`
  - 4 main theorems: `descent_psi_R_add/remove`, `descent_psi_LR_swap1/2`
  - Non-triviality examples

### Key design decisions

1. **Tree as recursion guide only**: Statements stay in terms of
   `window_size`, `window_at`, `has_left_child` (sequence operations).
   The tree provides the termination argument, not the API.

2. **Opaque bridge lemmas**: Each of the 9 bridges (ws/wa/hlc x left/right/root)
   is proved once via the fuel-based cons lemma, then made `#[global] Opaque`.
   The structural induction proof never touches fuel.

3. **`abstract` on descent-effect branches**: Each case branch in the
   4 descent-effect theorems is wrapped in `abstract(...)` to prevent
   proof-term accumulation during Qed.

4. **Explicit `index_uniq` applications**: Replace `rewrite !index_uniq ...`
   with positional `@index_uniq _ 0 k _ Hlt Huniq` to avoid exponential search.

---

## Alignment with Stanley EC1 section 1.6.3

The structural proof follows Stanley's reasoning exactly:

- **Left subtree case** (i < size sl): "position i is in the left subtree"
  — IH applies directly, with boundary case when window reaches root
  (root is first-occurring min-or-max, so strictly separates window
  from parent via `notin_take_mm`)

- **Root case** (i = size sl): "position i IS the root"
  — head is min/max of subtree, exactly-one-descent follows from root
  being extremum, window goes to end of sequence (P1 vacuous)

- **Right subtree case** (i > size sl): "position i is in the right subtree"
  — IH with position re-indexing (i' = i - size sl - 1), boundary case
  when i' = 0 (root is adjacent, need `nth_w_mm_pos` extremum argument)

---

## Progress Log

### Session 1: 2026-04-23

- Analyzed root cause (fuel-based strong induction → O(3^n) proof terms)
- Designed bridge-lemma architecture
- Implemented `valid_mm`, `valid_mm_build`, 9 bridge lemmas
- Proved `tree_structure_via_tree` by structural induction (3 agents in parallel)
- Derived `tree_structure`, 5 projection lemmas
- Core compiles: **8s, <1GB** (vs original: 50h+, 243GB+, never finished)

### Session 2: 2026-04-24 (psi_descent completion)

- Ported descent-effect theorems from original `psi_descent.v`
- First attempt: full file killed at 76 min / 74 GB (descent-effect serialization)
- Added `abstract` wrappers: reduced to killed at ~60 min / ~60 GB
- Identified second root cause: `rewrite !index_uniq` exponential search
- Fixed with explicit `index_uniq` applications
- Split into two files: `psi_descent_v2.v` + `psi_descent_thms.v`
- **Both compile in 15 seconds total, 233 KB .vo, 0 Admitted**
- Updated `_CoqProject` and `psi_cdindex.v` imports

### Session 3: 2026-04-24 (closing beta_swap axioms)

**Status**: In progress

**Remaining axioms**: Only 2 (both in beta_swap.v):
- `beta_swap_lt_caseA`: j+1 in D or j at boundary → omega strict containment
- `beta_swap_lt_caseB`: j+1 not in D → omega-sets differ by adjacent swap

**phi_w_support** and **strict_witness_exists**: Already proved in psi_cdindex.v
(the AXIOMS_TODO.md was stale — these were resolved in prior sessions).

**Architecture for closing beta_swap**:

The proof chain:
1. `toggle_at_j_omega_strict_superset` (proved in beta_swap.v §H)
   → omega_set D ⊊ omega_set (toggle_at D j) [Case A only]
2. TYPE BRIDGE (MISSING): connect omega_set (finset) to omega_seq (seq)
3. `omega_monotone_class_count` + `strict_witness_exists` (proved in psi_cdindex.v)
   → seq-level Prop 1.6.4
4. beta D < beta (toggle_at D j) [target]

**The gap**: No function converts between `{set 'I_n}` and `seq nat`
for descent positions, and no lemma relates `omega_set` to `omega_seq`.

**Plan**:
- [ ] Build type bridge: `desc_set_to_seq` / `desc_seq_to_set` + equivalence
- [ ] Prove `beta_omega_strict` at finset level (Case A)
- [ ] Prove `beta_swap_lt_caseA` from bridge + omega_strict_superset
- [ ] Prove `beta_swap_lt_caseB` (harder — needs cd-index coefficient comparison)

**Current state** (2 agents in parallel):
- Agent 1: Building type bridge (set_to_seq + omega equivalence) for omega_proper_beta_lt
- Agent 2: Trying direct Foata injection proof for beta_swap_lt_both_in

**Key discoveries**:
- phi_w_support and strict_witness_exists were already proved (AXIOMS_TODO was stale)
- Only 2 axioms remain: omega_proper_beta_lt + beta_swap_lt_caseB
  (was: beta_swap_lt_caseA + beta_swap_lt_caseB)
- beta_swap_lt_caseA was proved from omega_proper_beta_lt + toggle_at_j_omega_strict_superset
- vm_compute/native_compute cannot evaluate beta (factorial-sized enumeration)
- Restructured into beta_omega.v + beta_bridge.v + beta_swap.v (3 files)

**Status update**: Both agents still running. Current axiom state:
1. `omega_proper_beta_lt` (beta_bridge.v:97) — Prop 1.6.4, needs type bridge
2. `beta_swap_lt_caseB` (beta_swap.v:72) — omega-incomparable case

Both are HARD to close without the full cd-index theorem (phi_w_support_general).
The cd-index theorem is PROVED at seq level (fact3 in psi_cdindex.v) but the
bridge from fact3 → phi_w_support → omega_proper_beta_lt is not built.

The phi_w_support characterization is verified for S_3 and S_4 via vm_compute
but not proved in general. A general proof would need to show that fact3
implies the support characterization, which requires an additional
combinatorial argument about how expand_cde and omega_seq interact.

### Session 3 Final Status

**2 Axioms remain** (down from 2 at start of session, but restructured):
1. `omega_proper_beta_lt` (beta_bridge.v) — Prop 1.6.4 at finset level
2. `beta_swap_lt_caseB` (beta_swap.v) — omega-incomparable case

**What was accomplished in Session 3**:
- Confirmed phi_w_support and strict_witness_exists are already proved
- Extracted omega machinery into beta_omega.v (clean separation)
- Created beta_bridge.v with type bridge infrastructure (set_to_seq, mem lemmas)
- Proved beta_swap_lt_caseA from omega_proper_beta_lt + toggle_at_j_omega_strict_superset
- Restructured beta_swap.v to import beta_omega + beta_bridge

**What blocks closing the remaining 2 axioms**:
Both require the cd-index theorem at finset level, which requires:
  (a) phi_w_support_general — the cd-index coefficient identity for all n
  (b) {perm 'I_n.+1} ↔ seq nat bijection — connecting beta to M-class counting

These represent the mathematical CORE of Stanley's Prop 1.6.4 / Theorem 1.6.3,
not engineering issues. The seq-level proof (fact3) exists but the finset bridge
is substantial (~200 LOC estimated).

### Overall project status after all 3 sessions

| File | Status | Notes |
|------|--------|-------|
| psi_descent_v2.v | Fully compiled (8s) | tree_structure solved |
| psi_descent_thms.v | Fully compiled (7s) | descent-effect theorems |
| beta_omega.v | Compiled | omega infrastructure |
| beta_bridge.v | 1 Axiom | Prop 1.6.4 (omega_proper_beta_lt) |
| beta_swap.v | 1 Axiom | Case B (beta_swap_lt_caseB) |
| All other .v files | Compiled, 0 axioms | |

**Total**: 2 Axioms, 0 Admitted in active build.
All .vo files produced. Full build compiles.

### Agent results for beta_swap axioms

**Bridge agent** (omega_proper_beta_lt):
- Built set_to_seq infrastructure (5 proved lemmas)
- Proved omega_set_seq_local_bridge (key bridge connecting finset/seq omega maps)
- Axiom remains: needs phi_w_support_general (~500-1000 LOC) + perm↔seq bijection (~200 LOC)

**Foata agent** (beta_swap_lt_caseB):
- Analyzed multiple approaches: omega extension, adjacent transposition, reduction chains, complement symmetry
- Conclusion: direct proof needs piecewise injection (transposition for "good" case, cyclic rotation for "bad" case), ~300-500 LOC
- Fixed compilation issue in beta_bridge.v

**Final state**: 2 Axioms, 0 Admitted, all .vo files produced, full build compiles.
