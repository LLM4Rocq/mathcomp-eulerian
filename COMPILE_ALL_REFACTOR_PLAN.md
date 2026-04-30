# Compile-All Refactor Plan

Snapshot date: 2026-04-30.
Toolchain observed locally: Rocq 9.1.1, OCaml 5.2.1.

## Objective

Make the repository have one maintained build target where every maintained
Rocq source compiles to full `.vo`, not only `.vos`.

This plan treats "all files" carefully because the repository currently mixes:

- maintained split files listed in `_CoqProject`;
- historical monoliths that duplicate older versions of the split development;
- prototype files that compile only because they contain `Admitted`.

The recommended end state is: every file ending in `.v` is either maintained
and included in the build, or is a thin compatibility wrapper over maintained
files. Historical/prototype material should move out of the `.v` build surface.

## Current State

There are 23 maintained `.v` files in the repository.

`_CoqProject` currently includes all 23 maintained files. Historical/prototype
sources were moved out of the `.v` build surface:

- `archive/psi.v.txt`;
- `archive/psi_base.v.txt`;
- `archive/psi_descent_wf.v.txt`.

Observed build results:

- `make -j2` originally produced 18 `.vo` files and then spent several minutes
  in `psi_cdindex_support.v`; the run was stopped manually.
- `make vos -j2` succeeds for the active `_CoqProject` target.
- `psi_cdindex_support_defs.v` has been split out and full-compiles quickly.
- The previous `.vo` wall in `D_vertex_descent_transition` has been removed:
  that lemma is now a small corollary of `exactly_one_descent_LR`.
- A real proof gap is now exposed in `uniq_map_char_mono_powerset` /
  `check_fact3_true`: the old proof tried to derive uniqueness of the left
  multiset from subset plus equal size, which is not sufficient.
- The active `.vo` holdouts are leaf files:
  - `psi_cdindex_support.v`;
  - `perm_seq_bridge.v`;
  - `beta_swap.v`.
- `psi_descent.v` is now a compatibility wrapper exporting
  `psi_descent_v2.v` and `psi_descent_thms.v`; it full-compiles quickly.
- The archived `psi.v` and `psi_base.v` are stale monoliths that previously
  failed even at `-vos`.
- The archived `psi_descent_wf.v` is a prototype that full-compiled but
  contained several `Admitted` proofs.

## Refactor Principles

1. Keep one source of truth per theorem.
   The split files are the maintained source; monoliths should not duplicate
   active proofs.
2. Keep public theorem names stable.
   Downstream files should see the same API, even if proof bodies move.
3. Make heavy proof files leaf-like.
   The kernel should check large proof terms once, behind small opaque
   interfaces, instead of rebuilding them through downstream bridges.
4. Prefer structural or boolean interfaces over repeated fuel-Fixpoint
   reduction.
   The existing bottlenecks repeatedly reason through `window_size_fuel`,
   `has_left_child_fuel`, `iota`, `take`, `drop`, and `nth`.
5. Add compile gates before large rewrites.
   Every phase should end with a measurable build command.

## Target File Topology

Keep the current successful split as the base:

```text
ordinal_reindex -> perm_compress -> descent -> eulerian -> beta
                                            -> beta_omega -> beta_bridge

mmtree -> psi_core -> psi_comm -> psi_descent_v2 -> psi_descent_thms
      -> psi_cdindex_defs -> psi_cdindex_tree_shape
      -> psi_cdindex_tree_hlc -> psi_cdindex_tree
      -> psi_cdindex_core -> psi_cdindex_witness
      -> psi_cdindex_support_defs
      -> psi_cdindex_support
      -> perm_seq_bridge
      -> beta_swap
```

Historical file treatment already applied:

| File | Recommendation | Reason |
|------|----------------|--------|
| `psi.v` | Archived as `archive/psi.v.txt` | 6633-line stale monolith; previously syntax-broken. |
| `psi_base.v` | Archived as `archive/psi_base.v.txt` | 2722-line stale combined file; previously syntax-broken. |
| `psi_descent.v` | Kept as wrapper exporting `psi_descent_v2` and `psi_descent_thms` | Stable import name for old scripts. |
| `psi_descent_wf.v` | Archived as `archive/psi_descent_wf.v.txt` | Prototype file with `Admitted` proofs. |

## Phase 0: Freeze and Measure

Goal: establish a clean, reproducible baseline before changing proofs.

Tasks:

1. Commit or otherwise preserve the current state.
2. Run a clean signature build:

```bash
make clean
make vos -j2
```

3. Measure the three active `.vo` holdouts one at a time:

```bash
rocq compile -q -w -deprecated-library-file -w -notation-overridden \
  -time-file psi_cdindex_support.time \
  -R . mathcomp_eulerian psi_cdindex_support.v

rocq compile -q -w -deprecated-library-file -w -notation-overridden \
  -time-file perm_seq_bridge.time \
  -R . mathcomp_eulerian perm_seq_bridge.v

rocq compile -q -w -deprecated-library-file -w -notation-overridden \
  -time-file beta_swap.time \
  -R . mathcomp_eulerian beta_swap.v
```

4. Record first failing or long-running lemma names in this file or
   `BUILD_PLAN.md`.

Gate:

- `make vos` passes.
- The project has an agreed definition of which historical files are kept as
  wrappers and which are archived.

## Phase 1: Remove Historical Duplication

Status: complete.

Goal: make "all `.v` files" mean something enforceable.

Tasks:

1. Archived `psi.v`, `psi_base.v`, and `psi_descent_wf.v` under `archive/`
   with non-`.v` extensions.
2. Replaced `psi_descent.v` with a minimal compatibility wrapper:

```coq
From mathcomp Require Import all_ssreflect.
Require Export psi_descent_v2 psi_descent_thms.
```

3. Updated `_CoqProject` so every remaining maintained `.v` file is listed in
   topological order.

Gate:

- Every remaining `.v` file at least passes `-vos`. Current status:
  `make vos -j2` succeeds.
- `rg -n "\b(Axiom|Admitted|admit)\b" *.v` reports only intentionally archived
  or explicitly accepted prototype material.

## Phase 2: Refactor `psi_cdindex_support.v`

Status: in progress.

Goal: make the main support/fact3 leaf full-compile to `.vo`.

Why first:

- `perm_seq_bridge.v` imports `psi_cdindex_support.v`.
- `beta_swap.v` imports `perm_seq_bridge.v`.
- If `psi_cdindex_support.v` becomes a real `.vo`, the two downstream holdouts
  may become substantially cheaper without further changes.

Recommended split:

| New file | Contents |
|----------|----------|
| `psi_cdindex_support_defs.v` | Done. `cde_width`, offsets, transitions, `expand_cde` membership iff, and transition/omega bridge. |
| `psi_cdindex_expand.v` | `expand_cde` membership characterization and uniqueness. |
| `psi_cdindex_offsets.v` | `S_w_seq`, `D_offsets`, and width/offset alignment. |
| `psi_cdindex_fact3.v` | `phi_w_support_general`, `D_vertex_descent_transition`, `check_fact3_true`, `fact3`. |
| `psi_cdindex_support.v` | Thin compatibility re-export. |

Proof refactor targets:

| Current lemma | Issue | Refactor direction |
|---------------|-------|--------------------|
| `expand_cde_mem_transitions` | Induction over `seq cde` duplicates transition arithmetic. | Prove a compact boolean reflection lemma once, then expose only the iff interface. |
| `transitions_expand_cde_mem` | Reverse direction repeats the same structural cases. | Share the same reflected support predicate. |
| `D_offsets_phi_w_eq_S_w_seq` | Combines offset arithmetic with tree classification. | Split offset arithmetic from tree facts. |
| `D_vertex_descent_transition` | Re-entered `take`/`drop`/window reasoning near the kernel wall. | Done: replaced by a wrapper over `exactly_one_descent_LR`. |
| `uniq_map_char_mono_powerset` | Existing proof is logically insufficient: subset into `expand_cde` plus equal size does not imply uniqueness. | Prove an actual injectivity/surjectivity lemma for the M-class action, probably using `descent_psi_effect` as the bit-level action. |
| `check_fact3_true` and `fact3` | Now blocked by the M-class uniqueness/surjectivity gap, not by kernel memory. | Replace the cardinality shortcut with a constructive factorization or injectivity proof. |

Implementation notes:

- Avoid large `by rewrite ... /=` endings in heavy files.
- Avoid unfolding `window_size_fuel` and `has_left_child_fuel` inside large
  downstream proofs.
- Keep old theorem statements available from `psi_cdindex_support.v`, even if
  proofs move.
- Add one new split file at a time and verify it independently.

Gate:

```bash
rocq compile -q -w -deprecated-library-file -w -notation-overridden \
  -R . mathcomp_eulerian psi_cdindex_support.v
```

The gate succeeds only when `psi_cdindex_support.vo` is produced.

## Phase 3: Refactor `perm_seq_bridge.v`

Goal: make the permutation/sequence bridge full-compile once support is opaque.

First retry it unchanged after Phase 2. If it still stalls, split it:

| New file | Contents |
|----------|----------|
| `perm_seq_core.v` | `perm_to_seq`, `seq_to_perm`, round-trip and nth lemmas. |
| `perm_seq_descent.v` | descent bit-vector bridge and `char_mono_perm_to_seq`. |
| `perm_seq_class.v` | M-class helpers and `char_mono_class_inj`. |
| `perm_seq_omega.v` | omega bridge and `omega_proper_beta_lt`. |
| `perm_seq_bridge.v` | Thin compatibility re-export. |

Proof refactor targets:

- `is_descent_perm_seq`;
- `descent_to_bvec_inj`;
- `class_char_monos_uniq`;
- `char_mono_class_inj`;
- `omega_proper_beta_lt`;
- `beta_swap_lt_caseA`.

Gate:

```bash
rocq compile -q -w -deprecated-library-file -w -notation-overridden \
  -R . mathcomp_eulerian perm_seq_bridge.v
```

## Phase 4: Finish `beta_swap.v`

Goal: make the final leaf theorem full-compile.

First retry it unchanged after Phases 2 and 3. If it still stalls, keep the file
small but factor parity/complement reasoning:

| New file | Contents |
|----------|----------|
| `beta_alt_defs.v` | `alt_desc_set`, `set_is_alt`, small parity lemmas. |
| `beta_complement.v` | `compl_perm`, `beta_compl`, complement descent lemmas. |
| `beta_alt_max.v` | `omega_set_alt_full`, `not_set_is_alt_omega_not_full`, `beta_alt_max`. |
| `beta_swap.v` | Thin compatibility re-export. |

Gate:

```bash
rocq compile -q -w -deprecated-library-file -w -notation-overridden \
  -R . mathcomp_eulerian beta_swap.v
```

## Phase 5: Build and CI Cleanup

Goal: make regressions obvious.

Tasks:

1. Update `_CoqProject` to list every maintained `.v` file.
2. Keep the topological order explicit.
3. Add documented build commands to `README.md`:

```bash
make clean
make vos -j2
make -j1
```

4. Add a no-axioms/no-admits check for maintained files:

```bash
rg -n "\b(Axiom|Parameter|Conjecture|Admitted|admit)\b" *.v
```

5. Run `coqchk` on the final maintained library set.

Gate:

- `make clean && make -j1` succeeds.
- `make vos -j2` succeeds.
- `coqchk` succeeds for the maintained library.
- No stale monolith remains as a non-building `.v` file.

## Risks

1. `psi_cdindex_support.v` may still hit a kernel proof-term wall after simple
   splitting.
   If so, the project needs a deeper representation change or must accept a
   `.vos` workflow for that theorem layer.
2. Replacing monoliths with wrappers may remove private lemma names that no
   current file imports but a user may rely on interactively.
   Mitigation: use `rg "Require Import psi"` and `rg "Require Import psi_base"`
   before deleting names.
3. `psi_descent_wf.v` can make the phrase "all files compile" misleading
   because it compiles with `Admitted`.
   Mitigation: archive it or explicitly classify it as a prototype target.
4. Full `.vo` success may depend on machine memory.
   Mitigation: measure one holdout at a time with `-time-file`, and keep a
   documented `.vos` fallback if the kernel wall persists.

## Immediate Next Actions

1. Prove the missing M-class action lemma needed by
   `uniq_map_char_mono_powerset`.
2. Prefer a statement that characterizes `char_mono (apply_psis ss w)` as the
   result of independent C-toggles and D-swaps over `phi_w w`, using
   `descent_psi_effect`.
3. Once `check_fact3_true` full-compiles, retry:

```bash
rocq compile -q -w -deprecated-library-file -w -notation-overridden \
  -R . mathcomp_eulerian psi_cdindex_support.v
```

## Next-Session Handoff

This is the most important section if continuing from a fresh session.

### Files Changed In This Refactor

- `_CoqProject`
  - Now lists all maintained `.v` files.
  - Added `psi_cdindex_support_defs.v` before `psi_cdindex_support.v`.
  - Added `psi_descent.v` as a compatibility wrapper.
- `psi_descent.v`
  - Replaced old monolithic body with:

```coq
From mathcomp Require Import all_ssreflect.
Require Export psi_descent_v2 psi_descent_thms.
```

- `archive/psi.v.txt`
  - Archived stale monolith previously named `psi.v`.
- `archive/psi_base.v.txt`
  - Archived stale monolith previously named `psi_base.v`.
- `archive/psi_descent_wf.v.txt`
  - Archived prototype previously named `psi_descent_wf.v`.
- `psi_cdindex_support_defs.v`
  - New file. Full `.vo` compile succeeds.
  - Contains:
    - `cde_width`;
    - `cde_total_width`;
    - `cde_offset`;
    - `D_offsets`;
    - `has_transition`;
    - `all_D_transitions`;
    - `size_in_expand_cde`;
    - `expand_cde_mem_transitions`;
    - `transitions_expand_cde_mem`;
    - `expand_cde_mem_iff`;
    - `has_transition_omega_seq`;
    - `cde_total_width_cat`.
- `psi_cdindex_support.v`
  - Imports/re-exports `psi_cdindex_support_defs`.
  - No longer contains the cd-width/D-offset basic definitions.
  - `D_vertex_descent_transition` was reduced to a small corollary of
    `exactly_one_descent_LR`.

### Commands Already Verified

These passed after the current refactor:

```bash
rocq compile -q -w -deprecated-library-file -w -notation-overridden \
  -R . mathcomp_eulerian psi_descent.v

rocq compile -q -w -deprecated-library-file -w -notation-overridden \
  -R . mathcomp_eulerian psi_cdindex_support_defs.v

rocq compile -vos -q -w -deprecated-library-file -w -notation-overridden \
  -R . mathcomp_eulerian psi_cdindex_support.v

make -B vos -j2

rg -n "\b(Axiom|Parameter|Conjecture|Admitted|admit)\b" *.v
```

The last command has no matches among maintained `.v` files.

### Current Full-Compile Failure

Run:

```bash
rocq compile -q -w -deprecated-library-file -w -notation-overridden \
  -R . mathcomp_eulerian psi_cdindex_support.v
```

Expected current failure:

```text
File "./psi_cdindex_support.v", line around uniq_map_char_mono_powerset:
The term "Hdup" has type "is_true (size (undup lhs) < size lhs)"
while it is expected to have type ...
```

The exact line number may drift, but the failing lemma is:

```coq
Lemma uniq_map_char_mono_powerset w :
  uniq w -> 2 <= size w ->
  uniq [seq char_mono (apply_psis ss w) | ss <- powerset_internal w].
```

### Why The Current Proof Is Wrong

The current proof establishes:

```coq
set lhs := [seq char_mono (apply_psis ss w) | ss <- powerset_internal w].
set rhs := expand_cde (phi_w w).

Hmem : {subset lhs <= rhs}
Hsz_lhs : size lhs = size rhs
Huniq_rhs : uniq rhs
```

Then it tries to prove `uniq lhs`.

This is not valid. A list can have duplicates, have the same length as a unique
list, and still be a subset of that unique list. Example:

```text
lhs = [a; a]
rhs = [a; b]
```

So do not repair this with arithmetic gymnastics. The proof needs one of:

- actual injectivity of the map
  `ss ↦ char_mono (apply_psis ss w)` over `powerset_internal w`;
- or actual surjectivity plus a no-duplicates argument;
- or a constructive factorization proof of Fact #3.

### Best Next Lemma Targets

Start with one of these; the first is probably the cleanest.

#### Option A: Prove Injectivity Directly

Target shape:

```coq
Lemma char_mono_apply_psis_inj w ss1 ss2 :
  uniq w -> 2 <= size w ->
  ss1 \in powerset_internal w ->
  ss2 \in powerset_internal w ->
  char_mono (apply_psis ss1 w) =
  char_mono (apply_psis ss2 w) ->
  ss1 = ss2.
```

Then:

```coq
Lemma uniq_map_char_mono_powerset w :
  uniq w -> 2 <= size w ->
  uniq [seq char_mono (apply_psis ss w) | ss <- powerset_internal w].
Proof.
move=> Hu Hsz2.
apply: map_inj_in_uniq.
- move=> ss1 ss2 Hss1 Hss2.
  exact: char_mono_apply_psis_inj Hu Hsz2 Hss1 Hss2.
- (* prove powerset_internal w is uniq, likely by a separate lemma *)
Qed.
```

This also needs:

```coq
Lemma uniq_powerset_internal w : uniq (powerset_internal w).
```

That lemma should be independent of the psi/cd-index mathematics and can be
proved by induction over `internal_vertices w`, or more generally over a list
of vertices.

#### Option B: Prove Surjectivity Onto `expand_cde`

Target shape:

```coq
Lemma expand_cde_char_mono_surj w X :
  uniq w -> 2 <= size w ->
  X \in expand_cde (phi_w w) ->
  exists ss,
    ss \in powerset_internal w /\
    char_mono (apply_psis ss w) = X.
```

Together with the already-proved membership:

```coq
Lemma char_mono_apply_psis_mem w ss :
  uniq w -> 2 <= size w ->
  char_mono (apply_psis ss w) \in expand_cde (phi_w w).
```

and size equality, this can prove `perm_eq lhs rhs`. But note: surjectivity
alone still does not prove `uniq lhs`; use it directly for `fact3`, or combine
it with injectivity.

#### Option C: Bit-Level Action Lemma

This is probably the mathematical heart. Use `descent_psi_effect` from
`psi_cdindex_core.v`.

Possible target:

```coq
Lemma char_mono_psi_effect v w :
  uniq w -> is_internal v w ->
  char_mono (psi v w) =
  (* char_mono w with one C-toggle if ~~ has_left_child v w,
     or adjacent D-swap/toggle pattern if has_left_child v w *).
```

More explicitly:

- If `~~ has_left_child v w`, `psi v` toggles descent bit `v`.
- If `has_left_child v w`, `psi v` swaps descent bits `v.-1` and `v`.

This mirrors the already-proved theorem:

```coq
Lemma descent_psi_effect v w k :
  uniq w -> is_internal v w -> k < (size w).-1 ->
  is_descent_seq (psi v w) k =
    if ~~ has_left_child v w then
      if k == v then ~~ is_descent_seq w v
      else is_descent_seq w k
    else
      if k == v then is_descent_seq w v.-1
      else if k == v.-1 then is_descent_seq w v
      else is_descent_seq w k.
```

The action lemma should let us show that every internal vertex acts
nontrivially on a distinct coordinate or adjacent-pair coordinate of the
`expand_cde (phi_w w)` word. That is the missing reason why the M-class
monomials are unique.

### Known Helpful Existing Lemmas

Use these before inventing new machinery:

- `descent_psi_effect` in `psi_cdindex_core.v`.
- `phi_w_support_general` in `psi_cdindex_support.v`.
- `D_offsets_phi_w_eq_S_w_seq` in `psi_cdindex_support.v`.
- `S_w_seq_bound` in `psi_cdindex_support.v`.
- `char_mono_self_mem` in `psi_cdindex_support.v`.
- `char_mono_apply_psis_mem` in `psi_cdindex_support.v`.
- `size_powerset_internal` in `psi_cdindex_core.v`.
- `size_expand_cde_phi_w` in `psi_cdindex_core.v`.
- `apply_psis_cancel`, `apply_psis_revK`, `powerset_internal_apply_psis` in
  `perm_seq_bridge.v` may be useful later, but beware importing
  `perm_seq_bridge.v` into `psi_cdindex_support.v` would create a dependency
  cycle. If needed, move small generic action lemmas upstream into a new file.

### Dependency Warning

Do not import `perm_seq_bridge.v` into `psi_cdindex_support.v`.

Current order is:

```text
psi_cdindex_support -> perm_seq_bridge -> beta_swap
```

So any M-class helper needed by both support and bridge must live before
`psi_cdindex_support.v`, for example in a new file between
`psi_cdindex_witness.v` and `psi_cdindex_support.v`.

### Practical Next Steps

1. First prove `uniq_powerset_internal` in a dependency-light place.
   Candidate location: `psi_cdindex_core.v` near `size_powerset_internal`, or a
   new file before `psi_cdindex_support.v`.
2. Then try `char_mono_apply_psis_inj`.
3. If direct injectivity is too hard, prove the bit-level `char_mono_psi_effect`
   and use it to derive injectivity.
4. Replace the body of `uniq_map_char_mono_powerset`; do not keep the current
   subset/cardinality shortcut.
5. Re-run full compilation of `psi_cdindex_support.v`.
