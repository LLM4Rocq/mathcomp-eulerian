> **Historical document.** The May 2026 plan that actually finished the
> project: every phase is complete, every result is `.vo` and
> kernel-checked.  Kept here as the canonical record of the path that
> worked.  See [`README.md`](README.md) for the full chronology.

# Compile-All Refactor Plan

Snapshot date: 2026-05-01.
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

- `make vos -j2` succeeds for the active `_CoqProject` target.
- `make -j2` (full `.vo`) produces **all 23 `.vo` files**. The full
  `make clean && make -j2` build runs end-to-end through `beta_swap.v`.
- `psi_cdindex_support.v` now full-compiles. The M-class injectivity gap is
  closed: see commit `35a1bd0`. Bit-level recovery lemmas in
  `psi_cdindex_core.v` (`char_mono_apply_psis_C_bit`,
  `char_mono_apply_psis_D_bit_pred`, `char_mono_apply_psis_D_bit_self`) read
  off `(v \in ss)` from the char_mono of `apply_psis ss w`. Disjointness of
  the bit positions owned by distinct internal vertices follows from
  `LR_pred_is_endpoint` (D-vertex predecessors are non-internal).
  `char_mono_apply_psis_inj` and the new `uniq_map_char_mono_powerset` use
  `subseq_uniqP` on `internal_vertices w` to conclude `ss1 = ss2`.
- `psi_cdindex_support_defs.v` is split out and full-compiles quickly.
- The previous `.vo` wall in `D_vertex_descent_transition` has been removed:
  that lemma is now a small corollary of `exactly_one_descent_LR`.
- No `.vo` holdouts remain. `perm_seq_bridge.v` and `beta_swap.v` both
  full-compile.
- `psi_descent.v` is a compatibility wrapper exporting `psi_descent_v2.v`
  and `psi_descent_thms.v`; it full-compiles quickly.
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

Status: **complete** (commit `35a1bd0`).

Goal achieved: `psi_cdindex_support.v` full-compiles to `.vo`. The split
into `psi_cdindex_support_defs.v` plus a real injectivity proof closed
the M-class uniqueness gap. The further file split listed in earlier
drafts of this plan was *not* needed once the proof gap was closed.

Architecture of the proof now in tree:

- `psi_cdindex_core.v` adds bit-level recovery primitives:
  - `is_internal_lt v w : is_internal v w -> v < (size w).-1`.
  - `char_mono_psi_effect` lifts `descent_psi_effect` from
    `is_descent_seq` to `nth false (char_mono ...)`.
  - `uniq_powerset_of` / `uniq_powerset_internal` — subsets are uniq.
  - `subset_powerset_of` / `subseq_powerset_of` (and `_internal`
    variants) — every element of `powerset_internal w` is a subseq of
    `internal_vertices w`.
  - `char_mono_apply_psis_C_bit ss w v` — for a C-vertex `v`, bit `v`
    of `char_mono (apply_psis ss w)` equals
    `is_descent_seq w v (+) (v \in ss)`.
  - `char_mono_apply_psis_D_bit_pred` / `_D_bit_self` — for a D-vertex
    `v`, the pair `(bit v.-1, bit v)` is swapped iff `v \in ss`.
- `psi_cdindex_support.v` then proves:
  - `in_internal_vertices i w : (i \in internal_vertices w) = is_internal i w`.
  - `char_mono_apply_psis_inj` — recovers `(x \in ss)` from the bits at
    `x` (or at `x.-1, x` for D-vertices, using
    `D_vertex_descent_transition` to disambiguate); concludes
    `ss1 = ss2` via `subseq_uniqP` against `internal_vertices w`.
  - `uniq_map_char_mono_powerset` — now `map_inj_in_uniq` plus the
    above injectivity plus `uniq_powerset_internal`.

Why disjointness of "owned" bit positions holds: a D-vertex `v` has
`v.-1` non-internal (`LR_pred_is_endpoint`), so no other internal vertex
acts on positions `{v.-1, v}`. Each internal vertex independently
controls its bit pattern of `char_mono (apply_psis ss w)`.

Gate (passes):

```bash
rocq compile -q -w -deprecated-library-file -w -notation-overridden \
  -R . mathcomp_eulerian psi_cdindex_support.v
```

## Phase 3: Fix `perm_seq_bridge.v`

Status: **complete**.

Diagnosis change from earlier drafts: the file does *not* hit a kernel
proof-term wall after Phase 2. Compilation was blocked by a series of
mathcomp-version compatibility mismatches (signature drift). No file
split was required — lemma-by-lemma compat fixes drove the file to
`.vo`.

### Fixes already applied in `b39f109`

| Lemma | Change |
|-------|--------|
| `nth_perm_to_seq` | `nth_enum_ord` now returns `:> nat`, not ordinal equality. Wrap with `apply: val_inj => /=` before `rewrite nth_enum_ord`. |
| `perm_to_seq_inj` | `Ordinal Hi = i` is no longer definitional; introduce explicit `have Hord : Ordinal Hi = i by apply: val_inj` and rewrite. |
| `is_descent_perm_seq` | For `i : 'I_n`, `ltn_ord i` no longer auto-coerces to `val i < n.+1`; use `leq_trans (ltn_ord i) (leqnSn n)`. The trailing `by rewrite /bump /= add1n` simplification is unnecessary now (`by []` closes). |
| `nth_descent_to_bvec` | Same `val_inj => /=` pattern as `nth_perm_to_seq`. |
| `char_mono_perm_to_seq` | Use `have -> : nth (Ordinal Hk) (enum 'I_n) k = Ordinal Hk` via `val_inj`. Closing line is now `by symmetry; exact: is_descent_perm_seq`. |
| `descent_to_bvec_inj` | Same `Hord : Ordinal Hi = i` pattern; rewrite Hord into the equation, then `move=> ->`. |
| `psi_apply_psis_comm` | `psi_comm` now has explicit `i j` args; use `(psi_comm j i Hu)`. |
| `apply_psis_revK` | Reorder: `rewrite IH; last exact: uniq_psi.` then `exact: psi_involutive`. (Old order had `psi_involutive` first which no longer matches.) |
| `apply_psis_cancel` | `rewrite -{1}(apply_psis_rev ss (uniq_apply_psis ss Hu))` then `exact: apply_psis_revK`. (Old `rewrite -(apply_psis_revK ss Hu)` substituted `w` everywhere and cascaded.) |
| `char_mono_class_inj` | Two issues: (1) `rewrite (nth_map [::]) //` does not auto-discharge the index_mem goal — split into `rewrite (nth_map [::]); last by rewrite index_mem` with a separate `rewrite -Hn1`. (2) After `rewrite Hcm_idx eqxx`, the equation is `true = (idx1 == idx2)`; use `=> /esym/eqP Heq_idx` instead of `=> /eqP Heq_idx`. |
| `desc_positions_bvec` (partial) | `leq_anti` renamed to `anti_leq`. `sorted_filter` now needs `leq_trans` explicitly. `sort_sorted` is now curried with `leq_total` — needs `apply: sort_sorted; exact: leq_total` after unfolding `set_to_seq`. |

### Additional fixes applied to drive to `.vo`

| Lemma | Change |
|-------|--------|
| `desc_positions_bvec` | Wrapped third `sorted_eq` subgoal with `apply: uniq_perm`. Body rewritten to use `nth_descent_to_bvec` directly (the original `mem_enum`-based proof was structurally wrong anyway). |
| `perm_to_seq_seq_to_perm` | After `(nth_map (Ordinal Hk))`, `nth_enum_ord` no longer substitutes the ordinal directly. Insert `have Hord : nth (Ordinal Hk) (enum 'I_n) k = Ordinal Hk by apply: val_inj => /=; rewrite nth_enum_ord` then `rewrite Hord`. |
| `all_bnd_apply_psis` | `rewrite (perm_mem (perm_eq_apply_psis ss w))` was wrong direction (`perm_eq_apply_psis : perm_eq (apply_psis ss w) w`); use `rewrite -(perm_mem ...)`. |
| `uniq_expand_cde` | `cat_uniq` is now flat `[&& A, B & C]`, so `?andbT` no longer fires on the IH residue. Insert explicit `rewrite IH andbT` after `!map_inj_uniq //`. |
| `nil_in_powerset_internal` | `mem_seq1` LHS unification needed an explicit type annotation: `[::] \in [:: [::] : seq nat]`. |
| `char_mono_in_expand_cde` | `apply/mapP; exists [::] => //. ... by rewrite apply_psis_nil` failed because `=> //` now eats the `apply_psis [::] w = w` subgoal. Restructure to `exists [::]; first exact: nil_in_powerset_internal. by rewrite apply_psis_nil`. |
| `find_ss_spec` | `set flt` does not fold inside earlier hypotheses; add `have Hfilter' : ss \in flt by rewrite /flt` before using. `mem_head` lost its `s != [::]` hypothesis form: case-split on `flt` to obtain `head [::] flt \in flt`. |
| `omega_set_seq_bridge_bounded` | The lemma equation now goes `lhs = rhs` opposite of what `exact:` expected; use `rewrite` instead of `exact:`. |
| `S_w_seq_all_lt` | `(size w).-2 = size w - 2` no longer auto-discharges via `case ... //`; needs `case: (size w) => [\|[\|n']] //=; rewrite !subSS subn0`. `leq_subRL` direction flipped — needed an explicit `Hisz' : i <= size w` derived from `H2si : 2 <= size w - i` via `subn_gt0`. |
| `omega_proper_beta_lt` (Step 1) | After `phi_w_support_general` rewrite, the goal had `(size (perm_to_seq sigma)).-1` whereas surrounding lemmas used `m.+1`; insert `have Hrew : (size (perm_to_seq sigma)).-1 = m.+1` and rewrite via `[X in iota 0 X]Hrew` to avoid breaking the surrounding `'I_m.+2` types. Same for the `bvE` direction with explicit hyp args to `phi_w_support_general`. |
| `omega_proper_beta_lt` (Step 3) | `apply: char_mono_class_inj Hss1_pw Hss2_pw _` now leaves an extra `uniq w'` goal; replace with `apply: (char_mono_class_inj Hu' Hss1_pw Hss2_pw)`. The second `Hss2_pw` rewrite needed `-Hw'` first to align `w'` with `apply_psis ss2 w2` for `powerset_internal_apply_psis` to fire. |
| `omega_proper_beta_lt` (Step 3 closing) | `rewrite /w1 /w2 Hw12` lost the alias visibility after unfold; replace with `exact: Hw12`. |
| `omega_proper_beta_lt` (Step 4) | Same `(size w0).-1` vs `m.+1` mismatch in `bvE_in_w0` / `bvD_notin_w0`. Same `[X in iota 0 X]`-pattern fix. Closing the omega-set step needs an explicit `have -> : Ordinal Hkm = k by apply: val_inj` to bridge `Ordinal Hkm` (rebuilt) and `k` (original). |
| `omega_proper_beta_lt` (`Hnotin`) | The `have := img_has_bvD sigma_new. rewrite Heq => Habs.` flow no longer applies cleanly; restructure to first establish `Hsigma_in : sigma_new \in [set f tau' | ...]`, then `Habs := img_has_bvD sigma_new Hsigma_in`. |
| `omega_proper_beta_lt` (`Hproper`) | `by move: Hx; rewrite (subsetP img_sub).` no longer types — `subsetP` returns a function, not a rewrite. Use `exact: (subsetP img_sub _ Hx)`. `cardsD1` rewrite needed pattern restriction `[X in _ < X](cardsD1 sigma_new)` followed by `Hin_E ltnS leqnn`. Final `rewrite /beta -card_img` simplified to just `-card_img` (unfolding `beta` removes the rewrite target). |
| Local `Horder_iso` | `index_inj` lost its `uniq` arg. Switched `map_inj_uniq` to `map_inj_in_uniq` and rebuilt the `sp < sq ↔ index sp < index sq` equivalence inline using `sorted_leq_index` (only one direction is in mathcomp now). The `!(nth_map 0) ?Hsz0 //` side-condition discharge had to be rewritten as `!(nth_map 0) //; try by rewrite -Hsz0; first [exact: Hp \| exact: Hq]`. |
| `phi_w_order_iso` and `HS_w0` | `window_size_order_iso` and `has_left_child_order_iso` take `i` as the explicit first arg before the size/uniq/order proofs (they were being called with the proofs in the `i`-position). |

### Imports & dependencies — DO NOT do

- Do **not** import `perm_seq_bridge.v` into `psi_cdindex_support.v`
  (would create a cycle; the topology is `psi_cdindex_support
  -> perm_seq_bridge -> beta_swap`).
- Do **not** split this file unless an *actual* kernel wall reappears
  after the compat fixes. The earlier draft of this plan recommended a
  five-way split; that recommendation is superseded.

Gate:

```bash
rocq compile -q -w -deprecated-library-file -w -notation-overridden \
  -R . mathcomp_eulerian perm_seq_bridge.v
```

## Phase 4: Finish `beta_swap.v`

Status: **complete**. Once `perm_seq_bridge.vo` was produced, `beta_swap.v`
full-compiled with no further changes. No kernel wall reappeared, no
file split was needed.

If a kernel wall *does* reappear in future drift:

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

Status: **complete**.

Verified gates:

- `make clean && make -j2` succeeds — all 23 maintained `.v` files
  build to `.vo`.
- `make vos -j2` succeeds.
- `coqchk -R . mathcomp_eulerian mathcomp_eulerian.beta_swap` reports
  "Modules were successfully checked".
- `rg "\b(Axiom|Parameter|Conjecture|Admitted|admit)\b" *.v` returns
  no matches in maintained files.
- `Print Assumptions beta_alt_max` and `omega_proper_beta_lt` both
  report "Closed under the global context".

Optional remaining doc work: update `README.md` to include the
documented build commands.

## Risks

1. ~~`psi_cdindex_support.v` may still hit a kernel proof-term wall.~~
   Resolved: the support file full-compiles after the bit-level recovery
   refactor.
2. Replacing monoliths with wrappers may remove private lemma names that no
   current file imports but a user may rely on interactively.
   Mitigation: use `rg "Require Import psi"` and `rg "Require Import psi_base"`
   before deleting names.
3. `psi_descent_wf.v` can make the phrase "all files compile" misleading
   because it compiles with `Admitted`. Archived under
   `archive/psi_descent_wf.v.txt`; not in `_CoqProject`.
4. Full `.vo` success may depend on machine memory.
   Mitigation: measure one holdout at a time with `-time-file`, and keep a
   documented `.vos` fallback if a kernel wall reappears in Phases 3/4.
5. mathcomp signature drift surfaced lemma-by-lemma in
   `perm_seq_bridge.v`; resolved by iterating on the gate and
   applying the patterns documented in Phase 3. `beta_swap.v` did
   not exhibit further drift on top of `perm_seq_bridge.vo`.

## Immediate Next Actions

All compile-all phases are done. Remaining nice-to-haves:

1. Optionally update `README.md` with the documented build commands
   from Phase 5.
2. Optionally clean up the stray `.lia.cache` deletion that surfaced
   during the M-class work (or add it to `.gitignore`).

## Next-Session Handoff

This is the most important section if continuing from a fresh session.

### What is done

| Phase | Status | Key commit |
|-------|--------|------------|
| Phase 0 — freeze and measure | done | n/a |
| Phase 1 — archive monoliths, wrap `psi_descent.v` | done | `01c7858` |
| Phase 2 — `psi_cdindex_support.v` full-compiles | done | `35a1bd0` |
| Phase 3 — `perm_seq_bridge.v` full-compile | done | (this session, on top of `b39f109`) |
| Phase 4 — `beta_swap.v` full-compile | done | (no source changes — built once `perm_seq_bridge.vo` was produced) |
| Phase 5 — CI cleanup | done | (this session) |

`make vos -j2` passes. `make clean && make -j2` produces all 23 `.vo`
files. `coqchk -R . mathcomp_eulerian mathcomp_eulerian.beta_swap`
passes. `Print Assumptions beta_alt_max` and `omega_proper_beta_lt`
both report "Closed under the global context".

### Files changed (cumulative across all commits)

- `_CoqProject` — lists all 23 maintained files in topological order;
  added `psi_cdindex_support_defs.v` and `psi_descent.v` (as wrapper).
- `psi_descent.v` — compatibility wrapper:

  ```coq
  From mathcomp Require Import all_ssreflect.
  Require Export psi_descent_v2 psi_descent_thms.
  ```

- `archive/psi.v.txt`, `archive/psi_base.v.txt`,
  `archive/psi_descent_wf.v.txt` — historical sources off the build surface.
- `psi_cdindex_support_defs.v` — new file holding `cde_width`,
  `cde_total_width`, `cde_offset`, `D_offsets`, `has_transition`,
  `all_D_transitions`, `size_in_expand_cde`, `expand_cde_mem_transitions`,
  `transitions_expand_cde_mem`, `expand_cde_mem_iff`,
  `has_transition_omega_seq`, `cde_total_width_cat`. Full `.vo` compile.
- `psi_cdindex_core.v` — new lemmas for the M-class proof:
  - `is_internal_lt`,
  - `char_mono_psi_effect`,
  - `uniq_powerset_of`, `uniq_powerset_internal`,
  - `subset_powerset_of`, `subset_powerset_internal`,
  - `subseq_powerset_of`, `subseq_powerset_internal`,
  - `char_mono_apply_psis_C_bit`,
  - `char_mono_apply_psis_D_bit_pred`,
  - `char_mono_apply_psis_D_bit_self`.
- `psi_cdindex_support.v`:
  - Re-exports `psi_cdindex_support_defs`.
  - `D_vertex_descent_transition` is now a small corollary of
    `exactly_one_descent_LR`.
  - New: `in_internal_vertices`, `char_mono_apply_psis_inj`.
  - `uniq_map_char_mono_powerset` rewritten as
    `map_inj_in_uniq` + `uniq_powerset_internal`.
- `perm_seq_bridge.v` — full mathcomp-compat fixes (see Phase 3
  table above). Drives end-to-end to `.vo`; the closing lemma
  `omega_proper_beta_lt` is closed under the global context.
- `beta_swap.v` — unchanged source; full-compiles once
  `perm_seq_bridge.vo` is built. `beta_alt_max` is closed under the
  global context.

### Verified commands (current tree)

```bash
make clean && make -j2
# OK — all 23 maintained files at .vo.

rg -n "\b(Axiom|Parameter|Conjecture|Admitted|admit)\b" *.v
# No matches in maintained files.

coqchk -R . mathcomp_eulerian mathcomp_eulerian.beta_swap
# Modules were successfully checked.

echo 'From mathcomp_eulerian Require Import beta_swap. \
      Print Assumptions beta_alt_max.' \
  | rocq top -R . mathcomp_eulerian
# Closed under the global context.
```

### Imports & cycle-prevention

The strict topological order is:

```text
mmtree -> psi_core -> psi_comm -> psi_descent_v2 -> psi_descent_thms
      -> psi_cdindex_defs -> psi_cdindex_tree_shape
      -> psi_cdindex_tree_hlc -> psi_cdindex_tree
      -> psi_cdindex_core -> psi_cdindex_witness
      -> psi_cdindex_support_defs -> psi_cdindex_support
      -> perm_seq_bridge -> beta_swap
```

- Do not `Require Import perm_seq_bridge` from anything upstream of it.
- Any M-class helper needed by both `psi_cdindex_support` and
  `perm_seq_bridge` must live in `psi_cdindex_core` or earlier.

### Known helpful existing lemmas (for future work)

For Phase 3 / 4, search for these before inventing new machinery:

- `descent_psi_effect`, `char_mono_psi_effect`,
  `char_mono_apply_psis_{C_bit,D_bit_pred,D_bit_self}`,
  `uniq_powerset_internal`, `subseq_powerset_internal` —
  in `psi_cdindex_core.v`.
- `D_vertex_descent_transition`, `phi_w_support_general`,
  `D_offsets_phi_w_eq_S_w_seq`, `S_w_seq_bound`, `char_mono_self_mem`,
  `char_mono_apply_psis_mem`, `char_mono_apply_psis_inj`,
  `uniq_map_char_mono_powerset`, `check_fact3_true`, `fact3` —
  in `psi_cdindex_support.v`.
- `apply_psis_cancel`, `apply_psis_revK`,
  `powerset_internal_apply_psis` — in `perm_seq_bridge.v`.

### Practical next steps

The compile-all goal is achieved. Optional follow-ups:

1. Update `README.md` with the documented build commands above.
2. Clean up the stray `.lia.cache` deletion (or add it to `.gitignore`).
3. Consider regenerating `Makefile.coq` on first build automatically
   (the committed one had a stale macOS opam path; the pattern
   `rm -f Makefile.coq Makefile.coq.conf .Makefile.coq.d` clears it).
