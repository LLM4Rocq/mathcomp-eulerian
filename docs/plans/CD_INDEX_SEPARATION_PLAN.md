# Plan: separate the cd-index (§1.6.3) closure from the §1.4 closure

> **Forward-looking refactor plan.** Goal: make it possible to build a
> §1.4-only target (descents, Eulerian numbers, Foata, q-Eulerian) without
> compiling any of the cd-index machinery (`psi_*.v`).
>
> Motivation: today, `foata.v` → `perm_seq_bridge.v` → `psi_*.v` is a
> transitive dependency chain even though `foata` is pure §1.4 content
> and needs nothing from the cd-index theory.

## 1. The problem in one diagram

Current `Require` graph (project-local edges only, §1.4 leaves on the left):

```
descent ──┬──> eulerian ──┬──> beta ──> beta_omega ──> beta_bridge ──┐
          │               └──> qfact ──> qeul                          │
          ├──> inversions ──> foata ──> qfact, qeul                    │
          │                     ▲                                       │
          │                     └──── perm_seq_bridge ◄─────── psi_* (cd-index)
          └──> cycles ──> cycles_rec ──> stirling_fiber
```

`perm_seq_bridge.v` does two unrelated jobs in one file:

1. **Perm↔seq plumbing** (§1.4 ingredient) — used by `foata.v`.
2. **Proof of Prop 1.6.4** (§1.6.3) — uses `psi_core`, `psi_comm`,
   `psi_descent_v2`, `psi_descent_thms`, `psi_cdindex_core`,
   `psi_cdindex_witness`, `psi_cdindex_support`.

Because they live together, anything that needs (1) transitively pulls
in (2) and the entire cd-index closure.

## 2. Target graph

```
perm_seq_basics  (new, no psi)
       ▲
       │
foata, qfact, qeul, ...    perm_seq_cdindex  (was: perm_seq_bridge)
                                  ▲
                                  │
                             psi_*  + beta_bridge + beta_swap + altsub + ...
```

After the split, the §1.4 closure has zero `Require` paths into `psi_*`.

## 3. Concrete split of `perm_seq_bridge.v`

Source today: 1,139 LOC, 45 declarations.

### 3a. Move to `perm_seq_basics.v` (no `Require Import mmtree psi_*`)

Pure perm↔seq machinery. Estimated ~500–600 LOC. Lemmas (verify by
`grep` in `foata.v` that none of these reference psi-only symbols):

- Section "SA. perm_to_seq":
  - `perm_to_seq_size`, `perm_to_seq_uniq`, `nth_perm_to_seq`
  - `perm_to_seq_inj`
- `is_descent_perm_seq`, `size_descent_to_bvec`, `nth_descent_to_bvec`
- `descent_to_bvec_inj`
- `char_mono_perm_to_seq` *(check: does this reference `psi_core.char_mono`?
  if yes, either move `char_mono`'s definition out of psi-land into
  `perm_seq_basics`, or keep the lemma in `perm_seq_cdindex`)*
- Section `SeqToPerm`:
  - `seq_nth_bound`, `seq_to_fun_inj`
  - `perm_to_seq_bnd`
  - `perm_to_seq_seq_to_perm`
- `desc_positions_bvec`

(The lemmas `seq_to_perm_nth` and `seq_to_perm_perm_to_seq`, originally
listed here, were removed during the post-refactor dead-code audit
because nothing referenced them.)

### 3b. Keep in `perm_seq_bridge.v` (rename → `perm_seq_cdindex.v`?)

Everything that touches `psi_*`. Estimated ~500–600 LOC. Lemmas:

- `psi_apply_psis_comm`, `apply_psis_rev`, `apply_psis_revK`,
  `apply_psis_cancel`
- `powerset_internal_apply_psis`
- `class_char_monos_uniq`, `char_mono_class_inj`
- `all_bnd_apply_psis`, `apply_psis_size_eq`
- `uniq_expand_cde`, `nil_in_powerset_internal`, `char_mono_in_expand_cde`
- `find_ss_spec`
- The final headline result `omega_proper_beta_lt` (Stanley Prop 1.6.4).
  (`beta_swap_lt_caseA`, originally listed here as a derivation, was
  removed during the post-refactor dead-code audit because nothing
  referenced it.)

## 4. Mechanical steps

1. `cp perm_seq_bridge.v perm_seq_basics.v` and delete the
   psi-dependent lemmas from `perm_seq_basics.v`. Drop the
   `Require Import mmtree psi_*` lines.
2. From `perm_seq_bridge.v`, delete everything moved to
   `perm_seq_basics.v` and add `From mathcomp_eulerian Require Import
   perm_seq_basics.`
3. Update `_CoqProject` to include `perm_seq_basics.v`.
4. Update imports in `foata.v` (and anywhere else that today imports
   `perm_seq_bridge` but only needs the perm↔seq plumbing): replace
   `perm_seq_bridge` with `perm_seq_basics`.
5. `make clean && make -jN`. Iterate on missing lemmas: if a §1.4 file
   needs something currently in the cd-index half, decide whether to
   (a) move it to basics, or (b) prove a basics-only variant.

## 5. Verification

Two builds:

```bash
# Full build (unchanged result)
make clean && make -jN

# §1.4-only build: remove psi_* + cd-index half + downstream
mv psi_*.v mmtree.v perm_seq_bridge.v beta_bridge.v beta_swap.v altsub.v /tmp/
# (also check beta_omega.v — split if it has §1.6.3 content)
make clean && make -jN
```

If step 2 succeeds, count SLOC of what remains. Expected: ~7–8k SLOC for
the §1.4 closure. Restore from `/tmp/` after measuring.

## 6. Risks / gotchas

- **`char_mono` location.** The descent pattern of a permutation
  (`char_mono`) is currently defined in `psi_core.v`. `foata.v` and the
  perm↔seq plumbing use it. Two options:
  (a) Define `char_mono` in `descent.v` or a new `char_mono.v`, and have
      `psi_core` import that.
  (b) Keep `char_mono` in psi land and accept that anything mentioning it
      lives in the cd-index closure. This may force `is_descent_perm_seq`
      etc. into `perm_seq_cdindex` if they're stated in terms of
      `char_mono`.
  Check first which lemmas in §3a actually mention `char_mono`. If many,
  option (a) is the right move and `psi_core.v` shrinks.
- **`beta_swap.v`, `altsub.v` are deep cd-index territory.** Stanley
  §1.6.3 Cor 1.6.5 proofs (`altsub.v`, 1,418 LOC) and the alt-swap
  inequalities (`beta_swap.v`, 213 LOC) belong on the §1.6.3 side.
  Confirm by checking they `Require Import` only `beta`, `beta_omega`,
  `beta_bridge`, and `psi_*` content.
- **`beta_omega.v`** may straddle. It defines the omega map (used by
  Cor 1.6.5 statement) but also by Prop 1.6.4 (cd-index). If it contains
  only definitions + basic lemmas (no `psi_*` dependency), keep it in
  §1.4 closure. Otherwise split.
- **`mmtree.v`** is the min-max tree datatype (§1.6.3 native). Goes on
  the cd-index side.

## 7. Estimated outcome

| Target | Files | SLOC |
|---|---:|---:|
| Today (everything) | 31 | ~13,300 |
| §1.4 only (post-split) | ~14 | ~7,000–8,000 |
| §1.6.3 cd-index closure (deleted in §1.4 build) | ~17 | ~5,500–6,500 |

If the split is clean, the §1.4-only ratio becomes roughly 7.5k SLOC / 7
informal pages ≈ **~1,000 SLOC/page**, slightly worse than today's
overall 739/page — confirming that the cd-index work, despite being
~7k LOC, *amortizes* well across the full Stanley §§1.4 + 1.6 informal
scope.

## 8. What this does *not* do

- Does not remove or simplify any cd-index proof; only re-files them.
- Does not change any theorem statement or proof. Only `Require Import`
  lines and file boundaries.
- Does not address whether Cor 1.6.5 ("alternating perm maximizes
  beta(w)") admits a cd-index-free proof. That's a separate
  mathematical question, not a refactoring one.
