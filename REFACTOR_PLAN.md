# Heavy `-vo` Refactor Plan

Roadmap for getting the last 3 files to full `-vo` compilation. To be executed
in a fresh session.

## Current state (start of refactor)

- `.vo` count: 18/21
- `.vos` count: 21/21 (all proofs type-check; 0 `Admitted`, 0 `Axiom`)
- `.vo` holdouts:
  - `psi_cdindex_support.v` (1266 LOC, 53 lemmas)
  - `perm_seq_bridge.v` (1025 LOC, 44 lemmas)
  - `beta_swap.v` (301 LOC, 22 lemmas)

The 3 holdouts are syntactically clean (every tactic succeeds at `-vos`), but
the kernel can't elaborate the resulting proof terms in available
time/memory. `psi_cdindex_support.v` was observed running 60+ minutes with two
`rocqworker` processes each at ~46 GB RSS without producing a `.vo`.

This is the same class of issue the original `psi_cdindex_tree_hlc.v` /
`psi_cdindex_tree.v` had (>131 GB proof terms during `-vo` serialization), and
which the `mmtree-shape` refactor resolved (`psi_cdindex_tree_shape.v`: 8s,
~0.6 GB peak).

## The proven pattern: shape-and-corollary

From `psi_cdindex_tree_shape.v`:

1. **Identify** the heavy proof — typically one with deep nested case analysis
   on a structured datatype (e.g. recursion over `seq cde`, `seq nat`,
   `mmtree`).
2. **Abstract** the load-bearing input. Define a `*_shape` function that
   reduces the structured datatype to a minimal feature set (e.g. comparison
   pattern, transition pattern, descent positions).
3. **Prove the heavy lemma once on the shape.** This isolates the kernel cost
   to a single proof term, and lets you mark it `Qed` (opaque) so downstream
   reduction stops there.
4. **Derive concrete corollaries** as 5-line wrappers that pass through the
   shape lemma. Each corollary is small and elaborates trivially.

The refactor is "structural" — it doesn't change the math, it changes which
intermediate facts the kernel must rebuild.

## Per-file diagnosis

Run this first to confirm where each file's `-vo` cost concentrates:

```bash
for f in psi_cdindex_support perm_seq_bridge beta_swap; do
  /usr/bin/time -v opam exec -- coqc -R . mathcomp_eulerian \
    -w -deprecated-library-file -w -notation-overridden $f.v 2>&1 | \
    tee $f.vo.log
done
```

Watch for `Maximum resident set size` and which lemma the worker is on at
death. Likely culprits below are pre-identified from reading the proofs.

### `psi_cdindex_support.v`

Likely heavy proofs (long induction over `seq cde` with deep case analysis):

| Lemma | Line | Why it's heavy |
|-------|------|----------------|
| `expand_cde_mem_transitions` | 75 | Induction over `m : seq cde` with `[||]` case split (C/D/E). Each branch destructs the cat of two filtered/mapped iotas. Proof terms multiply. |
| `transitions_expand_cde_mem` | 125 | Same structure as above, reverse direction. |
| `phi_w_decomp_mm` | 503 | Splits `iota 0 (size s)` at `mm_pos`, then proves each segment correct. |
| `S_w_seq_decomp_mm` | 630 | Same shape as `phi_w_decomp_mm` plus offset arithmetic. |
| `cde_total_width_phi_w_all` | 711 | The 80-line arithmetic mega-proof; the agent already split helper steps but kernel still struggles. |
| `D_offsets_phi_w_eq_S_w_seq` | 803 | Combines several heavy facts. |
| `phi_w_support_general` | 880 | Top-level theorem; cheap if the supporting lemmas are opaque. |

Already-cheap (small proof terms — leave alone):

- `has_transition_cons`, `has_transition_cons2`, `cde_offset_C_succ`,
  `cde_offset_D_succ` — these are 1-line `by rewrite /...` proofs the agent
  added; they help by isolating a definitional unfolding.

#### Refactor proposal

Create `psi_cdindex_support_core.v` that defines:

```coq
(* The "shape" of a cd-word: just the lengths and D-positions. *)
Record cde_shape := {
  cs_widths : seq nat;          (* per-letter contribution: 1, 2, or 0 *)
  cs_d_indices : seq nat        (* indices i where letter is D *)
}.

Definition shape_of_cde (m : seq cde) : cde_shape :=
  {| cs_widths := [seq cde_width l | l <- m];
     cs_d_indices := [seq i <- iota 0 (size m) | is_D_letter (nth C_letter m i)] |}.

(* expand_cde behaves the same on cd-words with the same shape:
   D-transitions only depend on cs_widths and cs_d_indices. *)
Lemma expand_cde_mem_iff_shape m X :
  size X = sumn (cs_widths (shape_of_cde m)) ->
  (X \in expand_cde m) =
  all (fun k => has_transition X k)
      (cum_offsets (cs_widths (shape_of_cde m))
                   (cs_d_indices (shape_of_cde m))).
Proof. (* the heavy proof, done ONCE, opaque Qed *) Admitted.
```

Then in `psi_cdindex_support.v`:

```coq
Lemma expand_cde_mem_iff m X :
  size X = cde_total_width m ->
  (X \in expand_cde m) = all_D_transitions m X.
Proof.
move=> Hsz.
by rewrite expand_cde_mem_iff_shape // /shape_of_cde /=
           /cde_total_width /D_offsets /all_D_transitions.
Qed.
```

The corollary is now small (kernel checks unfolding only, no induction).

#### Subgoals worth carving out

While doing the above, consider extracting these as standalone opaque lemmas
(small interfaces, hidden proofs):

- `expand_cde_size_invariant` — `X \in expand_cde m -> size X = ...`. Already
  exists as `size_in_expand_cde`; ensure it's `Qed` (opaque) and not used
  inside transparent proofs.
- `cde_offset_decomp` — `cde_offset (m1 ++ l :: m2) i` for the three positions
  (i < size m1, i = size m1, i > size m1). Replaces inline `take_cat` /
  `nth_cat` reasoning that bloats each callsite.
- `D_offsets_split` — `D_offsets (m1 ++ D :: m2) = D_offsets m1 ++ ...`. The
  `D_offsets_cat_D` body already has this shape; promote it to a clean
  interface.
- `phi_w_at_mm_split` — `phi_w (a :: rest) = phi_w (take j ...) ++ D :: phi_w
  (drop j.+1 ...)` when `0 < mm_pos`. This is `phi_w_decomp_mm` already; verify
  it's `Qed`-opaque.

### `perm_seq_bridge.v`

Likely heavy proofs (set ↔ seq translation over `'I_n`):

| Lemma | Line | Why it's heavy |
|-------|------|----------------|
| `is_descent_perm_seq` | 67 | Connects `is_descent` (set-based) to `is_descent_seq` (seq-based) with bound-juggling. |
| `char_mono_perm_to_seq` | 101 | Top-level char monomial bridge. |
| `descent_to_bvec_inj` | 116 | Injectivity of the bvec encoding. |
| `class_char_monos_uniq` | 187 | Uniqueness of char monomials over the M-class. |
| `char_mono_class_inj` | 200 | Injectivity of the char-mono map. |
| `seq_to_perm_*` (lines 291-340) | | Section with several intertwined lemmas. |

#### Refactor proposal

The bridge between `{perm 'I_n}` and `seq nat` repeats argument patterns. Pull
them into a `Module BvecOfDescent` with:

```coq
Definition desc_bvec n (s : {perm 'I_n.+1}) : seq bool :=
  [seq is_descent s i | i : 'I_n].

(* Heavy lemma: this respects the seq/set duality. *)
Lemma desc_bvec_seq n (s : {perm 'I_n.+1}) :
  desc_bvec s = is_descent_seq_bvec (perm_to_seq s).
```

Then re-derive:

- `is_descent_perm_seq` from `desc_bvec_seq` + `nth` extraction.
- `char_mono_perm_to_seq` as `congr` over the bvec.
- Class-injectivity as injectivity of `desc_bvec` (proved once on bvecs, not
  again on each consumer).

The `seq_to_perm` / `perm_to_seq` round-trip also benefits from being proved
once at the level of `nth` and reused.

### `beta_swap.v`

Likely heavy proofs:

| Lemma | Line | Why it's heavy |
|-------|------|----------------|
| `beta_compl` | 166 | β(D) = β(~D); deep case work over set membership. |
| `beta_set_is_alt_eq` | 216 | Equality of β over alternating descent sets. |
| `beta_alt_max` | 273 | Top-level; cheap if `beta_compl` and `beta_set_is_alt_eq` are opaque. |

#### Refactor proposal

Smallest of the three. The "shape" here is the *parity pattern* of the
descent set, not the set itself. Define:

```coq
Definition desc_parity n (D : {set 'I_n}) : seq bool :=
  [seq i \in D | i : 'I_n].

Lemma beta_eq_of_parity n (D E : {set 'I_n}) :
  desc_parity D = desc_parity E -> beta D = beta E.
```

Then `beta_compl` becomes `desc_parity D = desc_parity (~: D)` after
toggling — short, structural.

`beta_alt_max` likely needs no refactor once `beta_compl` and friends are
opaque.

## Execution order

Refactor in this order — earlier wins unblock later files:

1. **`psi_cdindex_support.v`** (highest impact; both downstream files depend
   on it). Ship `psi_cdindex_support_core.v` first, verify `-vo`, then trim
   `psi_cdindex_support.v`.
2. **`perm_seq_bridge.v`** — once `support` is `.vo`, retry. Often files
   "just work" at `-vo` once their imports are kernel-elaborated.
3. **`beta_swap.v`** — last; smallest; should be fast.

After each step, run:

```bash
opam exec -- make
ls *.vo | wc -l   # should increment
opam exec -- coqchk -R . mathcomp_eulerian -silent \
  -o mathcomp_eulerian.<file>     # verify 0 axioms
```

## Hygiene rules learned this session

1. **Never run multiple `coqc` on the same file in parallel** — each
   `rocqworker` consumes 10–46 GB. Two competing builds can OOM the host.
   Kill duplicates before launching a fresh build.
2. **`-vos` and `-vo` test different things.** `-vos` checks tactics; `-vo`
   checks elaborated proof terms. A file passing `-vos` does NOT mean it
   passes `-vo`. Always verify with the full build.
3. **`Qed` vs `Defined`** — heavy lemmas must be `Qed` (opaque). A `Defined`
   proof is unfolded in every consumer, multiplying the proof term.
4. **`Set Implicit Arguments` interaction** — when a lemma like
   `classify_skip_mm0 i a rest : ...` has `Set Implicit Arguments`, all
   positional args become implicit; pass only the *hypotheses*, not
   `(_ _ _ Hmm Hi)`.
5. **Linter rewrites are opportunistic** — the editor occasionally rewrites
   tactic chains. Re-read the file after every edit before the next edit.
6. **`case: x` fails when `x` appears in another binder's body** (e.g.
   `s := a :: x`). Use `case: (x)` parens, or `clearbody` first if you don't
   need the binding.
7. **`congr (filter _ _)` works when both filters are over the same list**.
   When the lists differ, use `eq_in_filter` to align the predicates first,
   then `eq_in_map` for the inner map.

## What NOT to do

- **Do not introduce `Admitted`.** The current build has 0; keep it that way.
- **Do not skip the kernel re-check** with `-vos` once you think you're done.
  The whole point is `-vo`. A `.vos` build that takes 12 s is no evidence
  the `.vo` will succeed.
- **Do not add new axioms.** `coqchk` will catch them but the goal is
  fully axiom-free.
- **Do not refactor proofs that already build at `-vo`.** Touch only the
  3 holdouts and any new helper file you create.

## Pointers to existing context

- `BUILD_PLAN.md` — current build status and the original tree refactor
  context.
- `psi_cdindex_tree_shape.v` — the model refactor. Read its top comment for
  intuition on shape encoding.
- `psi_cdindex_tree.v` lines 1-50 — shows the corollary pattern: trivial
  derivations once the shape lemma is proved.

## Sanity check before declaring victory

```bash
opam exec -- make clean
opam exec -- make            # full -vo build
ls *.vo | wc -l              # expect: 21
opam exec -- coqchk -R . mathcomp_eulerian -silent \
  -o mathcomp_eulerian.beta_swap   # last file in chain
# Expect: Axioms: <none>
grep -rn "Admitted" *.v       # expect: empty
```
