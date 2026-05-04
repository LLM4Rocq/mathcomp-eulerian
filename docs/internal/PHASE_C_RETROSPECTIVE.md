# Phase C Retrospective — André's Reflection Method

> **What this is.** A factual record of the 8-session attempt to formalize
> Stanley EC1 §1.6.4 (André's reflection method for Euler numbers) in
> `experimental/reflection.v`. Captures the structural obstacle that
> made the headline `euler_rec` resist closure, the precise residual
> admit, and a concrete plan for any future discharge attempt.
>
> Audience: future contributors (or future-self) who want to either
> finish the proof, or transfer the lessons to a similar bijective
> argument.

## 1. Outcome

`experimental/reflection.v`, 1751 LOC, exists outside the active build
chain. Contains:

- `euler_rec n : 2 * eulerA n.+2 = \sum_(k < n.+2) 'C(n.+1, k) * eulerA k * eulerA (n.+1 - k)`
  — proven (one-line proof: `by rewrite two_eulerA_split boundary_cancellation_alt`).
- One named `Admitted`:
  ```coq
  Lemma sum_set_is_alt_eq_andre_sum n :
    \sum_(t : {perm 'I_n.+1}) \sum_(p : 'I_n.+2)
        set_is_alt (descent_set (insert_max_perm t p))
    = \sum_(k < n.+2) 'C(n.+1, k) * eulerA k * eulerA (n.+1 - k).
  ```
- Compute sanity: `euler_rec_n0_direct` proven unconditionally;
  `euler_rec_n1_via`, `euler_rec_n2_via` proven via `euler_rec`
  (transitively use the admit).

The active build chain (`_CoqProject`) excludes this file and remains
"0 axioms, 0 Admitted." See commit `13fe57b`.

## 2. Session-by-session

| # | Commit | Headline outcome | Estimate at end of session |
|---|--------|------------------|----------------------------|
| C-1 | `41ca2f8` | Defs + base cases | "C-2 closes the descent lemmas" |
| C-2 | `e29eaed` | `descent_set_insert_max_*` (3 cases) | "C-3 closes sub-perm infra" |
| C-3 | `1e04554` | embed_left/right, perm_left/right | "C-4 closes counting" |
| C-4 | `2761450` | rank, descent, partition lemmas | "C-5 closes assembly" |
| C-5 | `f3afd02` | `assemble_perm` + one-direction round-trip | "C-6 closes the bijection" |
| C-6 | `4cdf16b` | Full bijection round-trip + skeleton | "C-7 closes (~150 LOC)" |
| C-7 | `2435a03` | `sum_reindex_inner` (the C-6 gap) | "C-8 closes (~100-200 LOC)" |
| C-8 | `4b983ee` | `euler_rec` derived from named admit | (synthesis: hard stop) |

Pattern: each session lands genuinely useful infrastructure, then
re-projects the headline as "now just one combinatorial step away."
The estimates were wrong but each was made in good faith based on the
state visible at session-end. The headline kept moving because each
session surfaced a *qualitatively different* obstacle, not "more of
the same."

## 3. The structural obstacle

The classical proof of

  `2 E_{n+1} = \sum_k C(n,k) E_k E_{n-k}`

partitions permutations of `[n+1]` by `j := σ⁻¹(max)`. The values
left of `max` form a set `L` of size `j`; left and right sub-words
are independently arranged. The sum factors as a binomial × two
independent Euler-counts:

  `\sum_(L,sL,sR) [σ alternating] = C(n,j) · A_j · A_{n-j}`

The factor of 2 on the left absorbs the boundary descent at slot j-1
(which depends on `max(L)` vs first(~L)) via the alt ↔ ~:alt
involution.

**The formal obstacle.** The boundary descent at slot j-1 of
`assemble_perm L sL sR` is a function of `(L, sL, sR)` *jointly*:
specifically `enum_val_L (sL last) > enum_val_{~:L} (sR first)`. So
`[descent_set t == E]` does NOT factor cleanly into
`[sL-condition] * [sR-condition]`.

The classical "factor of 2 absorbs the boundary" argument has a
specific formal shape: of the 4 alt-flavour pairs
`(sL_flavour, sR_flavour) ∈ {alt, ~:alt}²`, exactly 1 is consistent
with the forced boundary parity for any given `(L, sL, sR)`. So the
inner sum factors *after* the alt + ~:alt sum is taken — a 4-to-1
reduction, not the 2-to-1 fibration that the classical English
description suggests.

## 4. What was missed in early estimates

- **C-5 / C-6 estimates assumed a 2-to-1 fibration** (one involution
  on `(sL, sR)` swaps boundary parity). Three-agent design session
  in C-7 rejected this: no clean per-`(L, sL, sR)` involution exists.
- **C-7 estimates assumed `set_is_alt_classify` factors at the
  boundary slot for free.** The C-8 mathematician + Rocq expert
  reviewers (post-mortem) confirmed this is wrong: the L-part
  constraint differs between alt and ~:alt, so summing alt + ~:alt
  doesn't make the boundary slot free in the obvious way.
- **The actual structure is a 4-to-1 reduction**, not a 2-to-1
  fibration. Mid-plan, the C-8 Rocq expert revised the bottleneck
  lemma's statement three times due to factor-of-2 and off-by-one
  bookkeeping. The fact that an expert couldn't pin down the
  statement on first pass is the strongest evidence that
  formalization cost will exceed estimates by 1.5-2x.

## 5. The infrastructure that DID land

All of the following are kernel-validated, axiom-free, and reusable
for any future bijective decomposition of permutations by
position-of-max. They live in `experimental/reflection.v` but the
math is general:

| Block | Section | Content |
|-------|---------|---------|
| `descent_set_insert_max_*` | §C | Descent set of `insert_max_perm t p` for `p ∈ {ord0, ord_max, interior}` |
| `embed_left`, `embed_right`, `image_left`, `image_right` | §D | Embeddings of sub-positions into the full perm |
| `perm_left`, `perm_right` | §D | Standardisation of left/right sub-words to `'I_j` and `'I_(n+1-j)` |
| `enum_val_perm_left/right` | §D | Round-trip through `enum_val`/`enum_rank_in` |
| Sortedness + `is_descent_perm_*` | §F-§G | Descent characterisation on left/right halves |
| `descent_set_decomp_partition` | §I | The full descent-set decomposition L-part ⊔ {boundary?} ⊔ R-part |
| `assemble_perm` + round-trips | §J.1-J.7 | Inverse of the (j, L, sL, sR) decomposition |
| `assemble_decomp_inverse` | §J.6 | Both directions of the bijection |
| `sum_partition_image_left` | §J.10 | `partition_big` over the left image set |
| `sum_reindex_inner` | §J.10 | Reindex `\sum_t` over fixed L into `\sum_(sL,sR)` |
| `set_is_alt_indicator` | §L.0 | `[s ∈ alt] + [s ∈ ~:alt] = set_is_alt s` |
| `alt_plus_nalt_as_set_is_alt_sum` | §L.0 | `beta(alt) + beta(~:alt) = \sum_t set_is_alt(descent_set t)` |
| `two_eulerA_split` | §J.9 | `2 * eulerA n.+2 = beta(alt) + beta(~:alt)` |
| `eulerA_S2`, `beta_eq_pair_sum`, `beta_eq_double_sum`, `beta_eq_triple_split` | §J.9 | Recurrence skeleton (the `(t, p)`-view + ord0/ord_max/interior split) |

These do NOT depend on the admit. Anything that wants the
position-of-max decomposition of permutations can copy them out.

## 6. Discharge plan (if anyone wants to try)

Per the C-8 Rocq-expert reviewer, ~510 LOC over 3 sessions.
Bottleneck: `sum_alt_assemble_boundary` (~220 LOC). Key new lemmas:

```coq
(* Group A — set_is_alt translation under the three insert positions *)
Lemma set_is_alt_lift_ord0 n (D : {set 'I_n.+1}) : ...    (* ~25 LOC *)
Lemma set_is_alt_lift_ord_max n (D : {set 'I_n.+1}) : ... (* ~25 LOC *)
Lemma set_is_alt_interior_eq n (t : {perm 'I_n.+1}) (j' : 'I_n) : ...  (* ~50 LOC *)

(* Group B — the boundary cancellation (the bottleneck) *)
Lemma sum_alt_assemble_boundary
    n (j : 'I_n.+2) (Hj : 0 < j) (Hjn : j < n.+1) (L : {set 'I_n.+1})
    (HL : #|L| = j) :
  \sum_(s : {perm 'I_j} * {perm 'I_(n.+1 - j)})
       set_is_alt (descent_set (assemble_perm HL s.1 s.2))
  = eulerA j * eulerA (n.+1 - j).         (* ~220 LOC *)

(* Group C — per-position aggregation *)
Lemma sum_alt_p_ord0 n     : ... = eulerA n.+1.   (* ~35 LOC *)
Lemma sum_alt_p_ord_max n  : ... = eulerA n.+1.   (* ~30 LOC *)
Lemma sum_alt_p_interior n (j' : 'I_n) :
  ... = 'C(n.+1, j'.+1) * eulerA j'.+1 * eulerA (n - j').  (* ~70 LOC *)

(* Group D — final assembly via exchange_big + big_ord_recl/recr *)
(* discharges the admit; ~50 LOC *)
```

**Critical idiom for the bottleneck.** After
`descent_set_decomp_partition`, the boundary bit at slot j-1 is
**forced** by `(L, sL, sR)`. Of the 4 flavour pairs
`(sL_flavour, sR_flavour) ∈ {alt, ~:alt}²`, exactly 1 is consistent
with each fixed boundary value. The total count of
boundary-consistent alt-flavour pairs (summed over `(sL, sR)` for
fixed L) is `eulerA j * eulerA (n.+1 - j)`. Showing this requires
either:
- A custom involution on `(sL, sR)` that flips both flavour and
  boundary (per Rocq expert), OR
- A direct case analysis on the 4 flavour pairs with a parity
  argument (per mathematician's `alt_classify_at_boundary`).

The Rocq expert's involution route is more idiomatic; the
mathematician's case analysis is more transparent.

**Off-by-one alert.** Mid-plan the Rocq expert revised statements
multiple times due to:
- Whether `2 * eulerA n.+1` or `eulerA n.+1` is the per-`p` total
  (resolution: `set_is_alt` is a boolean, not a flavour-counter; each
  `t` contributes 1 if `set_is_alt(descent_set t)` else 0).
- Parity offset induced by skipping `h` in the lift.
- Whether `j' : 'I_n` corresponds to `k = j'` or `k = j'.+1` in the
  binomial sum (resolution: `k = j'.+1`, with ord0 → k=0 and ord_max
  → k=n+1).

Verify by hand for small `n` before committing to a statement.

## 7. Verified by hand for n = 0

LHS: `\sum_(t ∈ S_1) \sum_(p ∈ 'I_2) set_is_alt(descent_set(insert_max_perm t p))`.
- `t = id`, `descent_set id = ∅`.
- `p = 0`: `descent_set(insert_max id 0) = {0}`. In `{set 'I_1}`,
  `alt_desc_set 1 = setT = {0}`, so `set_is_alt({0}) = true`.
  Contributes 1.
- `p = 1`: `descent_set(insert_max id 1) = ∅`. `set_is_alt(∅) = true`
  vacuously. Contributes 1.
- Total: 2.

RHS: `\sum_(k < 2) 'C(1, k) * eulerA k * eulerA (1 - k)`
    = `1·1·1 + 1·1·1 = 2`. ✓

The `euler_rec_n0_direct` proof (file line 1735) confirms this
unconditionally.

## 8. What this admit does NOT depend on

- It does NOT use `compl_perm` or `beta_compl` (those are used in
  `two_eulerA_split` outside the admit).
- It does NOT use `set_is_alt_classify` directly (that classifies
  alt-or-~:alt globally; the local boundary parity is a different
  fact).
- It does NOT use any axiom or admit from the active build chain.

## 9. Lessons for similar bijective formalizations

1. **Estimate the bottleneck lemma's STATEMENT before estimating its
   PROOF.** Phase C's confident estimates were all about proof
   length; the Rocq expert's mid-plan revisions of the statement
   itself were the warning sign that estimates were unreliable.
2. **Three-agent design (mathematician + Rocq expert + devil's
   advocate) caught two FALSE statements in this project before
   formal attempts** (Stirling H2 conjugation, original
   `maj_rev_perm`). Use it pre-session for any bijective lemma
   whose statement involves more than two coupled objects.
3. **The "factor of 2" in classical bijective proofs is rarely a
   2-to-1 fibration in the formal sense.** It's often a 4-to-1
   reduction or a more delicate parity argument. Budget accordingly.
4. **An admit is not a defeat if the statement is precise and
   surgically isolated.** Phase C ships `euler_rec` as
   "proven modulo one named, machine-checked-statement lemma."
   The math is captured; the proof is open.

## 10. Pointers

- File: `/workspace/experimental/reflection.v` (1751 LOC).
- Admit: line 1693 (`sum_set_is_alt_eq_andre_sum`).
- Headline: line 1705 (`euler_rec`).
- Sanity (axiom-free): line 1735 (`euler_rec_n0_direct`).
- Plan doc: `/workspace/docs/plans/REFLECTION_PLAN.md`.
- Build manually: `coqc -R . mathcomp_eulerian experimental/reflection.v`.
