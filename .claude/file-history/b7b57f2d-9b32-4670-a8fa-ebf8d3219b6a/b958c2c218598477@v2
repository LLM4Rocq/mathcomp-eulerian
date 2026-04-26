# Foata Swap Formalization Guide

Plan for discharging the two classical axioms in `beta_swap.v`:

```coq
Axiom beta_swap_monotone : forall n (D : {set 'I_n}) (i j : 'I_n),
  val j = (val i).+1 ->
  (i \in D) = (j \in D) ->
  beta D <= beta (toggle_at D i).

Axiom beta_swap_lt : forall n (D : {set 'I_n}) (i j : 'I_n),
  val j = (val i).+1 ->
  (i \in D) = (j \in D) ->
  beta D < beta (toggle_at D i).
```

## 1. What the axioms say

Let `D ⊆ 'I_n` be a descent-position set, and let `i, j = i+1` be two consecutive positions with the **same** D-membership (both descents or both ascents in a permutation). Then toggling `i` (flipping its membership in D) **strictly increases** the number of permutations whose descent set is exactly D.

Intuition: a descent set with a "run" of equal types (two consecutive descents, or two consecutive ascents) is less constraining after we break that run.

## 2. Source

Stanley, *Enumerative Combinatorics* Vol. 1:

- §1.4 ("P-partitions") develops the general framework.
- §1.6 ("Descents") contains the specific `β(D)` inequality.

Alternative references: Loday's work on quasi-symmetric functions; the "ribbon Schur function" / "descent polytope" literature. The result is sometimes called "descent-composition unimodality".

## 3. Proof idea

Construct an **injection** `Φ : {σ : descent_set σ = D} ↪ {τ : descent_set τ = toggle_at D i}` via **block-based cyclic rotation**.

### 3.1 The block

Assume the "both descents" case (`i ∈ D` and `j = i+1 ∈ D`); the ascent case is dual.

For `σ` with descent set D:
- Positions `i, i+1` are descents, so `σ(i) > σ(i+1) > σ(i+2)`.
- Let `[l, r]` be the **maximal block of consecutive descent positions of σ** containing both `i` and `i+1`. So:
  - `l ≤ i < i+1 ≤ r`,
  - positions `l, l+1, …, r` are all descents: `σ(l) > σ(l+1) > … > σ(r+1)` (strictly decreasing chain of `r-l+2` values),
  - position `l-1` is *not* a descent (or `l = 0`): `σ(l-1) < σ(l)` if `l > 0`,
  - position `r+1` is *not* a descent (or `r+1 = n`): `σ(r+1) < σ(r+2)` if `r < n-1`.

### 3.2 The rotation

Define `Φ σ` by **moving the block minimum `σ(r+1)` to position `i+1`** (between `σ(i)` and where `σ(i+1)` used to be), and shifting `σ(i+1), σ(i+2), …, σ(r)` one position to the right:

```
positions:   …  l  …  i-1   i      i+1     i+2    …   r    r+1  …
before:      …  σ(l) … σ(i-1) σ(i)   σ(i+1)  σ(i+2) …  σ(r)  σ(r+1)  …
after:       …  σ(l) … σ(i-1) σ(i)   σ(r+1)  σ(i+1) …  σ(r-1) σ(r)   …
```

Precisely: `(Φ σ)(k) = σ(k)` for `k < i+1 or k > r+1`, and `(Φ σ)(k) = σ(r+1)` if `k = i+1`, `(Φ σ)(k) = σ(k-1)` if `i+1 < k ≤ r+1`.

### 3.3 Why this is the right construction

Descent-by-descent analysis:

| Position | Before | After | Reason |
|----------|--------|-------|--------|
| `l-1` | ascent (block-maximal) | unchanged | `σ(l-1), σ(l)` untouched |
| `l, l+1, …, i-1` | descent | descent | values unchanged |
| `i` | descent | **ascent (toggled)** | `σ(i) > σ(r+1)` still holds, **but** compare `σ(i)` with the *new* `(Φ σ)(i+1) = σ(r+1)`: descent was `σ(i) > σ(i+1)`; now it's `σ(i) > σ(r+1)`, still a descent! ⚠️ |

**⚠ This is where the naïve block-rotation fails.** The "move block minimum to position i+1" construction described in §3.2 does *not* correctly toggle position `i` — moving the minimum into position `i+1` only strengthens the descent there. See §4 below for the actual fix.

### 3.4 The correct rotation

After more careful analysis, the right construction for the "both descents" case is:

**Move the block MAX `σ(l)` one position to the right of `i`**, and close the cycle:

```
positions:   …  l      l+1   …  i    i+1   i+2  …  r+1  …
after:       …  σ(l+1) σ(l+2) … σ(i+1) σ(l) σ(i+2) … σ(r+1) …
```

But this disturbs position `l-1` (compare `σ(l-1)` with `σ(l+1)` rather than `σ(l)`; status may flip).

**Neither end works alone.** The classical Foata construction pairs the rotation with a **boundary adjustment**, or uses a **two-block sweep**.

## 4. The actual classical argument

The correct construction is subtler than a single rotation. It uses one of:

### Approach A: *Pair* of rotations

Rotate the block containing `i` *and* simultaneously adjust at the block boundaries. The canonical form (Stanley EC1 §1.4, Exercise 1.36 or related) uses **P-partitions** and a *bijection on labeled chains*.

### Approach B: *Insertion tableau* via RSK

For each `σ` with descent set `D`, compute its RSK-image `(P, Q)`. The descent set of `σ` is determined by `Q`. Toggling descent at position `i` corresponds to an elementary transformation of `Q` that is easier to analyze.

### Approach C: *Quasi-symmetric function* expansion

`β(D)` is the coefficient of a specific quasi-symmetric function in a product of "ribbon Schur" functions. Monotonicity under toggling is a positivity property.

### Approach D (most concrete): *Run-based swap with backtracking*

For each `σ` with `descent_set σ = D` and `i, j` same-membership:

1. Identify the "Foata block" `[l, r]` as in §3.1.
2. **If `l > 0` and `σ(l-1) < σ(r+1)`** (boundary-safe case): rotate block so that `σ(l)` moves to position `r+1`. All internal descents are preserved by chain-transitivity; the "wrap-around" descent at position `i` becomes an ascent; and position `l-1` remains an ascent because `σ(l-1) < σ(r+1) < σ(l+1)`.
3. **Otherwise (boundary-unsafe)**: extend the block leftwards to swallow the problematic value, or use a different canonical rotation. This is where the classical proof does detailed case analysis.

### Suggested formalization path

Start with Approach D. Key sub-lemmas to formalize:

```coq
(* Left endpoint of the maximal descent-block containing position i. *)
Definition block_left (σ : {perm 'I_n.+1}) (i : 'I_n) : 'I_n := …

(* Right endpoint, likewise. *)
Definition block_right (σ : {perm 'I_n.+1}) (i : 'I_n) : 'I_n := …

Lemma block_left_ascent : val (block_left σ i) > 0 ->
  is_ascent σ (some ord with val (block_left σ i) - 1).

Lemma block_descent_chain :
  forall k, l <= k <= r -> is_descent σ (Ordinal _ k).

(* The rotation permutation. *)
Definition foata_rot (σ : {perm 'I_n.+1}) (i : 'I_n) : {perm 'I_n.+1} := …

Lemma foata_rot_inj σ i : injective (foata_rot σ i).   (* easy via structure *)

Lemma descent_set_foata_rot (σ : {perm 'I_n.+1}) (D : {set 'I_n}) (i j : 'I_n) :
  val j = (val i).+1 ->
  descent_set σ = D ->
  (i \in D) = (j \in D) ->
  descent_set (foata_rot σ i) = toggle_at D i.       (* the hard lemma *)

Lemma foata_rot_preimage_inj (D : {set 'I_n}) (i j : 'I_n) :
  val j = (val i).+1 ->
  (i \in D) = (j \in D) ->
  injective (fun σ : { σ | descent_set σ = D } => foata_rot (sval σ) i).
```

Then `beta_swap_monotone` follows by `card_imset` on the injection, and `beta_swap_lt` by exhibiting an `insert_max_perm`-based witness that's not in the image.

## 5. Dead ends — don't waste time on these

Summary of local approaches that **provably do not work** (I verified small counter-examples):

| Construction | Fails at |
|--------------|----------|
| `σ ↦ σ ∘ tperm (widen_ord i) (lift ord0 i)` (swap positions `i, i+1`) | position `i-1` if σ(i-1) ∈ (σ(i+1), σ(i)) |
| `σ ↦ σ ∘ tperm (lift ord0 i) (lift ord0 (S i))` (swap positions `i+1, i+2`) | position `i+2` (and toggles the wrong descent) |
| Cyclic 3-rotation `(σ(i), σ(i+1), σ(i+2)) → (σ(i+2), σ(i), σ(i+1))` | position `i-1` if σ(i-1) ∈ (σ(i+2), σ(i)) |
| Value-transposition via `tperm (σ i) (σ (i+1))` | same issue as position-swap |
| "Move block minimum to position i+1" (§3.2) | doesn't actually toggle position `i` |

Conclusion: **a non-local argument is required** — one that carefully handles the two ends of the block.

## 6. Infrastructure already available in the project

Things already proved that should be re-used:

### From `descent.v`
- `is_descent σ i`, `descent_set σ`, `des σ`, `asc σ`
- `rev_perm`, `is_descent_rev`, `des_rev_perm`
- `rev_perm_ord`

### From `perm_compress.v`
- `drop_perm`, `lift_perm`, bijection (`drop_perm_lift_perm`, `lift_perm_drop_perm`)
- `is_descent_drop`

### From `eulerian.v`
- `insert_max_perm`, `extract_max_perm`, bijection (`insert_max_perm_bij`)
- `insert_max_perm_at_p`, `insert_max_perm_lift`, `insert_max_perm_fiber`
- `des_insert_max_ord0`, `des_insert_max_ord_max`, `des_insert_max_interior`

### From `beta.v`
- `beta`, `beta0`, `beta_full`, `sum_beta_eq_fact`, `beta_eulerian`
- `beta_rev` (β symmetric under `D ↦ rev_ord @: ~D`)
- `imset_rev_ord_inv`, `imset_rev_ord_compl`

### From `beta_swap.v` (already Qed)
- `toggle_at`, `toggle_atK`, `toggle_at_self`, `toggle_at_other`, `toggle_at_in`
- `alt_desc_set`, `set_is_alt`, `alt_desc_set_is_alt`, `set_not_altP`, `set_is_alt_classify`
- `compl_perm` (= `s * rev_perm_ord n`), `compl_perm_inj`, `compl_perm_involutive`
- `is_descent_compl`, `descent_set_compl`, `beta_compl`
- `sym_diff`, `sym_diff_toggle_in`, `sym_diff_eq0`
- `beta_lt_fact`, `not_set_is_alt_n_ge2`, `beta_set_is_alt_eq`

## 7. Strict version (`beta_swap_lt`)

Once `beta_swap_monotone` is proved as an injection `Φ`, the strict gap follows by exhibiting a permutation `τ'` in the target fiber **not in the image**.

Natural candidate: use `insert_max_perm` to construct the permutation of `'I_{n+1}` whose maximum value is at position `i+1` and whose "Foata block containing `i` in the target" has length exactly 2. The preimage under `Φ` would require a length-1 block in the source, which is impossible (a length-1 descent block can't contain both `i` and `i+1`).

Concretely:

```coq
(* Candidate witness: max value placed at position i+1 in the toggled fiber. *)
Definition swap_witness (D : {set 'I_n}) (i : 'I_n) : {perm 'I_n.+1} :=
  insert_max_perm
    (* some canonical τ whose descent set, after insert_max at i+1,
       lands in toggle_at D i *)
    … i.

Lemma swap_witness_descent D i j :
  val j = (val i).+1 ->
  (i \in D) = (j \in D) ->
  descent_set (swap_witness D i) = toggle_at D i.

Lemma swap_witness_not_in_image D i j :
  val j = (val i).+1 ->
  (i \in D) = (j \in D) ->
  ~ exists σ,
      descent_set σ = D /\ foata_rot σ i = swap_witness D i.
```

Then `beta_swap_lt` follows by `#|image_of_injection| + 1 ≤ #|target_fiber|` via cards.

## 8. Effort estimate

| Task | Estimated lines | Difficulty |
|------|----------------|-----------|
| `block_left` / `block_right` definitions & well-foundedness | 30 | easy |
| Block characterization lemmas (boundaries, chain structure) | 50 | medium |
| `foata_rot` permutation definition (via `perm` constructor + injectivity) | 40 | medium |
| `descent_set_foata_rot` (the key preservation lemma) | 100–150 | **hard** |
| `foata_rot_inj` | 30 | medium (reuse block characterization) |
| Assembly of `beta_swap_monotone` | 20 | easy |
| `swap_witness` construction + properties | 60 | medium-hard |
| Assembly of `beta_swap_lt` | 30 | medium |
| **Total** | **~360–410 lines** | substantial |

## 9. Pitfalls

- **Boundary cases.** When `block_left = 0` or `block_right = n-1`, the "is position `l-1` an ascent" condition becomes "no position to the left" — easy to miss.
- **Block of length 2.** The minimal case `[l, r] = [i, i+1]` is special and often needs separate handling.
- **Empty blocks.** If `i = j - 1` is the *only* descent in a neighborhood, the block is just `{i}`, but the hypothesis `(i ∈ D) = (j ∈ D)` with both in `D` still requires both `i, i+1` to be descents — so the block has length ≥ 2.
- **Both-ascents case.** Don't forget to prove the dual (positions `i, i+1` both *not* in D). One clean way: use `compl_perm` / `beta_compl` to reduce the ascent case to the descent case.
- **Nat subtraction.** In MathComp, `val i - 1` saturates at 0; use `i.-1` or careful case analysis.

## 10. Recommended starting point

1. Write `block_left` / `block_right` and prove their characterization lemmas. (Standalone, doesn't touch permutations.)
2. Write `foata_rot` as a specific `{perm 'I_n.+1}` using `perm` + an explicit injective function.
3. Prove `descent_set_foata_rot` — this is the crux. Do it by `apply/setP => k` and case on the relationship between `k` and the block `[l, r]`.
4. Derive `beta_swap_monotone` via `card_imset`.
5. Separately, construct the `swap_witness` and prove `beta_swap_lt`.

Allow ~2 full days of focused work. A `rocq:admitted-filler-deep` subagent with this document as brief might succeed in one pass; otherwise iterate with interactive `rocq_start` / `rocq_check` to debug the descent-preservation argument case-by-case.
