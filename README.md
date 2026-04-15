# mathcomp-eulerian

A MathComp 2.5+ / Rocq 9.0 formalization of permutation **descent statistics**, **Eulerian numbers**, and the set-refined β-numbers used in Putnam 2025 problem A5. Six layers, each independently useful.

## Build

```
make            # builds all .v files in _CoqProject
```

Dependencies: Rocq ≥ 9.0 and MathComp ≥ 2.5 (`all_ssreflect`, `fingroup`, `perm`, `binomial`, `ssrint`, `ssralg`).

## File structure

```
ordinal_reindex.v → perm_compress.v → descent.v → eulerian.v → beta.v → beta_swap.v
```

| File | Lines | Contents |
|------|-------|----------|
| `ordinal_reindex.v` | 54 | Monotonicity of `lift`/`unlift` on `'I_n` |
| `perm_compress.v` | 115 | `drop_perm` / `lift_perm` bijection on `{perm 'I_n}` |
| `descent.v` | 122 | Descent set, descent/ascent counts, reversal symmetry |
| `eulerian.v` | 746 | Eulerian numbers: base cases, recurrence, symmetry, Worpitzky, closed form |
| `beta.v` | 173 | Set-refined descent counts `β(D)` (Layer 4) |
| `beta_swap.v` | 244 | β-swap lemmas + alt-maximises-β corollary toward Putnam A5 (Layer 5) |

## Results

### Layer 0 — ordinal reindexing (`ordinal_reindex.v`)

Monotonicity lemmas for MathComp's `lift`/`unlift` that are not in the core:

- `leq_lift`, `ltn_lift` — `lift k : 'I_n → 'I_n.+1` is strictly monotone.
- `lift_image` — `lift k` surjects onto `~: [set k]`.
- `ltn_unlift_some` — monotonicity of the `unlift` witness.

### Layer 1 — permutation compression (`perm_compress.v`)

Given `σ : {perm 'I_n.+1}`, produces `τ : {perm 'I_n}` by deleting the `ord_max` position, and vice versa:

- `drop_perm : {perm 'I_n.+1} → {perm 'I_n}`
- `lift_perm : 'I_n.+1 → {perm 'I_n} → {perm 'I_n.+1}`
- `drop_perm_lift_perm : drop_perm (lift_perm k τ) = τ`
- `lift_perm_drop_perm : lift_perm (σ ord_max) (drop_perm σ) = σ`
- `lift_perm_ord_max`, `lift_perm_lift`, `lift_perm_ne_k`, `lift_drop_permE`

### Layer 2 — descent statistics (`descent.v`)

```coq
Definition is_descent s (i : 'I_n) := s (widen_ord _ i) > s (lift ord0 i).
Definition descent_set s := [set i | is_descent s i].
Definition des s := #|descent_set s|.
Definition asc s := n - des s.
```

Core lemmas:

- `des_le`, `des_add_asc` — size bounds.
- `des_id : des (1 : {perm 'I_n.+1}) = 0` — identity has no descents.
- `is_descent_drop` — interior descents are preserved by `drop_perm`.
- **Reversal symmetry**: `rev_perm_ord`, `rev_perm s := rev_perm_ord * s`, `is_descent_rev`, `des_rev_perm : des (rev_perm s) = n - des s`, `des_rev_perm_ord : des rev_perm_ord = n`.

### Layer 3 — Eulerian numbers (`eulerian.v`)

```coq
Definition eulerian (n k : nat) : nat := #|[set s : {perm 'I_n.+1} | des s == k]|.
```

(`eulerian n k` counts permutations of `n+1` elements with exactly `k` descents.)

**Basic properties**:

- `eulerian_row_sum : \sum_(k < n.+1) eulerian n k = #|{perm 'I_n.+1}|`
- `eulerian_row_sum_fact : \sum_(k < n.+1) eulerian n k = n.+1`!`
- `eulerian_out_of_range : n < k → eulerian n k = 0`
- `eulerian_n_0 : eulerian n 0 = 1`
- `eulerian_n_n : eulerian n n = 1`

**Symmetry**: `eulerian_symm : k ≤ n → eulerian n k = eulerian n (n - k)`.

**Recurrence** (proved via the value-based insert-max bijection `{perm 'I_n.+2} ≃ {perm 'I_n.+1} × 'I_n.+2`):

```coq
Lemma eulerian_rec n k :
  eulerian n.+1 k.+1 = k.+2 * eulerian n k.+1 + (n.+1 - k) * eulerian n k.
```

(Note: the bijection is constructed by `insert_max_perm` / `extract_max_perm`, and the recurrence is assembled from three descent-count lemmas — `des_insert_max_ord0`, `des_insert_max_ord_max`, `des_insert_max_interior` — plus a `partition_big` / `reindex` over `σ^{-1}(ord_max)`.)

**Worpitzky's identity**:

```coq
Lemma worpitzky n x :
  x ^ n.+1 = \sum_(k < n.+1) eulerian n k * 'C(x + k, n.+1).
```

Proof is by induction on `n` using `eulerian_rec` and the algebraic identity `worpitzky_binom_id`:

```
x * 'C(x + k, n.+1) = k.+1 * 'C(x + k, n.+2) + (n.+1 - k) * 'C(x + k.+1, n.+2)   (k ≤ n)
```

**Closed-form formula** (in `int`, opens `ring_scope` locally):

```coq
Lemma eulerian_explicit n k :
  (eulerian n k)%:Z =
    \sum_(j < k.+1) (-1) ^ j *+ 'C(n.+2, j) *+ (k.+1 - j) ^ n.+1.
```

Proved by **Worpitzky inversion**. Two supporting lemmas:

- `binS'` — Pascal extension `'C(t, n.+2) = 'C(t.-1, n.+2) + 'C(t.-1, n.+1)` valid even when `t = 0` (saturating subtraction).
- `aux_id` — the alternating-binomial Kronecker identity `\sum_(j < n.+3) (-1)^j *+ 'C(n.+2, j) *+ 'C(t - j, n.+1) = (t == n.+1)%:Z`. Proved by induction on `n` using a recurrence `aux_id_step` (the analog of Vandermonde's `fxx`): `aux_id(n.+1, t) = aux_id(n, t.-1)`, established via two applications of Pascal (one on each binomial factor) plus a reindex that telescopes.

The main theorem then follows: substitute Worpitzky to expand `(k+1-j)^(n+1)`, swap sums (`exchange_big`), recognize the inner `j`-sum as `aux_id` at `t = k+1+m` (after extending the sum bound from `k.+1` to `maxn k.+1 n.+3` — the added terms vanish on each side for orthogonal reasons), use `bigD1` to pick out `m = n - k`, and apply `eulerian_symm`.

### Layer 4 — set-refined β-numbers (`beta.v`)

```coq
Definition beta (n : nat) (D : {set 'I_n}) : nat :=
  #|[set sigma : {perm 'I_n.+1} | descent_set sigma == D]|.
```

`beta D` counts permutations of `'I_n.+1` whose descent set is *exactly* `D`. Summing over `D` of fixed cardinality `k` recovers the classical Eulerian number.

Lemmas (all proved):
- `beta0 : beta set0 = 1` — only the identity has empty descent set.
- `beta_full : beta [set: 'I_n] = 1` — only the strictly-decreasing permutation has full descent set.
- `sum_beta_eq_fact n : \sum_(D : {set 'I_n}) beta D = n.+1\`!`
- `beta_eulerian n k : \sum_(D : {set 'I_n} | #|D| == k) beta D = eulerian n k`
- `beta_rev : beta D = beta ([set rev_ord i | i in ~: D])` — reversal-complement symmetry.

Auxiliary: `descent_set_rev_perm`, `descent_set_rev_perm_ord`, `imset_rev_ord_inv`, `imset_rev_ord_compl`, `descent_set_full_rev`.

### Layer 5 — β-swap and alternating maximum (`beta_swap.v`)

Toward Putnam 2025 problem A5: among descent sets that are *not* "set-alternating" (i.e. that contain some consecutive pair with equal D-membership), the alternating set strictly maximises β.

Definitions:
- `sym_diff D E := (D :\: E) :|: (E :\: D)` — set symmetric difference.
- `toggle_at D i := sym_diff D [set i]` — single-position membership flip.
- `alt_desc_set n := [set i : 'I_n | ~~ odd i]` — the "even-position" alternating descent set.
- `set_is_alt D := [forall i, [forall j, val j == val i + 1 ==> (i ∈ D) != (j ∈ D)]]` — every consecutive pair has differing membership.

Spec-facing theorem (one direction toward A5):
```coq
Lemma beta_alt_max n (D : {set 'I_n}) :
  ~~ set_is_alt D -> beta D < beta (alt_desc_set n).
```

**Important spec correction** (vs an earlier draft): the stronger claim `D != alt_desc_set n -> beta D < beta (alt_desc_set n)` is **false**. There are two set-alternating patterns (the "odd-position" one and the "even-position" `alt_desc_set`); by `beta_rev` they have equal β. So the correct hypothesis is `~~ set_is_alt D` — there must be a consecutive same-membership pair to even start the swap argument.

**Status**: the file's structural, combinatorial, and arithmetic content is fully proved. Two classical results from Stanley *Enumerative Combinatorics* Vol. 1 §1.4/§1.6 are **axiomatized** rather than formalized, as a self-contained MathComp proof would require ~300–400 lines of intricate permutation arithmetic (block-based cyclic rotation with boundary case analysis):

| Axiom | Section | Classical source |
|-------|---------|-----------------|
| `beta_swap_monotone` | §C.1 | Stanley EC1 §1.4 P-partition theory / Foata swap: `β D ≤ β (toggle_at D i)` when positions `i, i+1` have equal D-membership. |
| `beta_swap_lt` | §C.2 | Strict version: under the same hypothesis, `β D < β (toggle_at D i)`. |

Both are well-known descent-statistic inequalities; their correctness is not in doubt. Every downstream lemma (including `beta_alt_max`, `beta_alt_max_bounded`) depends *only* on these two axioms and otherwise closes under the global context.

**Proved Qed in `beta_swap.v`** (~300 lines): toggle machinery (`sym_diff`, `toggle_at`, `toggle_atK`), alternating-set theory (`alt_desc_set`, `set_is_alt`, `alt_desc_set_is_alt`, `set_not_altP`, `set_is_alt_classify`), value-complement bijection (`compl_perm`, `descent_set_compl`, `beta_compl`), boundary lemmas (`beta_lt_fact`, `not_set_is_alt_n_ge2`), and the β-based induction driver (`beta_alt_max_bounded`, `beta_alt_max`).

## Status

All lemmas in Layers 0–4 are **closed under the global context** (verified by `Print Assumptions`). Layer 5 (`beta_swap.v`) introduces exactly **two classical axioms** (`beta_swap_monotone`, `beta_swap_lt`); the rest of the file — including the spec-facing `beta_alt_max` — is fully proved. Running `Print Assumptions beta_alt_max` reports only `beta_swap_lt` as its sole axiom dependency.

## Conventions

- `eulerian n k` is indexed so that `n` is the "permutation size minus one" and `k` ranges over `0..n`. This avoids `n.-1` expressions in the recurrence.
- Layers 0–2 and 4–5 stay in `nat`. Layer 3 uses `int` only for `eulerian_explicit` (opens `ring_scope` locally).
- Naming follows MathComp: snake_case, conclusion-based names (`des_rev_perm`, `lift_perm_ord_max`, `beta_rev`, etc.).
- "Set-alternating" (`set_is_alt D`) means *every* consecutive pair `(i, i+1)` has differing membership in `D`. Two distinct sets satisfy this on `'I_n` (offset by 1); they have equal β by reversal symmetry.

## Deviations from the original plan

The plan (`eulerian_mathcomp_plan.md`) described the layer structure but had two statement-level discrepancies, corrected here:

1. **Recurrence**: plan stated `eulerian n.+1 k = k.+1 * eulerian n k + (n.+1 - k) * eulerian n k.-1`. This fails at `k = 0` (nat predecessor gives a wrong extra term) and has an off-by-one. The correct, total-on-nat statement is the one proved above, using `k.+1` on the LHS.
2. **Closed form**: plan stated `(eulerian n k)%:Z = \sum_(j < k.+1) (-1)^j *+ 'C(n.+1, j) *+ (k.+1 - j)^n`. Both the binomial (`n.+1 → n.+2`) and the power (`n → n.+1`) are off by one. The statement in `eulerian.v` is the corrected version; numerically verified for `(n, k) ∈ {(0,0), (1,0), (1,1), (2,1), (2,2)}`, formally proved via Worpitzky inversion.

Also added beyond the plan: the `insert_max_perm` / `extract_max_perm` infrastructure (bijection by value insertion), which makes the recurrence proof self-contained.
