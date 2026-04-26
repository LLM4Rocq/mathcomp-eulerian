# mathcomp-eulerian

A MathComp 2.5+ / Rocq 9.0 formalization of permutation **descent statistics** and **Eulerian numbers**. Four layers, each independently useful.

## Build

```
make            # builds all four .v files
```

Dependencies: Rocq ≥ 9.0 and MathComp ≥ 2.5 (`all_ssreflect`, `fingroup`, `perm`, `binomial`, `ssrint`, `ssralg`).

## File structure

```
ordinal_reindex.v  →  perm_compress.v  →  descent.v  →  eulerian.v
```

| File | Lines | Contents |
|------|-------|----------|
| `ordinal_reindex.v` | 54 | Monotonicity of `lift`/`unlift` on `'I_n` |
| `perm_compress.v` | 115 | `drop_perm` / `lift_perm` bijection on `{perm 'I_n}` |
| `descent.v` | 122 | Descent set, descent/ascent counts, reversal symmetry |
| `eulerian.v` | 612 | Eulerian numbers: base cases, recurrence, symmetry, Worpitzky |

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

## Status

All lemmas in Layers 0–3 are **closed under the global context** (verified by `Print Assumptions`), with one exception:

- `eulerian_explicit` (closed form `(eulerian n k)%:Z = \sum_(j < k.+1) (-1)^j *+ 'C(n.+2, j) *+ (k.+1 - j)^n.+1`) — stated but **`Admitted`**. Proof outline (in the file) is by Worpitzky inversion: the key intermediate lemma is `aux_id`, the "alternating Vandermonde" identity `\sum_(j < n.+3) (-1)^j *+ 'C(n.+2, j) *+ 'C(t - j, n.+1) = (t == n.+1)%:Z`, whose inductive step on `n` requires two applications of Pascal's rule.

## Conventions

- `eulerian n k` is indexed so that `n` is the "permutation size minus one" and `k` ranges over `0..n`. This avoids `n.-1` expressions in the recurrence.
- Layers 0–2 stay in `nat`. Layer 3 uses `int` only for `eulerian_explicit` (opens `ring_scope` locally).
- Naming follows MathComp: snake_case, conclusion-based names (`des_rev_perm`, `lift_perm_ord_max`, etc.).

## Deviations from the original plan

The plan (`eulerian_mathcomp_plan.md`) described the layer structure but had two statement-level discrepancies, corrected here:

1. **Recurrence**: plan stated `eulerian n.+1 k = k.+1 * eulerian n k + (n.+1 - k) * eulerian n k.-1`. This fails at `k = 0` (nat predecessor gives a wrong extra term) and has an off-by-one. The correct, total-on-nat statement is the one proved above, using `k.+1` on the LHS.
2. **Closed form**: plan stated `(eulerian n k)%:Z = \sum_(j < k.+1) (-1)^j *+ 'C(n.+1, j) *+ (k.+1 - j)^n`. Both the binomial (`n.+1 → n.+2`) and the power (`n → n.+1`) are off by one. The statement in `eulerian.v` is the corrected version; verified numerically for `(n, k) ∈ {(0,0), (1,0), (1,1), (2,1), (2,2)}`.

Also added beyond the plan: the `insert_max_perm` / `extract_max_perm` infrastructure (bijection by value insertion), which makes the recurrence proof self-contained.
