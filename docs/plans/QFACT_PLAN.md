# Plan: `qfact.v` — q-factorial generating function

> **Forward-looking design document.** Phase 5 of the §1.3 extension.
> Optional in the original `INVERSIONS_PLAN.md`; revisited after
> Phases 1-4 landed.

## 1. Goal

Stanley EC1 Cor 1.3.10 / §1.3.4: the q-factorial identity

```
∑_(σ ∈ S_{n+1}) q^(inv σ) = [n+1]_q!
∑_(σ ∈ S_{n+1}) q^(maj σ) = [n+1]_q!
```

where `[k]_q := 1 + q + q² + ... + q^(k-1)` and
`[n+1]_q! := [1]_q · [2]_q · ... · [n+1]_q`.

Combined with `inv_maj_equidistr` (already proven), the second
identity is automatic from the first. So the substantive new content
is the inv-side identity.

## 2. Polynomial setup

Use mathcomp's `poly` library over `int`:

```coq
From mathcomp Require Import all_ssreflect ssrint ssralg poly.
Import GRing.Theory.
Open Scope ring_scope.

Definition q_int n : {poly int} := \sum_(i < n) 'X^i.
Definition q_fact n : {poly int} := \prod_(k < n.+1) q_int k.+1.
```

Note: `'X` is the indeterminate; `'X^i` is `'X` to the `i`-th power.

## 3. Headline theorem

```coq
Theorem inv_q_fact n :
  \sum_(σ : {perm 'I_n.+1}) 'X^(inv σ) = q_fact n.
```

Combined with `inv_maj_equidistr`:

```coq
Theorem maj_q_fact n :
  \sum_(σ : {perm 'I_n.+1}) 'X^(maj σ) = q_fact n.
```

## 4. Strategy: induction via "insert max" bijection

Use the same bijection as `eulerian_rec` in `eulerian.v` —
`insert_max_perm` / `extract_max_perm` from §H of that file —
which already gives `S_{n+2} ≃ S_{n+1} × 'I_{n+2}`.

Key fact: when inserting `ord_max` at position `p` in
`τ ∈ S_{n+1}`, the resulting perm has
`inv (insert_max_perm τ p) = inv τ + (n+1 - p)`.

This is because `ord_max` is the largest element, so inversions
involving it are exactly the elements appearing AFTER it in the
seq representation, i.e., `n+1 - p` of them.

Then:
```
∑_(σ ∈ S_{n+2}) q^(inv σ)
  = ∑_(τ ∈ S_{n+1}) ∑_(p ∈ 'I_{n+2}) q^(inv τ + n+1 - p)
  = (∑_(τ ∈ S_{n+1}) q^(inv τ)) · (∑_(p ∈ 'I_{n+2}) q^(n+1 - p))
  = q_fact n · [n+2]_q          (by IH and reindexing)
  = q_fact n.+1.                  (by definition of q_fact)
```

## 5. Required helpers

- **Insertion-and-inversion lemma**:
  ```coq
  Lemma inv_insert_max n (τ : {perm 'I_n.+1}) (p : 'I_n.+2) :
    inv (insert_max_perm τ p) = inv τ + (n.+1 - val p).
  ```
  Probably the trickiest piece. ~50-80 LOC.

- **Reindexing lemma** for `[n+2]_q`:
  ```coq
  Lemma sum_rev_X n :
    \sum_(p < n.+2) 'X^(n.+1 - val p) = q_int n.+2.
  ```
  ~10 LOC via `reindex` over `rev_ord`.

- **Big-sum-product identity**:
  ```coq
  \sum_(τ in S) \sum_(p in T) f τ * g p
    = (\sum_(τ in S) f τ) * (\sum_(p in T) g p).
  ```
  Standard mathcomp manipulation via `big_distrlr` / `big_distrl`.

## 6. Estimated effort

| Section | LOC | Difficulty |
|---------|-----|------------|
| poly imports + q_int / q_fact defs | ~20 | trivial |
| `inv_insert_max` | ~80 | medium-high |
| `sum_rev_X` reindex | ~10 | low |
| `inv_q_fact` main induction | ~60 | medium |
| `maj_q_fact` corollary | ~20 | low (uses equidistr) |
| **Total** | **~190 LOC** | |

Less than `foata.v` because we get to leverage existing
infrastructure (`insert_max_perm`, `inv_maj_equidistr`, mathcomp
poly).

## 7. Risks

1. **Poly imports.** `'X` notation requires `Open Scope ring_scope`
   plus `Import GRing.Theory`. Watch for scope conflicts with
   existing `nat` operators in `inversions.v`.

2. **`inv (insert_max_perm τ p) = inv τ + (n+1 - p)`** is the only
   really new content. The proof needs:
   - For each pair (i, j) with i < j in the new perm:
     - if neither is `p` (or, the position of `ord_max`): inversion
       inherited from τ.
     - if one is `p`: pair (p, j) for j > p, with `ord_max > σ(j)`,
       so always inversion → contributes (n+1-p) inversions.
     - if (i, p) for i < p: not an inversion (σ(p) = ord_max > σ(i)).
   This is bookkeeping but tractable.

3. **mathcomp poly idioms.** `'X^k` vs `('X^+ k)` etc. Stick with
   `'X^k` and the `polyseq`-based reasoning if needed.

## 8. Once `inv_q_fact` lands

- Add `qfact.v` to `_CoqProject`.
- Add a §"q-factorial" subsection to `ch_inversions.tex` blueprint
  with the `\rocq{...}` references.
- Mark Phase 5 complete in `INVERSIONS_PLAN.md`.

This closes the §1.3 extension formally — every classical statistic
identity from Stanley §1.3 is then kernel-checked.
