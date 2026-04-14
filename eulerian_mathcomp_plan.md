# Eulerian Numbers and Descent Statistics for MathComp

## Overview

This document describes a plan to formalize permutation descent statistics and Eulerian numbers in MathComp, following MathComp idioms (boolean reflection, `finType` infrastructure, `ssrnat`/`ssrint`, `fingroup` for `'S_n`). The development is structured in layers so that each layer is independently useful and upstreamable.

**Naming conventions** follow MathComp style: `snake_case`, lemmas named by conclusion shape (e.g., `des_rev`, `eulerian_symm`, `drop_perm_lift_permK`).

---

## Layer 0: Ordinal Reindexing (`ordinal_reindex.v`)

**Goal.** Clean wrappers around the "skip" and "collapse" maps on `'I_n`, which underpin all permutation compression/expansion.

### Definitions

| Name | Type | Description |
|------|------|-------------|
| `bump k` | `'I_n -> 'I_n.+1` | Inject skipping value `k : 'I_n.+1`. For `i < k`, maps `i ↦ i`; for `i ≥ k`, maps `i ↦ i+1`. |
| `unbump k` | `'I_n.+1 -> 'I_n` | Partial inverse: for `j < k`, maps `j ↦ j`; for `j > k`, maps `j ↦ j-1`. Undefined (or default) at `j = k`. |

### Key Lemmas

- `unbump_bump : forall k i, unbump k (bump k i) = i`
- `bump_unbump : forall k j, j != k -> bump k (unbump k j) = j`
- `bump_injective : injective (bump k)`
- `bump_strictmono : i < j -> bump k i < bump k j`
- `unbump_strictmono : j1 != k -> j2 != k -> j1 < j2 -> unbump k j1 < unbump k j2`
- `bump_image : [set bump k i | i : 'I_n] = [set j : 'I_n.+1 | j != k]`

### MathComp integration notes

- MathComp's `fintype.v` has `lift_ord` / `unlift_ord` for `option`-valued collapse. Our `unbump` is the total version restricted away from `k`. Check whether `widen_ord`, `cast_ord`, `lift_ord` suffice or if wrappers are needed.
- The `bump`/`unbump` pair should form a bijection between `'I_n` and `{j : 'I_n.+1 | j != k}`, provable via `card` + `injective`.
- Provide simp lemmas for interaction with `inord`, `cast_ord`, `lshift`, `rshift`.

---

## Layer 1: Permutation Compression and Expansion (`perm_compress.v`)

**Goal.** Given `σ : {perm 'I_n.+1}` with `σ ord_max = k`, produce `τ : {perm 'I_n}` (and vice versa). This is the core combinatorial engine for inductive arguments on `'S_n`.

### Definitions

| Name | Type | Description |
|------|------|-------------|
| `drop_perm k σ` | `σ ord_max = k -> {perm 'I_n}` | Remove last position, reindex: `τ i = unbump k (σ (bump ord_max i))`. |
| `lift_perm k τ` | `{perm 'I_n} -> {perm 'I_n.+1}` | Inverse: `σ i = if i == ord_max then k else bump k (τ (unbump ord_max i))`. |

### Key Lemmas

- `drop_perm_lift_permK : drop_perm k (lift_perm k τ) _ = τ`
- `lift_perm_drop_permK : lift_perm k (drop_perm k σ h) = σ`
- `lift_perm_last : (lift_perm k τ) ord_max = k`
- `lift_perm_ne_last : i != ord_max -> (lift_perm k τ) i != k`
- `drop_perm_ne_last : i != ord_max -> σ i != k` (consequence of injectivity)

### Proof strategy

Define `drop_perm` and `lift_perm` as raw functions `'I_n -> 'I_n`, prove injectivity, then use `perm_of_injective` to obtain `{perm 'I_n}`. The cancellation lemmas follow from `unbump_bump` / `bump_unbump`.

### MathComp integration notes

- `{perm T}` is `perm_type` in MathComp. Construction via `perm_of_injective` or the `Perm` constructor.
- Provide interaction lemmas with `support`, `pcycle`, `odd_perm`:
  - `odd_lift_perm`: sign of `lift_perm k τ` in terms of sign of `τ` and parity of `k`.
  - `support_drop_perm`, `support_lift_perm`.
- This layer is **independently useful** for any inductive argument on symmetric groups (e.g., cycle index, representation theory).

---

## Layer 2: Descent Set and Descent Number (`descent.v`)

**Goal.** Define the descent set, descent number, and ascent number of a permutation of `'I_n`.

### Definitions

```
Definition is_descent (n : nat) (σ : {perm 'I_n.+1}) (i : 'I_n) : bool :=
  σ (inord i) > σ (inord i.+1).

Definition descent_set (n : nat) (σ : {perm 'I_n.+1}) : {set 'I_n} :=
  [set i | is_descent σ i].

Definition des (n : nat) (σ : {perm 'I_n.+1}) : nat :=
  #|descent_set σ|.

Definition asc (n : nat) (σ : {perm 'I_n.+1}) : nat := n - des σ.
```

### Key Lemmas

- `des_le : des σ <= n`
- `des_add_asc : des σ + asc σ = n`
- `des_id : des (1 : {perm 'I_n.+1}) = 0` (identity has no descents)
- `des_rev_ord : des (rev_perm σ) = n - des σ` where `rev_perm σ i = rev_ord (σ (rev_ord i))`
- `des_max : des (rev_ord_perm) = n` (the decreasing permutation has all descents)

### Interaction with Layer 1

The crucial lemma connecting descents to compression:

```
Lemma des_drop_perm (σ : {perm 'I_n.+2}) (k : 'I_n.+2) (h : σ ord_max = k) :
  forall i : 'I_n, 
    is_descent (drop_perm k σ h) i = is_descent σ (widen_ord i).
```

That is: descents at interior positions `0, ..., n-1` of `σ` are preserved by compression. This follows from `unbump_strictmono`. The descent at position `n` (involving `σ(n)`) disappears since position `n` is removed.

Consequence:
```
Lemma des_drop_perm_card (σ : {perm 'I_n.+2}) (k : 'I_n.+2) (h : σ ord_max = k) :
  des (drop_perm k σ h) = 
    if is_descent σ (inord n) then (des σ).-1 else des σ.
```

---

## Layer 3: Eulerian Numbers (`eulerian.v`)

**Goal.** Define Eulerian numbers and prove their basic properties.

### Definition

```
Definition eulerian (n k : nat) : nat :=
  #|[set σ : {perm 'I_n.+1} | des σ == k]|.
```

Convention: `eulerian n k` counts permutations of `{0,...,n}` (i.e., `'I_n.+1`) with exactly `k` descents. So `k` ranges over `0..n`.

### Properties (in order of proof dependency)

#### 3.1 Base cases and bounds

- `eulerian_0_0 : eulerian 0 0 = 1`
- `eulerian_n_0 : eulerian n 0 = 1` (only the identity has 0 descents)
- `eulerian_n_n : eulerian n n = 1` (only the decreasing permutation has `n` descents)
- `eulerian_n_ge : n < k -> eulerian n k = 0`
- `eulerian_row_sum : \sum_(k < n.+1) eulerian n k = (n.+1)`!` (partition of `'S_{n+1}`)

**Proof of row sum:** Every `σ : {perm 'I_n.+1}` has some descent number in `0..n`, giving a partition of the full symmetric group. Use `card_partition` or direct `big_sum` + `card_setT`.

#### 3.2 Symmetry

```
Theorem eulerian_symm : eulerian n k = eulerian n (n - k).
```

**Proof:** The reversal-complement involution `σ ↦ rev_ord ∘ σ ∘ rev_ord` is a bijection on `'S_{n+1}` satisfying `des(rev σ) = n - des σ` (from Layer 2's `des_rev_ord`). Apply `card_bij`.

#### 3.3 Recurrence

```
Theorem eulerian_rec (n k : nat) :
  eulerian n.+1 k = k.+1 * eulerian n k + (n.+1 - k) * eulerian n k.-1.
```

**Proof strategy:**

1. **Fiber by last value.** Define
   ```
   F n k j := #|{σ : {perm 'I_n.+1} | des σ == k /\ σ ord_max == j}|.
   ```
   Then `eulerian n k = \sum_(j < n.+1) F n k j`.

2. **Biject each fiber.** For each `j`, the map `σ ↦ drop_perm j σ` bijects the fiber `F n.+1 k j` onto a union of fibers at level `n`. By `des_drop_perm_card`:
   - If position `n` is an ascent (`σ(n) < j`): then `des(drop σ) = k`, and the constraint on the compressed permutation is that its last value maps below `j` after reindexing.
   - If position `n` is a descent (`σ(n) > j`): then `des(drop σ) = k - 1`, and the constraint is that its last value maps at or above `j` after reindexing.

3. **Count via prefix/suffix sums.** The fiber decomposition gives:
   ```
   F(n+1, k, j) = (# of τ with k descents and τ(n-1) < j after reindex)
                 + (# of τ with k-1 descents and τ(n-1) ≥ j after reindex)
   ```

4. **Sum over j and telescope.** Summing `F(n+1, k, j)` over all `j`:
   - The prefix sum contribution yields `(k+1) * eulerian n k`.
   - The suffix sum contribution yields `(n+1-k) * eulerian n (k-1)`.

This is the most substantial proof (~500–700 lines).

#### 3.4 Closed form

```
Theorem eulerian_explicit (n k : nat) :
  (eulerian n k)%:Z = \sum_(j < k.+1) (-1)^j *+ 'C(n.+1, j) *+ (k.+1 - j)^n.
```

**Proof:** Induction on `n` using the recurrence. The signed sum requires working in `int`; state the theorem over `int` and derive the `nat` version where needed.

#### 3.5 Worpitzky's Identity

```
Theorem worpitzky (n x : nat) :
  x ^ n = \sum_(k < n) eulerian n k * 'C(x + k, n).
```

**Proof:** Induction on `n`, using the recurrence and binomial absorption identities.

---

## File Structure

```
mathcomp-eulerian/
├── ordinal_reindex.v    # Layer 0: bump/unbump on 'I_n
├── perm_compress.v      # Layer 1: drop_perm/lift_perm
├── descent.v            # Layer 2: descent set, des, asc
├── eulerian.v           # Layer 3: Eulerian numbers + properties
└── README.md
```

### Dependencies

```
ordinal_reindex.v        (depends on: ssrnat, fintype, tuple)
       |
       v
perm_compress.v          (depends on: + perm, fingroup)
       |
       v
  descent.v              (depends on: + bigop)
       |
       v
  eulerian.v             (depends on: + binomial, div)
```

---

## Estimated Effort

| Layer | Lines (est.) | Difficulty | Upstreamability |
|-------|-------------|------------|-----------------|
| 0: ordinal_reindex | 150–200 | Low | High — general `'I_n` toolkit |
| 1: perm_compress | 300–400 | Medium | High — induction on `'S_n` |
| 2: descent | 100–150 | Low | High — basic combinatorics |
| 3: eulerian (rec.) | 500–700 | High | High — named integer sequence |
| 3: eulerian (closed) | 200–300 | Medium | Medium |
| 3: Worpitzky | 150–200 | Medium | Medium |

**Total: ~1400–1950 lines.**

---

## Design Decisions

1. **Convention for `eulerian n k`.** `eulerian n k` counts permutations of `'I_n.+1` (that is, of `n+1` elements) with `k` descents. Then `k` ranges over `0..n` and the recurrence relates `eulerian n.+1 k` to `eulerian n`. This avoids `n.-1` expressions.

2. **`is_descent` is `bool`-valued.** This is standard MathComp practice and enables `#|[set i | is_descent σ i]|` directly without decidability side-conditions.

3. **`drop_perm` takes a proof `σ ord_max = k`.** This avoids partiality. The alternative — defining it for arbitrary `k` and proving it's only meaningful when `σ ord_max = k` — is less clean.

4. **No `int` in Layers 0–2.** Everything stays in `nat` until the closed form in Layer 3.4, which requires signed sums. This keeps the development lightweight.

5. **Upstream target.** Layers 0–1 are candidates for MathComp core (`mathcomp/fingroup/` or `mathcomp/ssreflect/`). Layers 2–3 fit `mathcomp-contrib` or a dedicated `mathcomp-combinatorics` package.
