> **Historical document.** Plan that designed the `mmtree_shape`
> Opaque-sealed Fixpoint refactor — collapse five repeated 3-way-split
> structural inductions into one shape-induction with thin corollaries.
> Successfully executed; lives in `psi_cdindex_tree_shape.v` plus thin
> wrappers in `psi_cdindex_tree_hlc.v` / `psi_cdindex_tree.v`.  Both
> files now compile cleanly to `.vo`.  See [`README.md`](README.md).

# Plan: Refactor mmtree proofs for -vo compilation

## Problem

Two files (`psi_cdindex_tree_hlc.v`, `psi_cdindex_tree.v`) OOM at ~131GB
during -vo compilation. The root cause: five structural lemmas each prove
order-isomorphism invariance independently, repeating the same 3-way case
split induction, generating exponentially large proof terms.

| Lemma | LOC | Pattern | Problem |
|-------|-----|---------|---------|
| `has_left_child_order_iso` | 76 | induction + 3-way split | huge proof term |
| `has_left_child_psi` | 154 | calls order_iso with 39-line forall body | exponential duplication |
| `endpoint_implies_next_has_left_child` | 85 | induction + 3-way split | same pattern |
| `window_size_last_fuel` | 32 | induction | moderate |
| `LR_pred_is_endpoint` | 137 | induction + 3-way split | same pattern |

These proofs all say the same thing: "this property depends only on the
relative order of elements, so it's preserved by order-isomorphisms (and
hence by psi)." But each re-proves this from scratch.

## Key insight

Every mmtree property (mm_pos, window_size, has_left_child, is_internal,
classify_vertex_cde) is determined by the **tree shape** — the sequence of
mm_pos values at each level of the recursive decomposition. Two sequences
with the same relative order produce the same tree shape.

## New strategy: prove tree-shape invariance ONCE

### Step 1: Define the tree shape

The tree shape captures the mm_pos choices at each recursion level:

```coq
Fixpoint mmtree_shape_fuel (fuel : nat) (s : seq nat) : seq nat :=
  match fuel with
  | 0 => [::]
  | fuel'.+1 =>
      match s with
      | [::] => [::]
      | _ =>
          let j := mm_pos s in
          j :: mmtree_shape_fuel fuel' (take j s)
            ++ mmtree_shape_fuel fuel' (drop j.+1 s)
      end
  end.
Definition mmtree_shape s := mmtree_shape_fuel (size s) s.
```

This is a flat encoding of the tree structure: the root mm_pos, followed
by the left subtree's shape, followed by the right subtree's shape. Two
sequences have the same mmtree_shape iff they have the same min-max tree
(ignoring labels).

### Step 2: Prove tree shape is order-isomorphism invariant

```coq
Lemma mmtree_shape_order_iso s1 s2 :
  size s1 = size s2 -> uniq s1 -> uniq s2 ->
  (forall p q, p < size s1 -> q < size s1 ->
    (nth 0 s1 p < nth 0 s1 q) = (nth 0 s2 p < nth 0 s2 q)) ->
  mmtree_shape s1 = mmtree_shape s2.
```

**This is the ONE heavy proof.** It uses strong induction on size with
the 3-way case split at mm_pos. The key sub-lemma (already proved in
psi_core.v): `mm_pos_order_iso` — order-isomorphic sequences have the
same mm_pos. Then the induction decomposes both sequences at mm_pos and
applies the IH to the left and right subtrees.

Expected: ~100 LOC, one 3-way case split, proof term ~10-20GB for -vo.

### Step 3: Prove each property depends only on tree shape

These are NOT inductive — they just unfold the definitions and show that
has_left_child, window_size, etc. recurse using mm_pos (which is the
first element of mmtree_shape at each level).

```coq
Lemma has_left_child_of_shape s1 s2 i :
  size s1 = size s2 ->
  mmtree_shape s1 = mmtree_shape s2 ->
  has_left_child i s1 = has_left_child i s2.
```

**Why no induction?** Both has_left_child and mmtree_shape recurse
using mm_pos. If mmtree_shape s1 = mmtree_shape s2, then mm_pos s1 =
mm_pos s2 (it's the head of the shape). The recursion step follows the
same path in both sequences, so the result is the same at each level.

Wait — this DOES need induction (on fuel), but each step is a trivial
`congr` from the head of mmtree_shape. No case splits, no order-iso
reasoning. The proof term is tiny (~5 LOC).

Similarly for window_size:

```coq
Lemma window_size_of_shape s1 s2 i :
  size s1 = size s2 ->
  mmtree_shape s1 = mmtree_shape s2 ->
  window_size i s1 = window_size i s2.
```

And for is_internal and classify_vertex_cde (which are defined in terms
of has_left_child and window_size).

### Step 4: Derive psi-invariance as one-line corollaries

```coq
Lemma has_left_child_psi j i w :
  uniq w -> has_left_child i (psi j w) = has_left_child i w.
Proof.
move=> Hu.
apply: has_left_child_of_shape; first by rewrite size_psi.
apply: mmtree_shape_order_iso;
  [by rewrite size_psi | exact: uniq_psi | exact: Hu |].
exact: psi_preserves_order.  (* already essentially proved *)
Qed.
```

Each corollary is ~5 LOC with a tiny proof term.

### Step 5: Prove endpoint/LR lemmas

`endpoint_implies_next_has_left_child` and `LR_pred_is_endpoint` are
about the tree STRUCTURE, not about order-isomorphism. They say:
"endpoints are followed by D-vertices" and "the predecessor of the
left-right boundary is an endpoint."

These might still need induction on the tree structure, but they DON'T
need order-isomorphism reasoning. They should produce smaller proof
terms because they operate on a SINGLE sequence, not a pair.

If they're still too large, they can use the mmtree_shape to decompose
the argument.

## Expected result

| Component | LOC | Proof term | -vo memory |
|-----------|-----|------------|------------|
| mmtree_shape definition | 20 | trivial | <1GB |
| mmtree_shape_order_iso | 100 | moderate (one 3-way split) | ~10-20GB |
| has_left_child_of_shape | 10 | tiny | <1GB |
| window_size_of_shape | 10 | tiny | <1GB |
| has_left_child_psi | 5 | tiny | <1GB |
| window_size_psi | 5 | tiny | <1GB |
| endpoint_implies_next... | 50 | moderate | ~5GB |
| LR_pred_is_endpoint | 80 | moderate | ~5GB |
| **Total** | **~280** | | **~20-30GB** |

vs. current: ~550 LOC, >131GB.

## Why this works

1. **One heavy proof instead of five.** The 3-way case split induction
   is done ONCE in mmtree_shape_order_iso. All derived results are
   trivial corollaries.

2. **No proof term duplication.** The current has_left_child_psi passes
   a 39-line forall body to has_left_child_order_iso, which gets
   duplicated at every recursive IH application. The new approach passes
   `mmtree_shape_order_iso` by NAME — a constant-size reference.

3. **Separation of concerns.** The tree shape captures ALL structural
   information. Properties don't need to re-derive the structure —
   they just read it from the shape.

## What needs to exist first

1. `mm_pos_order_iso` — already proved in psi_core.v
2. `psi_preserves_order` — essentially proved (rank_shift_preserves_
   interior_order in psi_comm.v), may need a clean wrapper
3. `take/drop` preserve order-isomorphism — straightforward

## Implementation plan

1. Create `psi_cdindex_tree_shape.v` (~130 LOC):
   - mmtree_shape definition
   - mmtree_shape_order_iso (the one heavy proof)
   - has_left_child_of_shape, window_size_of_shape (trivial)

2. Rewrite `psi_cdindex_tree_hlc.v` (~50 LOC, down from 253):
   - has_left_child_psi as 5-line corollary
   - (has_left_child_order_iso becomes unnecessary — or stays as a
     trivial corollary of of_shape + order_iso)

3. Keep `psi_cdindex_tree.v` (~200 LOC, down from 329):
   - endpoint_implies_next_has_left_child (may simplify)
   - LR_pred_is_endpoint (may simplify)

4. Update imports and _CoqProject.

## Risk assessment

| Risk | Mitigation |
|------|------------|
| mmtree_shape_order_iso still too large | It's ONE proof instead of 5; if needed, wrap in abstract |
| has_left_child_of_shape needs more than congr | May need induction on fuel, but no case splits |
| endpoint/LR lemmas still large | They don't use order-iso, so they should be smaller independently |
| Circular dependencies | mmtree_shape only depends on mm_pos (in psi_core.v) |
