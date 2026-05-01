# Milestone 2: The operators ψᵢ on min-max trees (informal proof note)

**Source of truth.** Stanley, *Enumerative Combinatorics* vol. 1 (2nd ed.), §1.6.3,
pp. 57–60 of the PDF extract in `refs/stanley_1_6_cdindex.txt`. Specifically:
- definition of `M(w)` : lines 196–203;
- definition of ψᵢ     : lines 204–233;
- Fact #1 (commuting involutions) : lines 234–238 — **out of M2 scope; that is M3**.

**Goal of M2.** Define ψᵢ, prove (a) well-definedness as a relabelling (same
multiset of labels), (b) involutivity ψᵢ ∘ ψᵢ = id, (c) a non-triviality
`Example`. This note targets ~200 LOC of MathComp.

**Non-goals (deferred to M3/M4).** Commutativity ψᵢ ψⱼ = ψⱼ ψᵢ; the descent-set
effect of ψᵢ (Fact #2); anything about β or the cd-index.

---

## 1. Setup: the min-max tree and its alternation rule

### 1.1 Stanley's construction (authoritative)

Let `w = a₁ a₂ ⋯ aₙ` be a sequence of **distinct** integers.

> (Stanley lines 197–200.) Let `j` be the least integer for which either
> `aⱼ = min{a₁, …, aₙ}` or `aⱼ = max{a₁, …, aₙ}`. Define `aⱼ` to be the root of
> `M(w)`. Then define (recursively) `M(a₁, …, a_{j−1})` to be the left subtree
> of `aⱼ`, and `M(a_{j+1}, …, aₙ)` to be the right subtree.

Two structural facts drop out (Stanley lines 201–203):

- **(F1)** no vertex has *only* a left child;
- **(F2)** every vertex `v` is either the minimum *or* the maximum of the
  subtree rooted at `v`.

Call a vertex a **min-vertex** if it is the minimum of its subtree, a
**max-vertex** if it is the maximum. Every internal vertex has a well-defined
type. (Leaves / single-vertex subtrees are both, but for ψᵢ the ambiguity
never matters — endpoints are fixed by ψᵢ, Stanley line 208.)

Note that `min` vs `max` is *not* a fixed-per-depth alternation the way a
treap's heap property is. It is per-subtree: the root picks whichever of
min/max occurs *first* in `w`. Children inherit the opposite kind only
when forced. Concretely (Stanley's example, lines 216–222):

> `M(5, 10, 4, 6, 7, 2, 12, 1, 8, 11, 9, 3)`

The global maximum `12` is the first extremum (position 7), so it becomes the
root and is a **max**-vertex. The left subtree is `M(5, 10, 4, 6, 7, 2)`;
inside that, `2` is its global min and appears before `10` (its global max),
so `2` becomes the root of the left subtree, a **min**-vertex. And so on.
In general min-vertices and max-vertices interleave irregularly.

### 1.2 The "i-th internal vertex"

The operators ψᵢ are indexed by `i ∈ {1, …, n}`, where `i` refers to the
vertex **labelled `aᵢ`** (Stanley lines 206–208). Because `M(w)` is a binary
tree whose *in-order traversal* reproduces `w` (this is the round-trip
`mmtree_of_seqK` of Milestone 1), the vertex labelled `aᵢ` is exactly the
`(i−1)`-th vertex visited in in-order (0-indexed) — equivalently, the vertex
whose in-order position is `i−1`. Inside MathComp we index from 0, so we
treat ψᵢ with `i : nat` meaning "the vertex at in-order position `i`", with
`0 ≤ i < n`.

**Critical note (docs/internal/AXIOMS_TODO.md §5, item 1).** The i-th internal vertex in the
in-order word sits at position `i`, not `2i`. Do not reintroduce the `2*i`
mistake from the discarded scaffolding.

### 1.3 Compatibility with `mmtree.v` (Milestone 1)

`mmtree.v` implements `mmtree_of_seq` with a *single* rule at every recursive
step: split at the **least index of the minimum**. This was acceptable for
M1, whose only obligation was `mmtree_of_seqK : mmtree_to_seq ∘ mmtree_of_seq
= id`, and that round-trip holds for *any* choice of split index as long as
the recursion uses `take j s ++ aⱼ :: drop j.+1 s = s`. See the comment block
at lines 17–21 of `mmtree.v`.

For M2 we need Stanley's genuine min/max-alternating construction, because
`ψᵢ`'s action is *defined in terms of* the type (min vs max) of the vertex
`aᵢ`. So M2 must introduce the alternating rule. We have two options:

**Option A (preferred).** Keep `mmtree.v` untouched. In a new file `psi.v`,
define a *Stanley-correct* `mmtree_of_seq_mm : seq nat → mmtree nat` that
splits at the first-min-or-max index. All of M2's theorems use
`mmtree_of_seq_mm` (not `mmtree_of_seq`). The M1 round-trip machinery
(`cat_take_drop`, `drop_nth`, fuel bound) carries over verbatim because the
split index is still `< size s`.

**Option B.** Edit `mmtree.v` to use the alternating rule. This changes the
M1 API, possibly silently breaks dependent work. **Do not do this.** The
brief explicitly forbids it.

We adopt Option A. Henceforth `M(w)` refers to the tree produced by the
first-min-or-max rule. When writing Rocq code the function is called
`mmtree_of_seq_mm`; informally we continue to write `M(w)`.

### 1.4 The extremum rule for split

Define

    mm_pos : seq nat → nat
    mm_pos s := index (extremum s) s

where `extremum s` is the first element of `{min s, max s}` to occur in `s`,
i.e.

    let m := foldr minn (head 0 s) (behead s) in
    let M := foldr maxn (head 0 s) (behead s) in
    if index m s ≤ index M s then m else M

Then

    Fixpoint mmtree_of_seq_mm_fuel (fuel : nat) (s : seq nat) : mmtree nat :=
      match fuel, s with
      | 0, _       => Leaf
      | _, [::]    => Leaf
      | S k, _::_  =>
          let j := mm_pos s in
          Node (mmtree_of_seq_mm_fuel k (take j s))
               (nth 0 s j)
               (mmtree_of_seq_mm_fuel k (drop j.+1 s))
      end.

    Definition mmtree_of_seq_mm s := mmtree_of_seq_mm_fuel (size s) s.

`mmtree_of_seq_mmK` (round-trip) is proved by the same recipe as
`mmtree_of_seq_fuel_correct` in `mmtree.v`, using `mm_pos_lt : s ≠ [::] →
mm_pos s < size s`, which follows from `index_mem` applied to the fact that
`min s ∈ s` and `max s ∈ s` (for nonempty `s`).

---

## 2. Definition of ψᵢ

### 2.1 Semi-formal restatement (Stanley lines 206–229)

Fix `w = a₁ ⋯ aₙ` distinct. Fix `i ∈ [n]`. Let `v` be the vertex of `M(w)`
labelled `aᵢ`. Let `R(v)` be the set of labels of the right subtree of `v`,
and let

    M_{aᵢ} := {aᵢ} ∪ R(v).

(Stanley's notation, line 209.) Then `aᵢ` is either the min or the max of
`M_{aᵢ}` (inherited from F2).

**Case A.** `v` is a leaf, i.e. `R(v) = ∅`. Then ψᵢ acts as the identity
(Stanley line 208–209).

**Case B.** `aᵢ = min M_{aᵢ}` (v is a min-vertex with a right child). Let
`b := max M_{aᵢ}` be the right-subtree maximum. Write the labels of
`M_{aᵢ}` in "relative order" — the sequence in which they appear along the
in-order traversal of `M_{aᵢ}`. This sequence starts with `aᵢ` (since `aᵢ`
is the root and the tree has no left child at `v` in its own subtree —
wait, it *may* have a left child globally but we are only looking at
`M_{aᵢ}` = `v` together with its right subtree).

Actually let us restate carefully using Stanley's exact wording (lines 210–
213):

> We denote by `M_{aᵢ}` the subtree of `M(w)` consisting of `aᵢ` and the
> right subtree of `aᵢ`. Thus `aᵢ` is either the minimum or the maximum
> element of `M_{aᵢ}`. Suppose that `aᵢ` is the minimum element of `M_{aᵢ}`.
> Then replace `aᵢ` with the largest element of `M_{aᵢ}`, and permute the
> remaining elements of `M_{aᵢ}` so that they keep their same relative order.

"Keep their same relative order" means: read off the old labels of `M_{aᵢ}`
in in-order as a sequence `x₀, x₁, …, x_k` (here `x₀ = aᵢ` because `v` has
no left child *within* `M_{aᵢ}` — the left child of `v` in the full tree is
outside `M_{aᵢ}`). Form the *sorted-by-position* sequence of the new label
set `{b} ∪ (R(v) ∪ {aᵢ} ∖ {b})`. Since we're swapping `aᵢ ↔ b`:

1. The new multiset of labels on `M_{aᵢ}` is `(R(v) ∪ {aᵢ}) ∖ {b} ∪ {b}
   = R(v) ∪ {aᵢ}` — same as before (just permuted).
2. Concretely: sort the new labels in the order `b < (R(v) ∖ {b}) ∪ {aᵢ}`
   where the elements other than `b` keep their old position-order.

**Reformulation (clearest for formalization).** Let
`L = [x₀; x₁; …; x_k] = mmtree_to_seq(M_{aᵢ})`, so `x₀ = aᵢ`.
Let `j` be the in-order position of the maximum in `L` (in Case B).
Then `ψᵢ` replaces `L` by `L'` where

    L' = [x_j; x_1; …; x_{j-1}; x_0; x_{j+1}; …; x_k]

i.e. swap positions `0` and `j`. Then rebuild `M_{aᵢ}` from `L'` using the
min-max tree construction **restricted to that subtree** — but wait, we
don't have to rebuild: the *shape* of `M_{aᵢ}` is unchanged; only the
labels at positions `0` and `j` are swapped. This is because F2 says each
vertex of the new subtree is still a min or max of its subtree — and the
shape is a function of the label set only through F2, which is preserved by
swapping the global extremum with the root.

Actually one must verify that claim (shape-invariance). Stanley glosses
over it ("this defines ψᵢ M(w)"), but it is exactly what "permute the
remaining elements so that they keep their same relative order" is
shorthand for: we do **not** rebuild the tree; we just relabel. See §3 for
the justification.

**Case C.** `aᵢ = max M_{aᵢ}`. Symmetric: replace `aᵢ` with the minimum of
`M_{aᵢ}`; swap positions `0` and `j`, where now `j` is the in-order position
of the minimum of `L`.

### 2.2 Worked example (Stanley's, lines 225–233)

    w  = 5 10 4 6 7 2 12 1 8 11 9 3
    i  = 7,  so aᵢ = a₇ = 12
    v is a max-vertex (12 = max of whole tree; root; M_{12} = entire tree
       on the right of ... wait, let me redo: M_{a₇} is a₇ and its right
       subtree only).

Following Stanley's figure 1.11(a): the root of `M(w)` is `12` at position
7; its right subtree (Stanley line 217) has labels `{1, 3, 8, 9, 11}`. So
`M_{a₇} = {12, 1, 3, 8, 9, 11}` (six elements). `a₇ = 12` is the max. Case C
applies. Replace `12` with `1` (the min). The remaining elements `{3, 8, 9,
11, 12}` go into the *old* positions of `{1, 3, 8, 9, 11}` in the same
relative order:

- old in-order labels on `M_{a₇}`: `12, 1, 8, 11, 9, 3` (reading right
  subtree of root in Fig 1.11(a), with root first);
- new: swap `12 ↔ 1`, giving `1, 12, 8, 11, 9, 3`? No — Stanley says
  (lines 230–233): "The remaining elements 1, 3, 8, 9, 11 get replaced
  with 3, 8, 9, 11, 12 in that order."

That means: the *relative order* of the non-swapped labels is preserved, but
the *values* shift. Reading Stanley's Fig 1.11(b), the right subtree of `1`
(new root at position 7) has labels `3, 12, 11, 8` in in-order, whereas
before it had `1, 8, 11, 9, 3`. So the operation is *not* a plain
transposition at the label level — it is: "replace the root label with the
right-subtree extremum; then the old root label takes the place of that
extremum; no other swaps". Let me re-examine.

Old `M_{a₇}` in-order sequence (from Fig 1.11(a), reading 12 then its right
subtree in-order): `12, 1, 8, 11, 9, 3`. The max is `12` at position 0, the
min is `1` at position 1.

New `M_{a₇}` in-order sequence (from Fig 1.11(b)): `1, 3, 8, 9, 11, 12`?
Let me read Fig 1.11(b): root `1`, right subtree root `3`, with right
subtree `12, 11, 8`. In-order: left of 1 is empty (or, within M_{a₇}, we
ignore the left subtree of 1 because we started from position 7 = the
subtree rooted at the old 12 = now 1). So `mmtree_to_seq(M_{new a₇})` =
`1, ?, 3, ?, 12, ?, 11, 8, ?` — it's hard to read from ASCII.

Stanley's plain description wins: **swap `aᵢ` with the subtree extremum; the
rest retain their positions.** Old sequence `[12; 1; 8; 11; 9; 3]`; swap
positions `0` and `1` (since min `1` sits at position `1`); new sequence
`[1; 12; 8; 11; 9; 3]`. Full permutation: old `w =
5,10,4,6,7,2,12,1,8,11,9,3` → new `w' = 5,10,4,6,7,2,1,12,8,11,9,3`.

But Stanley reports `ψ₇ w = 5,10,4,6,7,2,1,3,9,12,11,8` (line 226). The
subsequence at positions 7..12 is `1,3,9,12,11,8` versus our
`1,12,8,11,9,3`. These disagree starting at position 8.

So ψᵢ is **not** a single label transposition. Re-read Stanley carefully
(lines 231–233):

> Vertex 12 is replaced by 1, the smallest vertex of the right subtree.
> The remaining elements 1, 3, 8, 9, 11 get replaced with 3, 8, 9, 11, 12
> in that order.

So the action is:

- **Labels of `M_{aᵢ}`** (a multiset of size `k+1`) get permuted by the
  cyclic-ish map: the root label `aᵢ` is replaced by the chosen extremum;
  and the *sorted* order of the other labels shifts by one. Specifically,
  listing `M_{aᵢ}`'s old labels in *sorted* order: `1 < 3 < 8 < 9 < 11 <
  12`. The root is `12` (the max). New root is `1` (the min). The remaining
  old labels `{1, 3, 8, 9, 11}` (i.e. all except the old max `12`), listed
  in sorted order, get *replaced* by `{3, 8, 9, 11, 12}` (all except the
  new min `1`), also in sorted order — meaning: the vertex that used to
  hold `1` now holds `3`; the vertex that used to hold `3` now holds `8`;
  etc.; the vertex that used to hold `11` now holds `12`.

This is a **rotation of labels within `M_{aᵢ}`**. Formally:

> **Case C (max-vertex).** Let `S = {aᵢ} ∪ R(v)`, `|S| = k+1`. Sort `S`
> increasingly: `s_0 < s_1 < ⋯ < s_k`, so `s_k = aᵢ`. The old labelling
> places, at each vertex `u ∈ M_{aᵢ}`, some `s_{π(u)}`. The new labelling
> places `s_{π(u) − 1 mod (k+1)}`. Equivalently: the *set* of labels used
> is unchanged (F2 preserved); each vertex's label gets "demoted" by one
> rank, with the maximum wrapping to the minimum.

Let's verify: old labels, by vertex (Fig 1.11(a) M_{12}):
- root v₇: 12 (rank 5),
- v₈: 1 (rank 0),
- v₉: 8 (rank 2),
- v₁₀: 11 (rank 4),
- v₁₁: 9 (rank 3),
- v₁₂: 3 (rank 1).

New ranks (subtract 1 mod 6): 4, 5, 1, 3, 2, 0. Labels: s_4 = 11, s_5 = 12,
s_1 = 3, s_3 = 9, s_2 = 8, s_0 = 1. In-order sequence: `11, 12, 3, 9, 8,
1`. But expected is `1, 3, 9, 12, 11, 8`. Does not match.

Let me re-read more carefully. Stanley says (lines 229–233): "replace aᵢ
with the smallest element of M_{aᵢ}, and permute the remaining elements so
that they keep their same **relative order**."

"Relative order" here almost certainly means: the vertices of `M_{aᵢ}`
other than the root `v` get the *sorted* new label-set `S ∖ {min S} = S ∖
{new root label}`, distributed *so as to keep their relative rank order*.
That is: if vertex `u ≠ v` previously held the k-th smallest label of
`M_{aᵢ}`, it now holds the k-th smallest label of `S ∖ {min S}`.

Verify with Stanley: old `M_{a₇}` labels sorted `1 < 3 < 8 < 9 < 11 < 12`.
Root v₇ holds `12` (largest). Other vertices' old ranks among `{1,3,8,9,
11,12}`: v₈=rank 0 (value 1), v₉=rank 2 (value 8), v₁₀=rank 4 (value 11),
v₁₁=rank 3 (value 9), v₁₂=rank 1 (value 3).

New root v₇ holds `1` (the smallest). Remaining new labels (i.e. `S ∖ {1} =
{3, 8, 9, 11, 12}`), distributed by *sorted rank order* to v₈, v₉, v₁₀,
v₁₁, v₁₂ according to their old ranks (rank `r` goes to rank `r` among the
new non-min labels, after deleting rank 0 from the old):

- v₈: old rank 0 → new rank 0 among `{3,8,9,11,12}` → value `3`.
- v₉: old rank 2 → new rank 2 → value `9`.
- v₁₀: old rank 4 → new rank 4 → value `12`.
- v₁₁: old rank 3 → new rank 3 → value `11`.
- v₁₂: old rank 1 → new rank 1 → value `8`.

In-order sequence of new `M_{a₇}`: `1, 3, 9, 12, 11, 8`. **Matches
Stanley.** So the rule is:

> **ψᵢ, clean formulation.** Let `S = labels(M_{aᵢ})`, `root = aᵢ`.
> Let `ρ = root_rank(S, aᵢ)` (rank of `aᵢ` in sorted `S`; for min-vertex
> `ρ = 0`, for max-vertex `ρ = |S| − 1`). Let `ρ'` be the opposite
> extreme (`|S| − 1` or `0`). For each non-root vertex `u`, let
> `r(u)` be its old rank. Then the new label at `u` is: the `r(u)`-th
> smallest element of `S ∖ {new root label}` — equivalently, if `ρ = 0`
> (min-vertex case) the "shifted up" labelling, if `ρ = |S|−1` (max-vertex
> case) the "shifted down" labelling, where only the delete/insert of
> extrema moves anything.

### 2.3 Concretely as a sequence operation

The in-order traversal of `M_{aᵢ}` has length `k+1`. Let `L = [x_0; x_1;
…; x_k]` with `x_0 = aᵢ`. The positions `0, 1, …, k` correspond to the
vertices (root, then right-subtree in in-order).

- **Min-vertex case (Case B).** `x_0 = min L`. Let `M = max L`, occurring
  at some position `p`. Among `L` \ `{x_0}` (i.e. `[x_1; …; x_k]`), the
  old ranks are `1, 2, …, k`. Replace `x_0` by `M`; replace each other
  `x_j` by "the old `x_j` with rank shifted *down* by 1" — i.e. each
  non-root vertex's label is replaced by the next-smaller label in `L`.
  Equivalently: in `L`, **remove** `x_0`, **prepend** `M`, and among the
  remaining vertices their labels shift down one rank.

  *Simpler equivalent statement.* Sort `L` as `ℓ_0 < ℓ_1 < ⋯ < ℓ_k`
  (so `ℓ_0 = x_0`, `ℓ_k = M`). For vertex at position `j > 0`, let
  `r_j ∈ {1, …, k}` be the rank of `x_j` in `L` (so `x_j = ℓ_{r_j}`).
  New label at position 0: `ℓ_k`. New label at position `j`:
  `ℓ_{r_j − 1}`.

- **Max-vertex case (Case C).** Symmetric: `x_0 = max L`, new root label is
  `ℓ_0 = min L`. For `j > 0` with old rank `r_j ∈ {0, …, k−1}`, new label
  at `j` is `ℓ_{r_j + 1}`.

Note both cases give **the same set of labels** as before; only the
assignment to vertices changes.

### 2.4 Lift to the whole word

Since ψᵢ acts trivially outside `M_{aᵢ}`, and `M_{aᵢ}`'s vertices occupy a
contiguous slice of in-order positions (because it is an in-order-connected
subtree rooted at `v`, and `v`'s right subtree immediately follows `v` in
in-order), ψᵢ acts on `w` by: fix positions `0, …, i−1`; on positions
`i, i+1, …, i + k` (where `k = |R(v)|`), apply the rank-shift above; fix
positions `i + k + 1, …, n − 1`.

**Out-of-range / edge conventions** (flagged per the brief):

- If `i ≥ n`, define `ψᵢ(w) := w`. (Out of range = identity.)
- If `aᵢ` is a leaf (`R(v) = ∅`), `M_{aᵢ} = {aᵢ}`, the construction is
  vacuously the identity. Stanley line 208–209 explicitly states this.
- If labels are not distinct, the "rank" is ambiguous. We work with
  `seq nat` and *assume* distinctness throughout the M2 theorems. A
  `uniq w` hypothesis will appear in the lemmas' statements (or we prove
  them unconditionally by being careful — see §6).

---

## 3. Lemma: same multiset of labels

**Lemma (multiset_psi).** `perm_eq (psi i w) w`.

**Proof.** By construction ψᵢ permutes the labels within the window
`[i, i+k]` (where `k+1` = size of `M_{aᵢ}`) and fixes the rest. Inside the
window, the rank-shift (Case B: `ℓ_k ℓ_{r_1−1} ℓ_{r_2−1} … ℓ_{r_k − 1}`;
Case C: symmetric) is a bijection from `{ℓ_0, …, ℓ_k}` to itself, because
it is a reindexing of the *same sorted list* `ℓ_0 < ⋯ < ℓ_k` by the
permutation

    σ : {0, …, k} → {0, …, k}
    σ(0) = k, σ(j) = r_j − 1 for j > 0    (Case B)

(and symmetric in Case C). That `σ` is a bijection follows because the
map `j ↦ r_j` is a bijection `{1, …, k} → {1, …, k}` (since the vertices
at positions `1, …, k` hold the `k` non-root old labels, each with a
distinct rank in `{1, …, k}` — this uses distinctness of labels). Then
`j ↦ r_j − 1` is a bijection `{1, …, k} → {0, …, k−1}`, and we complete
it by `0 ↦ k`, giving a bijection `{0, …, k} → {0, …, k}`. □

Formalization: via `perm_eq` of the windowed slice, combined with
`perm_eq_cat` to glue the unchanged prefix/suffix. MathComp has
`perm_sort` and `perm_eq_refl` ready to hand.

---

## 4. Lemma: involutivity

**Lemma (involutivity_psi).** `psi i (psi i w) = w`.

**Proof sketch.** Without loss of generality ψᵢ is non-trivial (the
identity case is immediate), so `aᵢ` is an internal non-leaf vertex with
right-subtree size `k ≥ 1`. Let the old window be `L = [ℓ_{π(0)}; ℓ_{π(1)};
…; ℓ_{π(k)}]` where `π` is the "rank permutation" of the window (it sends
in-order position to rank, i.e. `π(j) = r_j` in the notation of §2.3, with
`π(0) = 0` in Case B).

Apply ψᵢ once (Case B):
- new root rank: `k` (max);
- new non-root ranks: `π(j) − 1` for `j > 0`.

So the **new** rank permutation π' is: `π'(0) = k`, `π'(j) = π(j) − 1` for
`j > 0`. Note that for `j > 0`, `π(j) ∈ {1, …, k}`, so `π'(j) ∈ {0, …, k−1}`;
and `π'(0) = k`. So the *new* root's rank is `k` = max. That means the new
vertex `v` is a **max-vertex** of the new `M_{aᵢ}`. So a second application
of ψᵢ falls into Case C, not Case B.

Apply ψᵢ a second time (Case C, starting from π'):
- new-new root rank: `0` (min);
- new-new non-root ranks: `π'(j) + 1` for `j > 0`.

For `j > 0`: `π''(j) = π'(j) + 1 = (π(j) − 1) + 1 = π(j)`. And `π''(0) =
0 = π(0)`. So `π'' = π`, and since the sorted-label list `ℓ_0 < ⋯ < ℓ_k`
depends only on the *multiset* of labels (which §3 shows is preserved),
the new-new label at position `j` is `ℓ_{π''(j)} = ℓ_{π(j)}` = original
label.

Symmetric argument if we start in Case C.

Two things to verify in the Rocq proof:

1. The "shape of `M_{aᵢ}`" is unchanged under ψᵢ, so that "position `j` in
   `M_{aᵢ}`" refers to the same vertex before and after. This is evident
   because ψᵢ is defined as a label-swap on a fixed tree shape (Stanley
   line 229: "this defines ψᵢ M(w)"); in our formalization this is
   literally true because we implement `psi_tree` as a relabelling that
   does **not** call `mmtree_of_seq_mm` on the modified labels.

2. The transition Case B → Case C (root changes type after one ψᵢ). This
   is where "the min/max alternation *at depth* doesn't matter; what
   matters is the root's type, which flips under ψᵢ" shows up.

□

**Remark (why not a transposition).** If ψᵢ were a plain transposition of
`aᵢ` and the right-subtree extremum, involutivity would be trivial but the
*shape* F2 of `M_{aᵢ}` would break in general (the subtree rooted at the
extremum would no longer have its label as min-or-max). The rank-shift
formulation is precisely what keeps F2 intact — that's the content of
Stanley's phrase "keep their same relative order".

---

## 5. Non-triviality example

Take `w = [3; 1; 4; 1; 5; 9; 2; 6]` — wait, this has duplicates (`1`
twice), which our "distinct labels" assumption forbids. Amend to a
distinct-label variant:

    w = [3; 1; 4; 7; 5; 9; 2; 6]     (replace second 1 with 7)

Compute `M(w)` under the min-max rule:

- Whole `w`: min = 1 (at position 1), max = 9 (at position 5). First
  extremum is `1` at position 1. Root = `1`. Left subtree on `[3]`, right
  subtree on `[4; 7; 5; 9; 2; 6]`.

- Left `[3]`: single-vertex, root = `3`, leaf.

- Right `[4; 7; 5; 9; 2; 6]`: min = 2 (pos 4), max = 9 (pos 3). First is
  `9` at position 3. Root = `9`. Left subtree on `[4; 7; 5]`, right on
  `[2; 6]`.

  - `[4; 7; 5]`: min = 4 (pos 0), max = 7 (pos 1). First is `4` at pos 0.
    Root = `4`. Left = empty, right = `[7; 5]`.
    - `[7; 5]`: min 5 (pos 1), max 7 (pos 0). First is `7`. Root = `7`,
      left = empty, right = `[5]`.
      - `[5]`: leaf-root `5`.
  - `[2; 6]`: min 2 pos 0, max 6 pos 1. First is `2`. Root = `2`, left
    empty, right = `[6]`. `[6]` is leaf-root.

So `M(w)` has in-order: 3, 1, 4, 7, 5, 9, 2, 6 ✓ (round-trip).

**Pick `i = 5`** (0-indexed), which is the vertex labelled `a_5 = 9`.
`9` is the root of the right half; it is a **max-vertex** (max of its
subtree `{4,7,5,9,2,6}`). Its right subtree in-order is `[2; 6]`, and the
window `L = [9; 2; 6]` with sorted `ℓ_0 = 2 < ℓ_1 = 6 < ℓ_2 = 9`. Rank
permutation: `π(0) = 2`, `π(1) = 0`, `π(2) = 1`.

Apply ψ₅ (Case C, max-vertex): new root rank = 0 (= `ℓ_0 = 2`); for `j > 0`,
new rank = `π(j) + 1`. So `π'(0) = 0`, `π'(1) = 1`, `π'(2) = 2`. New window
labels: `[ℓ_0; ℓ_1; ℓ_2] = [2; 6; 9]`.

So `psi 5 w = [3; 1; 4; 7; 5; 2; 6; 9]`. Clearly ≠ `w`. ✓

**Double-check involutivity on this example.** Apply ψ₅ again. Now at
position 5 of the new word is `2`; its right subtree in the new tree… wait,
is the tree shape the same? Yes, ψᵢ preserves the shape. So the tree at
position 5 is still the node with right subtree of in-order size 2.
The new window is `[2; 6; 9]`, sorted identically. New root is `2`, which
is the **min** of the window — so we are in Case B. Apply Case B:
`π(0) = 0, π(1) = 1, π(2) = 2`; new ranks: `π'(0) = 2, π'(j) = π(j) − 1`
for `j > 0`, so `π'(1) = 0, π'(2) = 1`. New labels: position 0 → `ℓ_2 = 9`,
position 1 → `ℓ_0 = 2`, position 2 → `ℓ_1 = 6`. Window = `[9; 2; 6]`. This
matches the *original* window. ✓

**Formalizer's `Example`.** Something like:

    Example psi_nontrivial :
      psi 5 [:: 3; 1; 4; 7; 5; 9; 2; 6]
        = [:: 3; 1; 4; 7; 5; 2; 6; 9].
    Proof. by []. Qed.

    Example psi_involutive_ex :
      psi 5 (psi 5 [:: 3; 1; 4; 7; 5; 9; 2; 6])
        = [:: 3; 1; 4; 7; 5; 9; 2; 6].
    Proof. by []. Qed.

Both should reduce by `Compute`.

---

## 6. Formalization notes for the Rocq implementer

### 6.1 File layout

Create a new file `psi.v`. Do **not** modify `mmtree.v`. The imports are:

    From mathcomp Require Import all_ssreflect.
    Require Import mmtree.   (* for the mmtree inductive, Leaf, Node,
                                mmtree_to_seq, the fuel idiom *)

### 6.2 Step 1 — Stanley-correct tree construction

Redo the `mmtree_of_seq` recipe with the min-or-max split:

    Definition max_pos (s : seq nat) : nat :=
      index (foldr maxn (head 0 s) (behead s)) s.

    Definition mm_pos (s : seq nat) : nat :=
      if min_pos s <= max_pos s then min_pos s else max_pos s.

    Fixpoint mmtree_of_seq_mm_fuel fuel s : mmtree nat := ...
    Definition mmtree_of_seq_mm s := mmtree_of_seq_mm_fuel (size s) s.

Prove `mmtree_of_seq_mmK : mmtree_to_seq (mmtree_of_seq_mm s) = s` by
the exact same argument as `mmtree_of_seq_fuel_correct` in `mmtree.v`,
replacing `min_pos_lt` with `mm_pos_lt`. No new mathematical content;
this is a structural copy. **~30 LOC.**

### 6.3 Step 2 — locate the i-th vertex's right-subtree labels

Define a pure-tree function

    Fixpoint subtree_at (i : nat) (t : mmtree nat) : mmtree nat := ...

that returns the subtree rooted at the vertex at in-order position `i` of
`t`. For the M2 proof we also need the right subtree *only*:

    Definition right_subtree_at (i : nat) (t : mmtree nat) : mmtree nat :=
      match subtree_at i t with
      | Leaf        => Leaf
      | Node _ _ r  => r
      end.

`subtree_at` is defined by recursing with a size comparison against
`size (mmtree_to_seq l)` (the left subtree's in-order length): if `i <
size_left`, recurse left; if `i = size_left`, return the current node;
else recurse right with `i − size_left − 1`. **~20 LOC** including
correctness (the in-order position of the returned subtree's root is `i`
in the enclosing tree).

### 6.4 Step 3 — the extremum and the rank-shift

    Definition extremum_of_subtree (t : mmtree nat) (kind : bool) : nat :=
      (* kind = true → max, false → min *)
      if kind then foldr maxn 0 (mmtree_to_seq t)
              else foldr minn (head 0 (mmtree_to_seq t)) (behead (mmtree_to_seq t)).

    Definition root_kind (t : mmtree nat) : option bool :=
      (* Some true  if root = max of subtree;
         Some false if root = min;
         None       if t = Leaf. *)
      match t with
      | Leaf => None
      | Node _ x r =>
          let S := mmtree_to_seq (Node Leaf x r) in  (* = x :: labels(r) *)
          if x == foldr minn x (behead S) then Some false
          else if x == foldr maxn x (behead S) then Some true
          else None  (* unreachable when t = M_{aᵢ} for some w *)
      end.

    Definition rank_shift_seq (L : seq nat) (kind : bool) : seq nat :=
      (* L is the in-order of M_{aᵢ} (root first). kind = root type.
         Returns the new in-order labels. *)
      let sorted := sort leq L in
      let ranks  := [seq index x sorted | x <- L] in
      let shift  := if kind then (fun r => r.+1) else (fun r => r.-1) in
      (* Replace head-rank by the opposite extreme rank, others by shift. *)
      let new_ranks := (if kind then 0 else (size L).-1)
                         :: [seq shift r | r <- behead ranks] in
      [seq nth 0 sorted r | r <- new_ranks].

### 6.5 Step 4 — define ψᵢ on sequences

Do the splice directly on the sequence (easier than defining it on trees
and round-tripping):

    Definition psi (i : nat) (w : seq nat) : seq nat :=
      let t := mmtree_of_seq_mm w in
      let tsub := subtree_at i t in
      match tsub with
      | Leaf       => w                            (* i out of range: identity *)
      | Node _ _ Leaf => w                         (* endpoint: identity *)
      | Node _ x r =>
          let L := mmtree_to_seq tsub in          (* root :: right-in-order *)
          let kind := (* root_kind tsub, which is Some _ by F2 *) in
          let L' := rank_shift_seq L kind in
          take i w ++ L' ++ drop (i + size L) w
      end.

**Conventions (flagged per brief).**

- **Out-of-range `i`**: `subtree_at i t` returns `Leaf` when `i ≥ size w`;
  `psi` then returns `w`. Chosen because it keeps `psi i` total and
  involutive unconditionally.
- **Endpoint `aᵢ`**: returns `w`. This matches Stanley line 208: "if `aᵢ`
  is an endpoint then `ψᵢ M(w) = M(w)`." Involutivity is immediate.
- **Non-distinct labels**: `rank_shift_seq` uses `sort` and `index`, both
  of which are well-defined on duplicates but the rank permutation is no
  longer a bijection. We *state* the M2 theorems under `uniq w`.
  Alternative: prove `psi i w = w` when labels are non-distinct (this
  might follow from "the min-or-max index of the whole word is not well-
  defined in the non-uniq case, hence `mmtree_of_seq_mm` produces
  something that makes ψᵢ fix everything"). Not required for M2; leave
  as future work.

### 6.6 Step 5 — lemmas

Statements:

    Lemma psi_perm_eq i w : uniq w -> perm_eq (psi i w) w.

    Lemma psi_involutive i w : uniq w -> psi i (psi i w) = w.

    Example psi_nontrivial :
      psi 5 [:: 3; 1; 4; 7; 5; 9; 2; 6] = [:: 3; 1; 4; 7; 5; 2; 6; 9].

    Example psi_involutive_ex :
      psi 5 (psi 5 [:: 3; 1; 4; 7; 5; 9; 2; 6])
        = [:: 3; 1; 4; 7; 5; 9; 2; 6].

Proof strategy for `psi_perm_eq`:

- `take i w ++ L' ++ drop (i + size L) w` is a permutation of
  `take i w ++ L ++ drop (i + size L) w = w` because:
  - `L` and `L'` are permutations of each other (both equal to
    `perm sort (sort leq L)` — specifically, both index into `sort leq L`
    via bijective rank sequences);
  - `perm_cat2l`, `perm_cat2r` in MathComp lift this to the full sequence.
- The key technical lemma: `perm_eq (rank_shift_seq L kind) L` for any
  `uniq L`.

Proof strategy for `psi_involutive`:

- Compute `psi i w` = `w'`, then `psi i w'` = `w''`. The non-trivial part
  is showing `subtree_at i (mmtree_of_seq_mm w') = subtree_at i t`
  **with only the root label changed to the opposite extremum** (and the
  right subtree relabelled consistently). Two possible approaches:

  (a) *Syntactic*. Prove a lemma `mmtree_of_seq_mm_stable` saying that the
  *shape* of `mmtree_of_seq_mm w` depends only on the comparison pattern
  of `w`, and that ψᵢ preserves that pattern on the window (because it
  only permutes labels within an interval where the global min-or-max
  locations stay put). Then `mmtree_of_seq_mm (psi i w)` has the same
  shape as `mmtree_of_seq_mm w`.

  (b) *Semantic via `rank_shift_seq`*. Prove, at the level of
  `rank_shift_seq`, that `rank_shift_seq (rank_shift_seq L kind)
  (negb kind) = L`. This is the computational heart (§4 of this note
  spells it out). Combined with the "root-kind flips after one ψᵢ"
  lemma, this gives involutivity directly. **Strongly preferred.**

  Formally:

      Lemma rank_shift_involutive L kind :
        uniq L -> size L >= 2 ->
        rank_shift_seq (rank_shift_seq L kind) (negb kind) = L.

  Then prove the kind-flip: if `root_kind (Node _ x r) = Some kind`, then
  after applying `rank_shift_seq` once to the in-order of that subtree, the
  new root is the opposite extremum, so its `root_kind` is `Some (negb
  kind)`. Putting these together:

  - First ψᵢ reads `kind := root_kind tsub`, produces `L'`.
  - Second ψᵢ, applied to `psi i w`: `subtree_at i (mmtree_of_seq_mm
    (psi i w))` has **the same shape** as `subtree_at i (mmtree_of_seq_mm
    w)` — this is approach (a), needed as a sub-lemma — but with root
    label being the other extremum. So the new `kind` is `negb kind`,
    and `rank_shift_seq L' (negb kind) = L` by the involutivity of
    `rank_shift_seq`.
  - Therefore `psi i (psi i w) = take i w ++ L ++ drop (i + size L) w = w`.

  The shape-stability lemma (a) is the trickiest part. Rough statement:

      Lemma mmtree_shape_stable w w' :
        uniq w -> uniq w' -> perm_eq w w' ->
        (* w and w' agree in "comparison pattern" on every subinterval *)
        shape_eq (mmtree_of_seq_mm w) (mmtree_of_seq_mm w').

  But we only need a weaker statement: ψᵢ preserves the comparison
  pattern on the window (because it's a rank-preserving permutation inside
  the window), and the comparison pattern outside the window is unchanged
  because those labels are untouched. This is local and likely ~50–70 LOC.

### 6.7 LOC budget

| Piece | LOC |
|-------|-----|
| `mmtree_of_seq_mm` + round-trip | 30 |
| `subtree_at` + correctness | 20 |
| `rank_shift_seq` + `perm_eq` lemma | 30 |
| `rank_shift_involutive` | 40 |
| `psi` definition | 10 |
| `psi_perm_eq` | 15 |
| shape-stability sub-lemma (ψᵢ preserves split-patterns) | 40 |
| `psi_involutive` main theorem | 30 |
| two `Example`s | 6 |
| **Total** | **~220** |

This lines up with the "~200 LOC" target in docs/internal/AXIOMS_TODO.md §4 row 2.

### 6.8 Pitfalls to avoid (from docs/internal/AXIOMS_TODO.md §5)

- **No `2*i` indexing.** `subtree_at i` means "the vertex at in-order
  position `i`", period. The window in `psi` has size `size L = 1 +
  right_subtree_size`, which depends on the tree and is generally not 2.
- **Don't define `psi := id` or `psi_stanley := psi` as an alias.** The
  `Example psi_nontrivial` above is the contract: it must reduce by
  `by []` to the stated non-identity value. If it doesn't, something is
  wrong.
- **Don't stuff hypotheses into the *definition*** (cf. "Packaged-hypothesis
  bridges" in docs/internal/AXIOMS_TODO.md §5, item 2). `psi` should be a total function
  `nat → seq nat → seq nat`, with correctness conditions (`uniq`) appearing
  only in the *lemmas' statements*.
- **Don't weaken the involutivity lemma to a decidable-equality boolean
  that happens to be trivially `true`.** State `psi i (psi i w) = w`
  with `=` at type `seq nat`.

### 6.9 What is *not* part of M2

- Commutativity `psi i (psi j w) = psi j (psi i w)` (Fact #1, remaining
  half) — Milestone 3.
- The descent-set effect of ψᵢ (Fact #2) — Milestone 4.
- Any connection to `beta_swap.v` or `β(S)` — Milestones 5–7.

---

## 7. The four M2 deliverables (for the Rocq implementer)

The formalizer's `psi.v` must contain exactly these four items, with no
`Admitted` and no axioms:

1. **`Definition psi : nat -> seq nat -> seq nat`**, total, defined as
   described in §6.5 via `mmtree_of_seq_mm`, `subtree_at`, and
   `rank_shift_seq`. Conventions: identity when `i` is out of range or
   when `aᵢ` is an endpoint; for distinct-label inputs matches Stanley's
   Fig 1.11.

2. **`Lemma psi_perm_eq : forall i w, uniq w -> perm_eq (psi i w) w.`**
   ψᵢ preserves the multiset of labels.

3. **`Lemma psi_involutive : forall i w, uniq w -> psi i (psi i w) = w.`**
   ψᵢ is its own inverse.

4. **`Example psi_nontrivial : psi 5 [:: 3; 1; 4; 7; 5; 9; 2; 6] = [::
   3; 1; 4; 7; 5; 2; 6; 9].`** (and, optionally, a companion
   `psi_involutive_ex` that reduces by `by []`). Witnesses that ψ₅ is
   not the identity on this input and that our worked example of §5 is
   faithful.

Once these four items type-check under `rocq compile`, Milestone 2 is done
and Milestone 3 (commutativity, Fact #1) can begin using the same
infrastructure.

---

## Appendix A. Stanley line-reference index

| Claim | Stanley line(s) |
|-------|-----------------|
| `M(w)` recursive definition | 197–200 |
| No-left-only-child; every vertex is subtree-min-or-max (F1, F2) | 201–203 |
| ψᵢ permutes only `M_{aᵢ}` | 204–209 |
| Endpoints fixed by ψᵢ | 208–209 |
| Min-vertex case (replace by largest, keep relative order) | 210–213 |
| Max-vertex case (replace by smallest, keep relative order) | 213–215 |
| Worked example ψ₇ on Fig 1.11 | 225–233 |
| Fact #1 (commuting involutions) — **M3, NOT M2** | 234–238 |

## Appendix B. Differences between M1 (`mmtree.v`) and M2 (`psi.v`)

| Aspect | `mmtree.v` (M1) | `psi.v` (M2) |
|--------|-----------------|--------------|
| Split rule | `min_pos` (least index of minimum) | `mm_pos` (least index of min-or-max) |
| Round-trip theorem | `mmtree_of_seqK` | `mmtree_of_seq_mmK` |
| Used by | Nothing downstream yet | ψᵢ construction |
| Labels | `nat`, distinct or not | `nat`, distinct (for the M2 lemmas) |

M1 is **not** wrong; it is a simpler special case that is adequate for a
round-trip but not for the min-or-max-sensitive operators of §1.6.3. M2
introduces the full rule without touching M1, as Option A of §1.3.
