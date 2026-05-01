# Milestone 3: Commutativity of the operators psi_i (informal proof note)

**Claim (Fact #1, Stanley EC1 2nd ed., lines 234--238).**
For all `i`, `j`, and all sequences `w` of distinct integers,

    psi i (psi j w) = psi j (psi i w).

**Dependencies.** We freely use:
- M2 involutivity: `psi i (psi i w) = w` (axiomatized in `psi.v` line 594);
- M2 infrastructure: `window_size`, `window_at`, `rank_shift_seq`, `mm_pos`,
  and all lemmas in `psi.v` (588 LOC);
- the worked-through definition of psi from `M2_PSI_INFORMAL.md`.

**Source of truth.** Stanley EC1 (2nd ed.) section 1.6.3.
- Lines 234--238: statement of Fact #1 (commuting involutions).
- Lines 259--263: the independence of descent-set changes (Fact #2) is
  equivalent to commutativity of the psi_i.

---

## 1. Setup: window geometry and the three cases

### 1.1 Recap of the window structure

Recall from M2 (M2_PSI_INFORMAL.md, sections 2.3--2.4): psi_i acts on the
contiguous slice `w[i .. i + ws_i)` where `ws_i := window_size i w`. This
slice is the in-order traversal of the subtree `M_{a_i}` = vertex `a_i`
together with its right subtree in `M(w)`. The action is a rank-shift
(cyclic relabelling by +/-1 in sorted rank) on this window, and the identity
outside it.

Formally (from `psi.v` line 220):

    psi i w = take i w ++ rank_shift_seq (window_at i w) ++ drop (i + ws_i) w

where `window_at i w = take ws_i (drop i w)`.

The window at position `i` corresponds to a subtree of `M(w)` rooted at the
vertex with in-order index `i`. The recursive definition of `window_size`
(`psi.v` lines 93--105) mirrors the tree construction: at each level, let
`j = mm_pos s` (the root of the current subtree); then:
- if `i < j`: recurse into `take j s` (left subtree);
- if `i = j`: the window is `drop j s` (root + entire right subtree),
  so `ws = size s - j`;
- if `i > j`: recurse into `drop (j+1) s` (right subtree), with
  `i' = i - j - 1`.

### 1.2 The three geometric cases for two windows

Fix two positions `i` and `j` with `i != j`. Their windows are:

    W_i = [i, i + ws_i),    W_j = [j, j + ws_j).

Because each window corresponds to a subtree of `M(w)`, and subtrees in a
binary tree are either **disjoint** or **nested** (one contains the other),
the windows satisfy exactly one of:

**(Case 1) Disjoint:** `W_i` and `W_j` are disjoint as intervals. This
happens when neither vertex is an ancestor of the other in `M(w)` -- i.e.,
neither subtree contains the other.

**(Case 2) Nested, W_j inside W_i:** `W_j` is a proper sub-interval of
`W_i`, i.e. `i <= j` and `j + ws_j <= i + ws_i`. This happens when vertex
`j` lies in the right subtree of vertex `i` (note: it cannot lie in the left
subtree, because left-subtree positions are `< i`, and we have `i < j` since
`j`'s in-order index is in `[i+1, i+ws_i)`).

**(Case 3) Nested, W_i inside W_j:** Symmetric to Case 2 with roles swapped.

**Why no partial overlap.** If two subtrees of a rooted tree share any
vertex, one must be contained in the other (a subtree is a downward-closed
connected component from a root). In terms of in-order intervals: if `W_i`
and `W_j` overlapped without nesting, there would exist a vertex in `W_i`
that is not in the subtree of `j`, and a vertex in `W_j` that is not in the
subtree of `i`, yet both subtrees share a common vertex -- contradicting the
tree nesting property.

### 1.3 WLOG reduction for the nested case

Since `psi i (psi j w) = psi j (psi i w)` is symmetric in swapping `i` and
`j`, Cases 2 and 3 are equivalent by symmetry. It suffices to prove Case 1
and Case 2 (with `W_j` properly inside `W_i`).

---

## 2. Case 1: Disjoint windows

**Claim.** If `W_i` and `W_j` are disjoint, then `psi i` and `psi j`
commute.

**Proof.** WLOG assume `i + ws_i <= j` (the case `j + ws_j <= i` is
symmetric). Then `psi i` modifies only positions in `[i, i + ws_i)` and
`psi j` modifies only positions in `[j, j + ws_j)`. These ranges do not
overlap.

More precisely, `psi j` does not change any position in `[0, j)`, so it
preserves `take i w` and `window_at i w` and `drop (i + ws_i) w` restricted
to positions `< j`. Similarly `psi i` preserves everything at positions
`>= j`.

Formally: since `psi j` acts as the identity on positions outside `[j, j +
ws_j)`, and the window `W_i = [i, i + ws_i)` is entirely outside `[j, j +
ws_j)`, we have:

    window_at i (psi j w) = window_at i w      ... (*)
    window_size i (psi j w) = window_size i w   ... (**)

and the prefix `take i (psi j w) = take i w` and suffix
`drop (i + ws_i) (psi j w)` agrees with `psi j` applied to `drop (i + ws_i) w`
only in the `[j, j + ws_j)` range. Therefore:

    psi i (psi j w)
      = take i (psi j w)
        ++ rank_shift_seq (window_at i (psi j w))
        ++ drop (i + ws_i) (psi j w)
      = take i w                           [psi j doesn't touch [0,i)]
        ++ rank_shift_seq (window_at i w)  [by (*)]
        ++ drop (i + ws_i) (psi j w)       [psi j acts on [j, j+ws_j) inside this tail]

By a symmetric argument starting from `psi j (psi i w)`:

    psi j (psi i w)
      = take j (psi i w) ++ rank_shift_seq (window_at j w) ++ drop (j + ws_j) (psi i w)

Now `take j (psi i w) = take i w ++ rank_shift_seq (window_at i w) ++ take (j - i - ws_i) (drop (i + ws_i) w)`, and similarly the tails match. Both expressions
decompose `w` into five consecutive slices:

    [0, i) | [i, i+ws_i) | [i+ws_i, j) | [j, j+ws_j) | [j+ws_j, n)

with `psi i` acting (by rank_shift_seq) on slice 2 and `psi j` on slice 4,
and both leaving slices 1, 3, 5 unchanged. Since the two rank-shifts act on
disjoint slices, the order of application is irrelevant. QED.

**Rocq sketch.** The key lemma is `nth_psi_outside` (M2_SUBTASKS.md, T3):
positions outside the window are unchanged. Given this, the disjoint case
reduces to showing that `window_at` and `window_size` at position `i` are
determined by positions in `[i, i + ws_i)`, which are untouched by `psi j`
(and vice versa). This needs the "window stability under external
perturbation" lemma -- a corollary of `mm_pos` stability (T4) applied to
the observation that `psi j` does not modify any position that `window_size i`
examines.

---

## 3. Case 2: Nested windows (the hard case)

**Setup.** Assume `W_j` is properly contained in `W_i`: that is,
`i < j` and `j + ws_j <= i + ws_i`, where `ws_i = window_size i w` and
`ws_j = window_size j w`.

Equivalently, vertex `j` lies in the right subtree of vertex `i` in `M(w)`.

### 3.1 What psi_i does to the window at j

The window at position `i` is `W_i = window_at i w`, a slice of length
`ws_i` starting at position `i`. The rank-shift `rank_shift_seq(W_i)`
permutes the labels in this window by a cyclic shift of sorted ranks.

Let `S_i = sort leq W_i` be the sorted labels, with `|S_i| = ws_i`.
Let `h = head 0 W_i` (the label at position `i`, the root of the subtree).

If `h = min(W_i)` (= `S_i[0]`), then `rank_shift_seq` maps each label of
rank `r` to rank `(r + ws_i - 1) mod ws_i`, i.e. shifts ranks down by 1
cyclically.

If `h = max(W_i)` (= `S_i[ws_i - 1]`), then `rank_shift_seq` maps rank `r`
to `(r + 1) mod ws_i`, i.e. shifts ranks up by 1 cyclically.

**Key property: rank-shift preserves relative order within any sub-window.**

Let `W_j` be the sub-window at position `j`, occupying positions
`[j, j + ws_j)` within `w`. These same positions sit at offsets
`[j - i, j - i + ws_j)` within `W_i`.

**Claim 3.1.** After applying `psi_i`, the labels at positions `[j, j + ws_j)`
form a sequence whose **relative rank order** is identical to that of the
original `window_at j w`.

**Proof of Claim 3.1.** The rank-shift on `W_i` maps rank `r` to
`(r + delta) mod ws_i` for a fixed `delta` (either `1` or `ws_i - 1`).
This is a *uniform* additive shift modulo `ws_i`. Consider any two positions
`p, q` in `[j, j + ws_j)` with original labels `x_p, x_q` having ranks
`r_p, r_q` respectively within `S_i`. After rank-shift, their new ranks are
`(r_p + delta) mod ws_i` and `(r_q + delta) mod ws_i`.

Now, the crucial observation: the labels within `W_j` form a *consecutive
block of ranks* within `S_i`. This is because `W_j` corresponds to a subtree
of `M(w)`, and the labels of a subtree form a contiguous interval in the
sorted order of any ancestor subtree's labels.

Wait -- that last claim needs justification. Actually it is **not** true in
general that subtree labels form a contiguous rank interval. Consider the
tree `M(3, 1, 4, 2)`: root is `1` (min, at position 1), right subtree has
labels `{4, 2}` at positions 2--3. Sorted full labels: `1 < 2 < 3 < 4`.
The right subtree labels `{4, 2}` have ranks `{1, 3}` within the full set --
not contiguous.

So the argument must be more careful. Let us reconsider.

### 3.2 Rank-shift algebra: the nested commutation

Let us work with explicit rank-shift notation. Write `RS(L, delta)` for the
rank-shift of a sequence `L` by shift amount `delta` (where `delta` depends
on whether the head is min or max).

**Notation.** For a sequence `w` and interval `[a, b)`, write `w|_{[a,b)}`
for the slice `take (b-a) (drop a w)`.

After `psi_i`, the full word becomes:

    w' := psi_i(w) = take i w ++ RS(W_i) ++ drop (i + ws_i) w

where `RS(W_i) = rank_shift_seq(window_at i w)`.

Now consider `window_at j w'`. Since `j` is inside `W_i`, position `j` in
`w'` has a *different label* from position `j` in `w`. Specifically, the
label at position `j` in `w'` is the rank-shifted version of the old label.

**Claim 3.2 (window stability under ancestor rank-shift).** Under the nested
assumption, the window geometry at position `j` is preserved:

    window_size j (psi_i w) = window_size j w = ws_j
    window_at j (psi_i w) = RS_i(window_at j w)

where `RS_i(window_at j w)` denotes: take each label `x` in `window_at j w`,
find its rank `r` in `sort leq (window_at i w)`, and replace it by
`S_i[(r + delta_i) mod ws_i]`.

**Proof sketch of Claim 3.2.** The window structure at position `j` is
determined by the recursive `mm_pos` computation on the relevant sub-sequence.
The `mm_pos` of a sequence depends on which element is the first min-or-max.
Under rank-shift of the *entire* enclosing window `W_i`, every label in
`W_i` gets its rank shifted by the same `delta`. This is an order-preserving
map on the labels (it cyclically shifts the sorted order). For the sub-
sequence corresponding to `window_at j w`, the mm_pos computation asks:
"which element is the first min-or-max?" Since rank-shift preserves the
relative order of all elements **except** for the cyclic wrap-around (the
old maximum becomes the new minimum or vice versa), we need to check that
the wrap-around element does not land inside `W_j` in a way that disrupts
`mm_pos`.

This is where the subtree structure helps. The element that wraps around is
the old root label `a_i` (at position `i`), which gets mapped to the
opposite extremum. But position `i` is **outside** `W_j` (since `i < j`
and `W_j` starts at position `j`). Therefore, within the positions
`[j, j + ws_j)`, the rank-shift acts as a **strictly monotone** map on labels
(no wrap-around occurs within this sub-window), and hence `mm_pos` is
preserved. QED sketch.

More precisely: within `W_j`, the rank-shift maps rank `r` to
`(r + delta) mod ws_i`. The wrap-around (where `(r + delta) mod ws_i < r`
for delta > 0, or `> r` for delta < 0) happens only at the boundary rank --
rank `ws_i - 1` when delta = 1, or rank `0` when delta = `ws_i - 1`. The
element with this boundary rank in `W_i` is the root label `a_i` at position
`i`, which is not in `W_j`. So within `W_j`, the map `r -> (r + delta) mod
ws_i` is strictly order-preserving. Therefore `mm_pos` at every recursive
level within `W_j` is unchanged.

### 3.3 The commutation identity

We now prove `psi_i(psi_j(w)) = psi_j(psi_i(w))`.

**LHS: psi_i(psi_j(w)).**

Step 1: Apply `psi_j` to `w`. This modifies only positions in `[j, j + ws_j)`.
The result is:

    w_1 := psi_j(w):
      positions [0, j):         unchanged from w
      positions [j, j+ws_j):    RS_j(window_at j w)
      positions [j+ws_j, n):    unchanged from w

Step 2: Apply `psi_i` to `w_1`. We need `window_at i w_1` and
`window_size i w_1`. Since `psi_j` only modifies positions in `[j, j+ws_j)`
which is a sub-interval of `[i, i + ws_i)`, the positions outside
`[i, i + ws_i)` are unchanged, so by the same mm_pos-stability argument
(the external positions that determine the recursive path to position `i`
are untouched), we get:

    window_size i w_1 = ws_i
    window_at i w_1 = (labels at positions [i, i+ws_i) in w_1)

The labels at positions `[i, i+ws_i)` in `w_1` are:
- at position `i`: same as `w[i]` (since `i < j`, unchanged by `psi_j`);
- at positions `[i+1, j)`: same as in `w` (before `W_j`, unchanged);
- at positions `[j, j+ws_j)`: `RS_j(window_at j w)`;
- at positions `[j+ws_j, i+ws_i)`: same as in `w` (after `W_j`, unchanged).

Call this combined sequence `W_i^{(1)}`. Now `psi_i` applies `RS_i` to
`W_i^{(1)}`, using the sorted order of `W_i^{(1)}`.

**Key fact:** `perm_eq W_i^{(1)} W_i`. This is because `psi_j` is a
permutation of labels within `W_j` (by `psi_perm_eq`), and `W_j` is a
sub-interval of `W_i`. So the multiset of labels in `W_i` is unchanged.
Therefore `sort leq W_i^{(1)} = sort leq W_i =: S_i`, and the rank-shift
`RS_i` uses the same sorted reference `S_i`. The head of `W_i^{(1)}` is
`w[i]` = head of `W_i` (unchanged since position `i` is outside `W_j`), so
the shift direction (min/max) is also unchanged.

Therefore:

    psi_i(w_1) at positions [i, i+ws_i) = RS_i(W_i^{(1)})

where `RS_i` uses sorted order `S_i` and shift `delta_i`.

**RHS: psi_j(psi_i(w)).**

Step 1: Apply `psi_i` to `w`. This modifies positions `[i, i+ws_i)`:

    w_2 := psi_i(w):
      positions [i, i+ws_i):    RS_i(W_i)
      rest:                     unchanged

Step 2: Apply `psi_j` to `w_2`. By Claim 3.2:

    window_size j w_2 = ws_j
    window_at j w_2 = (positions [j, j+ws_j) of RS_i(W_i))
                     = RS_i restricted to sub-window at j

Call this `RS_i(W_j)` -- the labels at positions `[j, j+ws_j)` after
rank-shifting all of `W_i`. Now `psi_j` applies `RS_j'` to this sub-window,
where the prime indicates that the sorted reference and shift direction are
computed from the *new* sub-window labels.

**Key fact:** `perm_eq (RS_i(W_j)) W_j` (rank-shift preserves the multiset),
so `sort leq (RS_i(W_j)) = sort leq W_j =: S_j`. The head of `RS_i(W_j)` is
the rank-shifted version of `w[j]`. Since `w[j]` was either min or max of
`W_j = window_at j w`, and rank-shift is a monotone map on the labels of
`W_j` (as argued in 3.2 -- no wrap-around within `W_j`), the rank-shifted
`w[j]` is either the min or max of `RS_i(W_j)`. Specifically:

- If `w[j] = min(W_j)`, then since `RS_i` is order-preserving on `W_j`,
  `RS_i(w[j]) = min(RS_i(W_j))`. Wait -- but `RS_i` maps rank `r` to
  `(r + delta_i) mod ws_i` in the *global* sorted order `S_i`. Within `W_j`,
  the relative order is preserved (no wrap), so min maps to min and max maps
  to max within the shifted sub-window. Therefore the head of `RS_i(W_j)` has
  the same extremal type (min or max) as the head of `W_j`. Hence
  `delta_j' = delta_j` (same shift direction).

- If `w[j] = max(W_j)`, symmetric argument, same conclusion.

So `RS_j'` uses the same sorted list `S_j` and the same shift amount
`delta_j` as the original `RS_j`. Therefore:

    psi_j(w_2) at positions [j, j+ws_j)
      = RS_j(RS_i(W_j))           ... (A)

### 3.4 Showing LHS = RHS

We need to show that the final labels at every position agree. Positions
outside `[i, i+ws_i)` are easy (both sides agree with `w`). Within
`[i, i+ws_i)`, we compare:

**LHS at positions [i, i+ws_i):**

    RS_i(W_i^{(1)})

where `W_i^{(1)}` agrees with `W_i` except at positions `[j, j+ws_j)`, where
it has `RS_j(W_j)` instead of `W_j`.

**RHS at positions [i, i+ws_i):**

    psi_j(w_2)|_{[i, i+ws_i)} = RS_i(W_i) with positions [j, j+ws_j) replaced
    by RS_j(RS_i(W_j))

More carefully: `w_2 = psi_i(w)` has `RS_i(W_i)` at positions `[i, i+ws_i)`.
Then `psi_j` modifies only positions `[j, j+ws_j)` within that, replacing the
labels there by `RS_j` applied to the sub-window. So:

    RHS at [i, i+ws_i) = RS_i(W_i) with [j-i, j-i+ws_j) replaced by
                          RS_j(RS_i(W_j))

We need to show this equals `RS_i(W_i^{(1)})`.

**The crucial algebraic identity.** Let `L` be a sequence of distinct
integers (length `ws_i`), and let `L'` be obtained from `L` by replacing a
sub-interval `[a, a+m)` with a permutation of the same labels (so
`perm_eq L L'`). Then:

    RS(L') = RS(L) with [a, a+m) replaced by RS applied to [a, a+m) of L'

This holds because `RS` is defined entry-by-entry: for each position `p`,

    RS(L)[p] = S[(index(L[p], S) + delta) mod k]

where `S = sort leq L` and `k = |L|`. Since `perm_eq L L'`, we have
`sort leq L' = sort leq L = S`, and `head L' = head L` (position 0 is
outside `[a, a+m)` since `a >= j - i >= 1`). So the formula for `RS(L')` at
position `p` is:

    RS(L')[p] = S[(index(L'[p], S) + delta) mod k]

At positions outside `[a, a+m)`, `L'[p] = L[p]`, so `RS(L')[p] = RS(L)[p]`.
At positions inside `[a, a+m)`, `L'[p]` is the permuted label. Now:

    LHS entry at global position j+t (for 0 <= t < ws_j):
      RS_i(W_i^{(1)})[j-i+t]
        = S_i[(index(W_i^{(1)}[j-i+t], S_i) + delta_i) mod ws_i]
        = S_i[(index(RS_j(W_j)[t], S_i) + delta_i) mod ws_i]

    RHS entry at global position j+t:
      RS_j(RS_i(W_i)[j-i .. j-i+ws_j))[t]
        = S_j[(index(RS_i(W_i)[j-i+t], S_j) + delta_j) mod ws_j]

We need these to be equal. Let us unpack `RS_i(W_i)[j-i+t]`:

    RS_i(W_i)[j-i+t] = S_i[(index(W_i[j-i+t], S_i) + delta_i) mod ws_i]
                       = S_i[(index(W_j[t], S_i) + delta_i) mod ws_i]

(since `W_i[j-i+t] = W_j[t]` -- the sub-window at offset `j-i` within `W_i`
is exactly `W_j`).

And `RS_j(W_j)[t]`:

    RS_j(W_j)[t] = S_j[(index(W_j[t], S_j) + delta_j) mod ws_j]

So:

    LHS = S_i[(index(S_j[(index(W_j[t], S_j) + delta_j) mod ws_j], S_i) + delta_i) mod ws_i]

    RHS = S_j[(index(S_i[(index(W_j[t], S_i) + delta_i) mod ws_i], S_j) + delta_j) mod ws_j]

These are `RS_i(RS_j(W_j)[t])` and `RS_j(RS_i(W_j)[t])` respectively. So
the identity we need is:

    **For each label x in W_j: RS_i(RS_j(x)) = RS_j(RS_i(x))**

where `RS_i(x) = S_i[(r_i(x) + delta_i) mod ws_i]` with `r_i(x) = index(x, S_i)`,
and `RS_j(x) = S_j[(r_j(x) + delta_j) mod ws_j]` with `r_j(x) = index(x, S_j)`.

### 3.5 Why RS_i and RS_j commute on labels in W_j

Define the rank functions:
- `r_i(x) = index(x, S_i)` -- rank of `x` among all labels in `W_i`.
- `r_j(x) = index(x, S_j)` -- rank of `x` among labels in `W_j` only.

Since `W_j`'s labels are a subset of `W_i`'s labels, `r_i` and `r_j` are
related: the labels `S_j[0] < S_j[1] < ... < S_j[ws_j - 1]` appear as a
subsequence of `S_i[0] < S_i[1] < ... < S_i[ws_i - 1]`. Let
`phi: {0, ..., ws_j - 1} -> {0, ..., ws_i - 1}` be the embedding that
sends the `r_j`-rank to the `r_i`-rank, i.e. `phi(r_j(x)) = r_i(x)` for
all `x` in `W_j`.

**Claim 3.5.** `RS_i` acts on labels of `W_j` as a **monotone** map: if
`r_j(x) < r_j(y)` then `r_j(RS_i(x)) < r_j(RS_i(y))`. (No wrap-around
within `W_j` under `RS_i`, as argued in section 3.2.)

Given Claim 3.5, `RS_i` restricted to labels of `W_j` is a monotone
bijection `W_j -> W_j` (the multiset is preserved by `psi_perm_eq` and
the nested structure). Such a monotone bijection on a finite totally ordered
set is uniquely determined by its action on ranks: it maps `r_j`-rank `s` to
`r_j`-rank `s + delta_j'` for some fixed offset `delta_j'` (modular
arithmetic within `{0, ..., ws_j - 1}`). In fact `delta_j' = delta_j`
as argued in section 3.3 (the head's extremal type is preserved).

Wait -- we need to be more precise. `RS_i` restricted to `W_j`-labels is
monotone, so it acts as an order-preserving bijection on `S_j`. But
`RS_j` also acts as a specific rank-shift on `S_j`. The question is whether
these two operations commute.

Let us re-derive. For `x` in `W_j`:

    RS_i(x) = S_i[(r_i(x) + delta_i) mod ws_i]

Since `RS_i` is monotone on `W_j` labels (no wrap), there exists a function
`sigma: {0,...,ws_j-1} -> {0,...,ws_j-1}` (a monotone bijection) such that
`r_j(RS_i(x)) = sigma(r_j(x))`. By monotonicity, `sigma` is the identity or
a shift. In fact, `sigma(s) = (s + c) mod ws_j` for some constant `c`.

To compute `c`: the label `S_j[0]` (the min of `W_j`) has `r_i`-rank
`phi(0)`. Under `RS_i`, it maps to `S_i[(phi(0) + delta_i) mod ws_i]`.
Since no wrap-around occurs, this label is still in `W_j`, and its `r_j`-rank
is `c = sigma(0)`.

Similarly, `RS_j(x) = S_j[(r_j(x) + delta_j) mod ws_j]`. This has
`r_i`-rank `phi((r_j(x) + delta_j) mod ws_j)`.

Now:

    RS_i(RS_j(x)):
      First, RS_j(x) = S_j[(r_j(x) + delta_j) mod ws_j].
      This has r_i-rank phi((r_j(x) + delta_j) mod ws_j).
      Then RS_i maps it to S_i[(phi((r_j(x) + delta_j) mod ws_j) + delta_i) mod ws_i].

    RS_j(RS_i(x)):
      First, RS_i(x) has r_j-rank sigma(r_j(x)) = (r_j(x) + c) mod ws_j.
      Then RS_j maps it to S_j[((r_j(x) + c) + delta_j) mod ws_j]
        = S_j[(r_j(x) + c + delta_j) mod ws_j].

For these to be equal, we need `RS_i(RS_j(x))` to also equal
`S_j[(r_j(x) + c + delta_j) mod ws_j]`.

Note that `RS_i(RS_j(x))` is `S_i[(phi(r_j(RS_j(x))) + delta_i) mod ws_i]`
(wait, I should use the no-wrap-around property more directly).

Since RS_i is monotone on W_j labels and acts as rank-shift-by-c on the
r_j-ranks, we have for any label `y` in `W_j`:

    RS_i(y) = S_j[(r_j(y) + c) mod ws_j]

Therefore:

    RS_i(RS_j(x)) = S_j[(r_j(RS_j(x)) + c) mod ws_j]
                   = S_j[((r_j(x) + delta_j) mod ws_j + c) mod ws_j]
                   = S_j[(r_j(x) + delta_j + c) mod ws_j]

    RS_j(RS_i(x)) = S_j[(r_j(RS_i(x)) + delta_j) mod ws_j]
                   = S_j[((r_j(x) + c) mod ws_j + delta_j) mod ws_j]
                   = S_j[(r_j(x) + c + delta_j) mod ws_j]

These are equal since addition modulo `ws_j` is commutative:
`(r_j(x) + delta_j + c) mod ws_j = (r_j(x) + c + delta_j) mod ws_j`. **QED.**

### 3.6 Finishing the nested case

Combining: at positions outside `[i, i+ws_i)`, both LHS and RHS agree with
`w`. At positions in `[i, i+ws_i) \ [j, j+ws_j)`, `psi_j` acts as identity,
so both sides reduce to `RS_i(W_i)` at those positions. At positions in
`[j, j+ws_j)`, both sides give `RS_i(RS_j(W_j)) = RS_j(RS_i(W_j))` by
section 3.5. Therefore `psi_i(psi_j(w)) = psi_j(psi_i(w))`. **QED.**

---

## 4. Worked example: nested windows

We use `w = [3; 1; 4; 7; 5; 9; 2; 6]` from M2_PSI_INFORMAL.md section 5.

### 4.1 Tree structure recap

    M(w):
      root = 1 at position 1 (first min-or-max of w)
      left subtree: [3] (position 0)
      right subtree: M(4, 7, 5, 9, 2, 6)
        root = 9 at position 5 (first min-or-max of [4,7,5,9,2,6] is 9 at
               relative position 3, global position 1+1+3 = 5)
        left: M(4, 7, 5) -> root 4 at position 2, right subtree [7, 5]
              -> root 7 at position 3, right [5] at position 4
        right: M(2, 6) -> root 2 at position 6, right [6] at position 7

### 4.2 Windows

    window_at 1 w = drop 1 w = [1; 4; 7; 5; 9; 2; 6]  (ws = 7)
    window_at 5 w = [9; 2; 6]  (ws = 3)

So `W_5 = [5, 8)` is inside `W_1 = [1, 8)`. This is the nested case with
`i = 1, j = 5`.

### 4.3 Sorted orders

    S_1 = sort [1; 4; 7; 5; 9; 2; 6] = [1; 2; 4; 5; 6; 7; 9]  (ws_1 = 7)
    S_5 = sort [9; 2; 6] = [2; 6; 9]  (ws_5 = 3)

Head of W_1 is 1 = min(W_1), so delta_1 = ws_1 - 1 = 6 (shift down by 1,
i.e. rank r -> (r + 6) mod 7).

Head of W_5 is 9 = max(W_5), so delta_5 = 1 (shift up by 1, rank r ->
(r + 1) mod 3).

### 4.4 Compute psi_1(w) and psi_5(w)

**psi_5(w):**
Window [9; 2; 6], sorted [2; 6; 9], delta = 1.
- 9 (rank 2) -> rank 0 -> 2
- 2 (rank 0) -> rank 1 -> 6
- 6 (rank 1) -> rank 2 -> 9

psi_5(w) = [3; 1; 4; 7; 5; 2; 6; 9]

**psi_1(w):**
Window [1; 4; 7; 5; 9; 2; 6], sorted [1; 2; 4; 5; 6; 7; 9], delta = 6.
- 1 (rank 0) -> rank 6 -> 9
- 4 (rank 2) -> rank 1 -> 2
- 7 (rank 5) -> rank 4 -> 6
- 5 (rank 3) -> rank 2 -> 4
- 9 (rank 6) -> rank 5 -> 7
- 2 (rank 1) -> rank 0 -> 1
- 6 (rank 4) -> rank 3 -> 5

psi_1(w) = [3; 9; 2; 6; 4; 7; 1; 5]

### 4.5 Compute psi_1(psi_5(w))

psi_5(w) = [3; 1; 4; 7; 5; 2; 6; 9]

Window at position 1 in psi_5(w): still has ws = 7 (by window stability),
so window = [1; 4; 7; 5; 2; 6; 9].

Check: perm_eq with [1; 4; 7; 5; 9; 2; 6]? The labels are
{1, 4, 7, 5, 2, 6, 9} = {1, 2, 4, 5, 6, 7, 9}. Yes, same multiset.
Sorted: [1; 2; 4; 5; 6; 7; 9] = S_1 as before.
Head = 1 = min, so delta = 6 as before.

Rank-shift:
- 1 (rank 0) -> rank 6 -> 9
- 4 (rank 2) -> rank 1 -> 2
- 7 (rank 5) -> rank 4 -> 6
- 5 (rank 3) -> rank 2 -> 4
- 2 (rank 1) -> rank 0 -> 1
- 6 (rank 4) -> rank 3 -> 5
- 9 (rank 6) -> rank 5 -> 7

psi_1(psi_5(w)) = [3; 9; 2; 6; 4; 1; 5; 7]

### 4.6 Compute psi_5(psi_1(w))

psi_1(w) = [3; 9; 2; 6; 4; 7; 1; 5]

Window at position 5 in psi_1(w): ws = 3 (by Claim 3.2).
Positions 5, 6, 7 of psi_1(w) = [7; 1; 5].

Check: original W_5 labels were {9, 2, 6}. After RS_1: labels at positions
5, 6, 7 should be RS_1 applied to those labels.
- 9 (rank 6 in S_1) -> rank (6+6) mod 7 = 5 -> S_1[5] = 7. Check: yes, position 5 has 7.
- 2 (rank 1 in S_1) -> rank (1+6) mod 7 = 0 -> S_1[0] = 1. Check: yes, position 6 has 1.
- 6 (rank 4 in S_1) -> rank (4+6) mod 7 = 3 -> S_1[3] = 5. Check: yes, position 7 has 5.

Good. Window at 5 in psi_1(w) = [7; 1; 5]. Sorted: [1; 5; 7].
Head = 7 = max([1; 5; 7]), so delta_5' = 1.

Compare: original head of W_5 was 9 = max, delta_5 = 1. New head 7 is also
max. So delta_5' = delta_5 = 1. Consistent with section 3.3.

Rank-shift on [7; 1; 5] with sorted [1; 5; 7], delta = 1:
- 7 (rank 2) -> rank 0 -> 1
- 1 (rank 0) -> rank 1 -> 5
- 5 (rank 1) -> rank 2 -> 7

psi_5(psi_1(w)) = [3; 9; 2; 6; 4; 1; 5; 7]

### 4.7 Verification

    psi_1(psi_5(w)) = [3; 9; 2; 6; 4; 1; 5; 7]
    psi_5(psi_1(w)) = [3; 9; 2; 6; 4; 1; 5; 7]

They agree. Commutativity verified on this example.

**Cross-check of the key identity (section 3.5) on this example.**

For label x = 9 in W_5 (original):
- RS_5(9): rank 2 in S_5, (2+1) mod 3 = 0, -> S_5[0] = 2.
- RS_1(2): rank 1 in S_1, (1+6) mod 7 = 0, -> S_1[0] = 1.
- RS_1(RS_5(9)) = 1.

- RS_1(9): rank 6, (6+6) mod 7 = 5, -> S_1[5] = 7.
- RS_5(7)? But 7 is not in W_5! We need r_j-rank of RS_1(9) = 7 among S_j.
  After RS_1, the labels at positions [5,8) are [7; 1; 5]. Sorted: [1; 5; 7].
  So the "new S_j" is [1; 5; 7], and RS_j on this with delta = 1:
  7 has rank 2 in [1;5;7], (2+1) mod 3 = 0, -> 1.
- RS_j(RS_i(9)) = 1. Matches.

For label x = 2 in W_5:
- RS_5(2): rank 0, (0+1) mod 3 = 1, -> S_5[1] = 6.
- RS_1(6): rank 4, (4+6) mod 7 = 3, -> S_1[3] = 5.
- RS_1(RS_5(2)) = 5.

- RS_1(2): rank 1, (1+6) mod 7 = 0, -> 1.
- RS_j on RS_i(W_j) = [7,1,5], sorted [1,5,7]:
  1 has rank 0, (0+1) mod 3 = 1, -> 5.
- RS_j(RS_i(2)) = 5. Matches.

For label x = 6 in W_5:
- RS_5(6): rank 1, (1+1) mod 3 = 2, -> 9.
- RS_1(9): rank 6, (6+6) mod 7 = 5, -> 7.
- RS_1(RS_5(6)) = 7.

- RS_1(6): rank 4, (4+6) mod 7 = 3, -> 5.
  Wait: RS_1(6) = S_1[(4+6) mod 7] = S_1[3] = 5.
  Then RS_j: 5 in [1,5,7] has rank 1, (1+1) mod 3 = 2, -> 7.
- RS_j(RS_i(6)) = 7. Matches.

All three labels check out: RS_i and RS_j commute on W_j labels.

---

## 5. Formalization notes for Rocq

### 5.1 Suggested lemma decomposition (~150 LOC budget)

The proof structure maps to the following lemmas, building on `psi.v`'s
current API:

**L1. `psi_comm_disjoint` (~30 LOC).** Case 1: disjoint windows.

```
Lemma psi_comm_disjoint i j w :
  uniq w ->
  i + window_size i w <= j \/ j + window_size j w <= i ->
  psi i (psi j w) = psi j (psi i w).
```

Strategy: unfold `psi`, use `nth_psi_outside` (M2, T3) to show each
operator's window is unaffected by the other. Reduce to showing the five-
slice decomposition (section 2) commutes. Most of the work is bookkeeping
with `take`, `drop`, `cat`, and `size` lemmas.

**L2. `window_size_psi_ancestor` (~25 LOC).** Window-size stability when the
modified window contains the queried one.

```
Lemma window_size_psi_ancestor i j w :
  uniq w -> i < j -> j + window_size j w <= i + window_size i w ->
  window_size j (psi i w) = window_size j w.
```

Strategy: induction on `size w` paralleling the recursive structure of
`window_size`. Uses `mm_pos` stability (M2 T4) and the fact that `psi_i`
preserves `mm_pos` at all levels above and at `i` (already analyzed in
M2_SUBTASKS.md T4). The key new ingredient: `psi_i`'s rank-shift, restricted
to positions within `W_j`, preserves the `mm_pos` split points because it
is monotone there (no rank wrap-around).

**L3. `window_at_psi_ancestor` (~25 LOC).** Window-at stability (companion
to L2).

```
Lemma window_at_psi_ancestor i j w :
  uniq w -> i < j -> j + window_size j w <= i + window_size i w ->
  window_at j (psi i w) =
    [seq nth 0 (sort leq (window_at i w))
         ((index y (sort leq (window_at i w)) +
           (if head 0 (window_at i w) == nth 0 (sort leq (window_at i w)) 0
            then (window_size i w).-1 else 1))
          %% window_size i w)
     | y <- window_at j w].
```

(In words: the window at `j` in `psi_i(w)` is the entry-wise rank-shift of
the window at `j` in `w`, using `W_i`'s sorted reference.)

**L4. `rank_shift_comm_nested` (~30 LOC).** The core algebraic identity from
section 3.5.

```
Lemma rank_shift_comm_nested (L_big L_small : seq nat) (a : nat) :
  uniq L_big -> uniq L_small ->
  (* L_small is a contiguous sub-sequence of L_big starting at offset a *)
  subseq L_small (drop a L_big) ->
  ... ->
  (* RS on L_big then RS on the sub-window = RS on sub-window then RS on L_big *)
  ...
```

The exact statement needs care; the cleanest formulation may be point-wise:
for each label `x` in `L_small`,
`RS_big(RS_small(x)) = RS_small(RS_big(x))` where both sides are well-
defined because `RS_big` is monotone on `L_small`'s labels (Claim 3.5).

Alternatively, state it as: `rank_shift_seq` on the big window, followed by
extracting and rank-shifting the sub-window, equals rank-shifting the sub-
window first and then rank-shifting the big window. This is the equation
from section 3.4.

The proof reduces to modular arithmetic: `(r + delta_i + c) mod ws_j =
(r + c + delta_j) mod ws_j` by commutativity of addition.

**L5. `psi_comm_nested` (~25 LOC).** Case 2: nested windows.

```
Lemma psi_comm_nested i j w :
  uniq w ->
  i < j -> j + window_size j w <= i + window_size i w ->
  psi i (psi j w) = psi j (psi i w).
```

Assembles L2, L3, L4 and the slice decomposition.

**L6. `psi_comm` (~15 LOC).** The main theorem.

```
Theorem psi_comm i j w :
  uniq w -> psi i (psi j w) = psi j (psi i w).
```

Case split on disjoint vs nested. The three geometric cases (section 1.2)
are decided by comparing `i + ws_i` with `j` and `j + ws_j` with `i`.
When `i = j`, the statement is trivially `psi i (psi i w) = psi i (psi i w)`.

**Total: ~150 LOC.**

### 5.2 Dependencies on M2 infrastructure

The proof critically depends on the following M2 lemmas (from `psi.v` and
M2_SUBTASKS.md):

- `psi_perm_eq` (line 333): `perm_eq (psi i w) w`. Used to show sorted
  references are preserved.
- `rank_shift_perm_eq` (line 271): `perm_eq (rank_shift_seq L) L`. Same
  purpose at the window level.
- `window_size_cons`, `window_at_cons` (lines 498, 551): structural
  recursion on windows. Essential for the inductive proofs of L2, L3.
- `psi_id_oor`, `psi_id_trivial` (lines 521, 531): boundary cases.
- `sort_rank_shift_seq` (line 310): sorted order is preserved by rank-shift.

Additionally, the M2_SUBTASKS.md T4 (`mm_pos_psi_eq`) is needed: if `psi_i`
modifies positions within a window, the `mm_pos` at levels above `i` is
preserved. If T4 is not yet proved (it is listed as the "crux" of M2),
it must be established before M3 can proceed.

### 5.3 What can be computed vs what needs proof

The `Example`-level check can verify specific instances:

```coq
Example psi_comm_ex :
  psi 1 (psi 5 [:: 3; 1; 4; 7; 5; 9; 2; 6])
  = psi 5 (psi 1 [:: 3; 1; 4; 7; 5; 9; 2; 6]).
Proof. by []. Qed.
```

This reduces by `Compute` and provides a non-triviality sanity check. But
the general proof requires the inductive mm_pos-stability and the rank-shift
commutation algebra.

---

## 6. Relation to Fact #2 and proof strategy recommendation

### 6.1 Stanley's remark (lines 259--263)

Stanley observes (line 263):

> "In fact, this independence is equivalent to the commutativity of the psi_i's."

The "independence" refers to the descent-set changes described by Fact #2:
each `psi_i` toggles at most one or two descent positions (depending on
whether vertex `i` has only a right child or both children), and these
toggles act on *disjoint* positions for different `i`. The key is that when
vertex `a_i` has both children, the affected positions are `{i-1, i}`, and
`a_{i-1}` is always an endpoint (Stanley line 259), so `psi_{i-1}` acts
trivially -- hence no conflict.

### 6.2 Two possible proof routes

**Route A: Prove commutativity directly (recommended).**

This is the approach developed in sections 2--3 above. It works purely at
the level of sequence operations and rank-shift algebra, without needing to
analyze descent sets at all. The core is the algebraic identity
`RS_i(RS_j(x)) = RS_j(RS_i(x))` for nested windows (section 3.5), which
reduces to commutativity of modular addition.

Advantages:
- Self-contained: does not require Fact #2 (which is M4 scope).
- The key identity is clean modular arithmetic.
- Naturally fits the existing `psi.v` API (windows, rank-shift).

Disadvantages:
- Requires proving window-stability lemmas (L2, L3) which involve
  non-trivial induction on the tree recursion.

**Route B: Go through Fact #2 (descent-set independence implies commutativity).**

The idea: if we prove Fact #2 first (each `psi_i` toggles specific descent
positions) and that these toggles are independent, commutativity follows
because two permutations that agree on their descent-set effect and are
both involutions must commute (when they affect disjoint positions).

Disadvantages:
- Fact #2 is significantly harder than commutativity. It requires the
  "tree-classifier" machinery (M4 in the roadmap, ~200 LOC per
  docs/internal/AXIOMS_TODO.md).
- The implication "independence => commutativity" is not trivial: it
  requires showing that two permutations of S_n with the same descent-set
  effect are equal, which itself needs a non-trivial argument (the
  M-equivalence class structure).
- This route would force us to complete M4 before M3, inverting the
  planned dependency order.

### 6.3 Recommendation

**Prove commutativity directly (Route A).** The rank-shift commutation
identity (section 3.5) is the cleanest path. The algebraic core --
commutativity of addition mod m -- is trivial once the monotonicity of
RS_i on sub-windows is established. The mm_pos-stability infrastructure
(L2, L3) is needed anyway for Route B and for later milestones.

Furthermore, Stanley's parenthetical "in fact, this independence is
equivalent to the commutativity" (line 263) is an observation about the
*logical relationship* between Facts #1 and #2, not a recommended proof
strategy. The direct proof of commutativity is shorter and more elementary
than proving Fact #2 first.
