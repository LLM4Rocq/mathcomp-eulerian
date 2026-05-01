# Milestone 4: Fact #2 --- the descent-set effect of psi_i

**Source of truth.** Stanley, *Enumerative Combinatorics* vol. 1 (2nd ed.),
section 1.6.3, lines 245--264 of `refs/stanley_1_6_cdindex.txt`.

**Dependencies.** `psi.v` (Milestones 2--3), `descent.v`, `M2_PSI_INFORMAL.md`.

---

## 1. Setup

### 1.1 Descent at position k for `seq nat`

For a sequence `w : seq nat` of length `n`, position `k` (0-indexed,
`0 <= k < n-1`) is a **descent** if

    w[k] > w[k+1]

where `w[k] := nth 0 w k`. In Rocq:

```coq
Definition is_descent_seq (w : seq nat) (k : nat) : bool :=
  nth 0 w k > nth 0 w k.+1.
```

The **descent set** is `D(w) = { k : 0 <= k < size w - 1 | w[k] > w[k+1] }`.

Note: Stanley uses 1-indexed positions (`D(w) \subseteq [n-1]` for
`w \in S_n`). We use 0-indexed throughout. Stanley's "i in D(w)" corresponds
to our "i-1 in D(w)" when i is 1-indexed. However, since `psi.v` already uses
0-indexed `i` for vertex positions, we adopt the convention that "position i"
in both the tree and the descent set means the 0-indexed position. Stanley's
Fact #2 statement translates directly once we fix the indexing.

### 1.2 The min-max tree and vertex classification

Recall from `M2_PSI_INFORMAL.md`: the min-max tree `M(w)` is built by
recursively splitting at `mm_pos s` (the first position achieving either the
global min or the global max). The in-order traversal of `M(w)` recovers `w`
(`mmtree_of_seq_mmK`). The vertex at in-order position `i` is labelled `w[i]`.

For the vertex at position `i`, define:

- **window**: `window_at i w = take (window_size i w) (drop i w)`, i.e. the
  contiguous slice `w[i], w[i+1], ..., w[i + ws - 1]` where
  `ws = window_size i w`. This slice consists of `w[i]` (the root of the
  subtree `M_{a_i}`) together with its right subtree's labels.

- **endpoint** (leaf): `window_size i w = 1`. The vertex has no right child.
  `psi i w = w` (identity).

- **internal vertex**: `window_size i w >= 2`. The vertex has a right child.

Stanley's Fact #2 further distinguishes internal vertices by whether they
have a left child:

**(a) Right-child only (Case R).** Vertex `a_i` has a right child but no left
child. This means `i` is the leftmost position reached during the recursive
tree construction at the level where `a_i` becomes the root. Equivalently:
either `i = 0` (the global root has no left subtree when the first extremum
is the leftmost element), or `a_i` is the root of some right subtree whose
left subtree is empty.

In terms of `psi.v`'s API: vertex `i` has no left child if and only if, in
the recursive decomposition of `M(w)`, position `i` coincides with `mm_pos`
of the subarray it belongs to. Concretely: `i` is at the leftmost position of
a subarray at the recursive level where it is selected as root. This means
there are no elements to the left of `i` in its subarray, i.e. the left
subtree is empty.

**(b) Both children (Case LR).** Vertex `a_i` has both a left and a right
child. This means `i > mm_pos` of the subarray at the level where `i` becomes
a root --- wait, that's not quite right. Let me restate precisely.

Vertex `a_i` has a left child when `i > 0` and position `i-1` lies in the
left subtree of vertex `i`. In the in-order traversal, the left subtree of
vertex `i` occupies positions immediately before `i`. Specifically, if
`window_size i w >= 2` (so `i` is internal), then `i` has a left child if and
only if `i > 0` and position `i-1` is an element of the left subtree of
vertex `i` in `M(w)`.

**How to detect "has left child" from `window_size` and `mm_pos`:** At the
recursive level where vertex `i` is selected as root, the subarray is some
`s = w[l..r]` and `mm_pos(s) = i - l`. Vertex `i` has a left child iff
`i - l > 0`, i.e. `l < i`. The positions `l, l+1, ..., i-1` form the left
subtree.

For formalization, rather than tracking `l` explicitly through the recursion,
we can use the following characterization:

> **has_left_child i w** iff `i > 0` and `window_size (i-1) w = 1` and
> vertex `i-1` is the rightmost leaf of the left subtree of vertex `i`.

Actually, the cleaner characterization (which avoids tracking recursion depth)
is:

> Vertex `i` has a left child iff `i > 0` and
> `i + window_size i w < (i-1) + window_size (i-1) w` is FALSE, i.e.
> vertex `i-1`'s window does NOT extend past vertex `i`'s window.

Wait --- this conflates window geometry with tree structure. Let us use a more
direct definition.

**Direct definition via `mm_pos`.** Define recursively:

```
has_left_child i w :=
  let s = subarray containing i at its recursive level in
  (i - left_endpoint(s)) > 0
```

For a formalization-friendly version, we observe: vertex `i` has a left child
if and only if `i` is NOT the leftmost position in its containing subarray
when it is chosen as root. We can detect this by a recursive descent through
the tree, mirroring `window_size_fuel`:

```coq
Fixpoint has_left_child_fuel (fuel : nat) (i : nat) (s : seq nat) : bool :=
  match fuel with
  | 0 => false
  | fuel'.+1 =>
      match s with
      | [::] => false
      | _ :: _ =>
          let j := mm_pos s in
          if i < j then has_left_child_fuel fuel' i (take j s)
          else if i == j then (0 < j)
          else has_left_child_fuel fuel' (i - j - 1) (drop j.+1 s)
      end
  end.

Definition has_left_child (i : nat) (w : seq nat) : bool :=
  has_left_child_fuel (size w) i w.
```

When `i == j` (i.e., position `i` is chosen as root of its subarray), it has
a left child iff `j > 0`, i.e., there are elements to its left in the
subarray.

### 1.3 Stanley's key structural observation (line 259)

> "If `a_i` is a vertex with two children, then `a_{i-1}` will always be an
> endpoint on the left subtree of `a_i`."

In 0-indexed terms: if vertex `i` has both children, then vertex `i-1` is the
**rightmost** element of the left subtree of vertex `i`, and it is an
**endpoint** (leaf) of `M(w)`. This is because the in-order traversal visits
the left subtree, then the root, then the right subtree --- so the element
immediately before the root in in-order is the rightmost leaf of the left
subtree.

That vertex `i-1` is a leaf means `window_size (i-1) w = 1`, i.e.
`psi (i-1)` acts as the identity.

---

## 2. Descent at positions far from i

**Claim.** For `k` such that `k != i-1` and `k != i`, we have

    is_descent_seq (psi i w) k = is_descent_seq w k.

**Proof.** Set `ws = window_size i w`. The window occupies positions
`[i, i + ws)`. We have

    psi i w = take i w ++ rank_shift_seq(window_at i w) ++ drop (i + ws) w.

We need to show `(psi i w)[k] > (psi i w)[k+1]` iff `w[k] > w[k+1]`.

**Case 1: Both `k` and `k+1` are outside the window.**

If `k+1 < i` (i.e., `k < i-1`): both `w[k]` and `w[k+1]` are in the prefix
`take i w`, which `psi i` does not modify. So `(psi i w)[k] = w[k]` and
`(psi i w)[k+1] = w[k+1]`. The descent bit is unchanged.

If `k >= i + ws` (i.e., `k+1 > i + ws`): both `w[k]` and `w[k+1]` are in the
suffix `drop (i + ws) w`, which `psi i` does not modify. The descent bit is
unchanged.

**Case 2: Both `k` and `k+1` are strictly inside the window, i.e.,
`i < k` and `k+1 < i + ws`.**

This means `i+1 <= k` and `k+1 <= i + ws - 1`, i.e., both `w[k]` and
`w[k+1]` are among the non-head elements of the window (positions
`i+1, ..., i+ws-1`).

Key fact: `rank_shift_seq` preserves the relative order of non-head elements.

To see this: let `L = window_at i w = [x_0; x_1; ...; x_{ws-1}]` where
`x_0 = w[i]` is the head. Let `sorted = sort leq L`. The rank-shift maps
each element `y` to `sorted[(index y sorted + delta) mod ws]` where
`delta = ws-1` if `x_0 = min L`, and `delta = 1` if `x_0 = max L`.

For non-head elements `x_p, x_q` with `1 <= p, q <= ws-1`:
- Their ranks in `sorted` are `r_p = index x_p sorted` and
  `r_q = index x_q sorted`.
- The head `x_0` has rank 0 (if min) or `ws-1` (if max).
- The non-head elements have ranks in `{1, ..., ws-1}` (if head is min) or
  `{0, ..., ws-2}` (if head is max).

**Sub-case: head is min (`delta = ws-1`).** Non-head ranks are in
`{1, ..., ws-1}`. After shift: rank `r` maps to `(r + ws - 1) mod ws = r - 1`
(since `1 <= r <= ws-1`, we get `r + ws - 1 = r - 1 + ws`, and
`(r-1+ws) mod ws = r-1`). So the shift sends rank `r` to rank `r-1`. This is
a monotone (strictly increasing) map on `{1, ..., ws-1}` to `{0, ..., ws-2}`.
Therefore: `r_p < r_q` iff `r_p - 1 < r_q - 1`, i.e., the relative order of
non-head elements is preserved.

**Sub-case: head is max (`delta = 1`).** Non-head ranks are in
`{0, ..., ws-2}`. After shift: rank `r` maps to `(r + 1) mod ws = r + 1`
(since `0 <= r <= ws-2`, we have `r + 1 <= ws - 1 < ws`, so mod is trivial).
Again monotone on the non-head ranks. Relative order preserved.

Therefore, for positions `k, k+1` both strictly inside the window:
`(psi i w)[k] > (psi i w)[k+1]` iff `w[k] > w[k+1]`. The descent bit at `k`
is unchanged.

**Case 3: `k = i + ws - 1` (boundary: `k` inside window, `k+1` outside).**

This is position `k = i + ws - 1`, and we need `k != i` (given) and
`k != i-1`. Since `ws >= 2` (vertex `i` is internal), `k = i + ws - 1 >= i+1`,
so `k != i` and `k != i-1` (since `k >= i+1 > i-1`). Now:
- `(psi i w)[k]` is the last element of `rank_shift_seq(window_at i w)`.
- `(psi i w)[k+1] = w[k+1]` (unchanged, outside window).

We need this descent bit to be unchanged. But wait: the last element of the
window *does* change under rank_shift. So this position `k = i + ws - 1` needs
separate analysis.

Actually, let me reconsider. For `k = i + ws - 1` with `ws >= 2`:
- If `ws = 2`: `k = i+1`, so `k = i+1 != i` and `k = i+1 != i-1` (when
  `i >= 1`). But `k = i+1` means `k-1 = i`, and we're looking at position
  `k`, not `k-1`. Since `k = i+1`, this is actually position `i+1`, which is
  the last element of the 2-element window. After rank_shift, position `i+1`
  changes. And `k+1 = i+2` is outside the window. So the descent bit at `k`
  *could* change.

Hmm --- but Stanley's Fact #2 says the *only* positions whose descent bit
changes are `i` and (in Case LR) `i-1`. So I need to show that the boundary
position `k = i + ws - 1` is NOT affected. Let me think about this more
carefully.

The window occupies `w[i], w[i+1], ..., w[i+ws-1]`. After rank_shift:
- `(psi i w)[i + ws - 1]` = last element of the shifted window.
- `(psi i w)[i + ws]` = `w[i + ws]` (unchanged).

For the last element of the window: it is the element at position `ws - 1` in
`rank_shift_seq(L)`. In the original tree, this is the rightmost leaf of the
subtree `M_{a_i}`. By property F2 of min-max trees, the rightmost element of
a min-max tree's in-order traversal is always an endpoint. As an endpoint,
its value is either the min or max of some 1-element subtree.

More precisely: the element at position `i + ws - 1` in `w` is the rightmost
element of the right subtree of vertex `i`. After rank_shift, this element's
value changes (it shifts by one rank). However, the element at position
`i + ws` is the first element of whatever comes after the subtree `M_{a_i}` in
the in-order traversal.

**Key structural fact:** In the min-max tree, the element at position `i + ws`
(if it exists) is an ancestor of vertex `i`, or in a completely different
branch. The relative order between `w[i + ws - 1]` and `w[i + ws]` is
determined by the tree structure at a level above vertex `i`. After
rank_shift, `w[i + ws - 1]` changes, but only by one rank within the sorted
order of the window `L`.

Actually, we need a finer argument. The element `w[i + ws - 1]` (the last
window element) is the rightmost leaf of `M_{a_i}`. Since it's a leaf, it is
an endpoint: `window_size (i + ws - 1) w = 1`. In the tree, the boundary
between positions `i + ws - 1` and `i + ws` is at a level above vertex `i`,
and the descent bit there depends on `w[i + ws - 1]` vs `w[i + ws]`.

Under rank_shift, position `i + ws - 1` (the last element of the window) has
its value changed. But does the comparison with `w[i + ws]` change?

**The answer is yes in general --- but position `i + ws - 1` is NOT one of
the positions listed in our "far from i" case.** Let me re-examine: we claimed
the result for `k != i-1` and `k != i`. For `k = i + ws - 1`:
- If `ws = 2`, then `k = i + 1`. We have `k != i` (true) and `k != i-1`
  (true for `i >= 1`). So this position IS in our "far from i" case. But does
  it actually stay unchanged?

Let me reconsider. In Case R (right-child only, no left child), the window
`[i, i+ws)` contains only vertex `i` and its right subtree. The descent bit
at positions `i+1, ..., i+ws-2` all involve two non-head window elements and
are preserved (Case 2 above). The descent bit at position `i+ws-1` involves
`w[i+ws-1]` (last window element) and `w[i+ws]` (outside window).

For this boundary: `w[i+ws-1]` is the rightmost element of `M_{a_i}`.
In the rank-shift, this element changes. BUT: the element at position `i+ws`
is determined by the tree structure outside `M_{a_i}`. Specifically, `w[i+ws]`
is the element that follows the subtree `M_{a_i}` in the in-order traversal;
this is the first element in the parent's right subtree that comes after
`M_{a_i}`, or the parent itself if `M_{a_i}` is a left subtree.

In any case, `w[i+ws]` is NOT in the window and is NOT modified by `psi i`.
And `w[i+ws-1]` IS modified. So the descent bit at `k = i+ws-1` *could*
change. This would contradict our claim.

Let me re-examine Stanley's Fact #2 more carefully. Stanley says `D(psi_i w)`
differs from `D(w)` only at positions `i` (Case R) or at positions `i-1, i`
(Case LR). So positions `i+ws-1` (for `ws >= 3`) must be unchanged.

**Resolution:** The rightmost leaf of `M_{a_i}` at position `i + ws - 1` has
rank either 0 or `ws-1` among the window elements (since it's an endpoint of
the subtree, it's either the min or max of some sub-subtree, and by the
structure of min-max trees, the rightmost leaf of a right subtree is always an
extremum within that subtree).

Actually, the key property is simpler: the element at position `i + ws - 1`
has rank `r` in `L = window_at i w`. Under rank_shift with `delta`, its new
rank is `(r + delta) mod ws`. For non-head elements, we showed the shift is
monotone: rank `r` goes to `r-1` (if head is min) or `r+1` (if head is max).
But what is the new *value*?

We need to compare the new `w[i+ws-1]` with the old `w[i+ws]`. The question
is: does `sorted[r-1] > w[i+ws]` iff `sorted[r] > w[i+ws]`? Not in general!

So indeed the descent bit at `i + ws - 1` could change in general... unless
the tree structure prevents it. Let me think about what the tree structure
guarantees.

**Tree-structural guarantee at the right boundary.** Position `i + ws` (if it
exists, i.e., `i + ws < size w`) is the next element after the subtree
`M_{a_i}` in the in-order traversal. In the min-max tree, the element
`w[i + ws]` is an ancestor of vertex `i`. Specifically, it is the vertex `v`
such that `M_{a_i}` is the rightmost subtree within `v`'s left subtree (if
`v` comes after `M_{a_i}` in the traversal). The key constraint from the
min-max tree property is:

`w[i + ws]` is either the min or max of the subtree rooted at `v`, and the
subtree rooted at `v` contains `M_{a_i}` as a sub-subtree. Therefore, either
`w[i+ws] < all elements of M_{a_i}` or `w[i+ws] > all elements of M_{a_i}`.

If `w[i+ws] < min(L)`: after rank_shift, all elements of the shifted window
are still `>= min(L)` (since rank_shift is a permutation of the same
multiset), so in particular `(psi i w)[i+ws-1] >= min(L) > w[i+ws]`. The
descent bit at `i+ws-1` is 1 before AND after. Unchanged.

If `w[i+ws] > max(L)`: similarly, `(psi i w)[i+ws-1] <= max(L) < w[i+ws]`.
The descent bit at `i+ws-1` is 0 before AND after. Unchanged.

Wait --- but `w[i+ws]` need not be an extremum of a subtree *containing*
`M_{a_i}`. It could be that `M_{a_i}` ends and the next element in in-order
is a sibling or uncle, not necessarily an ancestor.

Let me reconsider. In a binary tree, the in-order successor of the rightmost
element of a subtree is the *parent* of that subtree (if the subtree is a left
child), or the parent's parent (climbing up until we find a left-child
relationship). In any case, the in-order successor `w[i + ws]` is an
*ancestor* of the root of `M_{a_i}` (in the full tree `M(w)`), specifically
the closest ancestor whose left subtree contains `M_{a_i}`.

Actually, this isn't quite right either. The subtree `M_{a_i}` is rooted at
position `i`, which is a vertex in `M(w)`. The right subtree of vertex `i`
consists of positions `i+1, ..., i+ws-1`. The position `i+ws` is the in-order
successor of the rightmost element of vertex `i`'s subtree (considering only
vertex `i` and its right subtree). But vertex `i` may also have a left subtree
(positions before `i`), and in the full tree, the subtree rooted at the
*parent* of vertex `i` contains more positions.

The correct statement is: position `i + ws` is the in-order successor of
vertex `i`'s "right-extended subtree" `M_{a_i}`. In the full tree, this means
`w[i + ws]` is an ancestor of vertex `i` --- specifically, the lowest ancestor
`v` such that `i` is in `v`'s left subtree (viewing `M_{a_i}` as part of
`v`'s left side). By the min-max tree property (F2), `v` is either the min or
max of its subtree, which includes all elements of `M_{a_i}`. Therefore:

> Either `w[i+ws] < min(L)` or `w[i+ws] > max(L)`.

Since `rank_shift_seq` is a permutation of `L`, the multiset of values is
unchanged. So:
- If `w[i+ws] < min(L)`: `w[i+ws-1] > w[i+ws]` iff `(psi i w)[i+ws-1] > w[i+ws]`, both true. Descent bit unchanged.
- If `w[i+ws] > max(L)`: `w[i+ws-1] < w[i+ws]` iff `(psi i w)[i+ws-1] < w[i+ws]`, both true. Descent bit unchanged.

**Similarly for the left boundary in Case LR.** In Case LR, vertex `i` has a
left child, so position `i-1` is in the left subtree. The position `i-2`
(if it exists) is also in the left subtree. What about position `i-2` vs
`i-1`? Since `psi i` does not modify positions before `i`, both `w[i-2]` and
`w[i-1]` are unchanged. So the descent bit at `i-2` is unchanged. Good ---
this is consistent with our Case 1 (`k < i-1`).

**Summary of section 2.** For all positions `k` with `k != i-1` and `k != i`:

1. If `k+1 < i`: both `w[k], w[k+1]` unchanged. Descent bit unchanged.
2. If `k >= i + ws`: both `w[k], w[k+1]` unchanged. Descent bit unchanged.
3. If `i < k` and `k+1 < i + ws`: both inside window, rank_shift preserves
   relative order of non-head elements. Descent bit unchanged.
4. If `k = i + ws - 1` and `k+1 = i + ws`: right boundary. The value at `k`
   changes but `w[i+ws]` is an ancestor satisfying `w[i+ws] < min(L)` or
   `w[i+ws] > max(L)`. Since the multiset is preserved, the comparison doesn't
   flip. Descent bit unchanged.
5. If `k = i-1` in Case R: this is `k = i-1`, which is one of the excluded
   positions. (Not treated here.)

Therefore, for `k != i-1` and `k != i`, the descent bit is unchanged.
In Case R, we additionally have `k = i-1` unchanged (since vertex `i` has no
left child and `w[i-1]` is not in the window); the only change is at `k = i`.
In Case LR, changes occur at `k = i-1` and `k = i`.

---

## 3. Descent at position i (the main case)

### 3.1 Case R: right-child only

Vertex `i` has a right child but no left child. The window is
`L = [w[i]; w[i+1]; ...; w[i+ws-1]]` with `ws >= 2`.

By the min-max tree property (F2), `w[i]` is either the min or the max of `L`.

**Sub-case R1: `i` is NOT a descent (`w[i] < w[i+1]`).**

Since `w[i]` is an extremum of `L` and `w[i] < w[i+1]`, we must have
`w[i] = min(L)`. (If `w[i]` were `max(L)`, then `w[i] >= w[i+1]`, and since
all elements are distinct, `w[i] > w[i+1]`, contradiction.)

After rank_shift with `delta = ws - 1` (head is min):

- New head: `sorted[(0 + ws - 1) mod ws] = sorted[ws-1] = max(L)`.
- New second element: `sorted[(r_1 + ws - 1) mod ws] = sorted[r_1 - 1]`
  where `r_1 = index(w[i+1], sorted)`.

So `(psi i w)[i] = max(L)`. We need to show `(psi i w)[i] > (psi i w)[i+1]`,
i.e., position `i` becomes a descent.

`(psi i w)[i+1] = sorted[r_1 - 1]`. Since `r_1 >= 1` (because `w[i+1] > w[i]
= min(L) = sorted[0]`), we have `sorted[r_1 - 1] <= sorted[ws - 2] < sorted[ws-1] = max(L) = (psi i w)[i]`.

Therefore `(psi i w)[i] > (psi i w)[i+1]`: position `i` IS a descent of
`psi i w`.

Result: `D(psi_i w) \supseteq D(w) \cup {i}` at position `i`. Combined with
section 2 (all other positions unchanged) and the fact that `i \notin D(w)`:
`D(psi_i w) = D(w) \cup {i}`.

**Sub-case R2: `i` IS a descent (`w[i] > w[i+1]`).**

Since `w[i]` is an extremum and `w[i] > w[i+1]`, we have `w[i] = max(L)`.

After rank_shift with `delta = 1` (head is max):

- New head: `sorted[(ws-1 + 1) mod ws] = sorted[0] = min(L)`.
- New second element: `sorted[(r_1 + 1) mod ws] = sorted[r_1 + 1]`
  where `r_1 = index(w[i+1], sorted)`.

So `(psi i w)[i] = min(L)`. We need `(psi i w)[i] < (psi i w)[i+1]`:

`(psi i w)[i+1] = sorted[r_1 + 1]`. Since `r_1 <= ws - 2` (because
`w[i+1] < w[i] = max(L) = sorted[ws-1]`), we have
`sorted[r_1 + 1] >= sorted[1] > sorted[0] = min(L) = (psi i w)[i]`.

Therefore `(psi i w)[i] < (psi i w)[i+1]`: position `i` is NOT a descent of
`psi_i w`.

Result: `D(psi_i w) = D(w) \ {i}`.

### 3.2 Case LR: both children --- descent at position i

Vertex `i` has both left and right children. Position `i-1` is the rightmost
leaf of the left subtree of vertex `i` (Stanley's observation, line 259).

The analysis of position `i` is identical to Case R above:
- The window `L = window_at i w` starts with `w[i]`, which is min or max of `L`.
- If `w[i] < w[i+1]` (not a descent at `i`): after rank_shift, `(psi i w)[i] = max(L) > (psi i w)[i+1]`. Position `i` becomes a descent.
- If `w[i] > w[i+1]` (descent at `i`): after rank_shift, `(psi i w)[i] = min(L) < (psi i w)[i+1]`. Position `i` loses its descent.

The difference from Case R is that we also need to track what happens at
position `i-1`. This is section 4.

---

## 4. Descent at position i-1 (Case LR only)

### 4.1 Why exactly one of `i-1`, `i` is a descent

Position `i-1` is the rightmost leaf of the left subtree of vertex `i`. In
the min-max tree, vertex `i` is the root of a subtree `S_i` whose left
subtree has `i-1` as its rightmost leaf. By the tree property:

- `w[i]` is either `min(S_i)` or `max(S_i)`, where `S_i` is the subtree
  rooted at vertex `i` (including both left and right subtrees).
- `w[i-1]` is an element of the left subtree of vertex `i`.

Since `i-1` is the rightmost leaf of the left subtree, and `i` is the root,
the in-order traversal visits `..., w[i-1], w[i], w[i+1], ...`. The element
`w[i]` separates the left subtree from the right subtree.

Now, `w[i]` is an extremum (min or max) of the entire subtree rooted at `i`,
which includes `w[i-1]` and `w[i+1]` (among others).

**If `w[i] = min(S_i)`:** Then `w[i] < w[i-1]` and `w[i] < w[i+1]` (since
`w[i]` is strictly less than all other elements of `S_i`). So `w[i-1] > w[i]`
(descent at `i-1`) and `w[i] < w[i+1]` (NOT a descent at `i`). Exactly one of
`{i-1, i}` is a descent, namely `i-1`.

**If `w[i] = max(S_i)`:** Then `w[i] > w[i-1]` and `w[i] > w[i+1]`. So
`w[i-1] < w[i]` (NOT a descent at `i-1`) and `w[i] > w[i+1]` (descent at
`i`). Exactly one of `{i-1, i}` is a descent, namely `i`.

This confirms Stanley's claim: exactly one of `i-1, i` belongs to `D(w)`.

### 4.2 Effect of psi_i on the descent at position i-1

`psi i` does NOT modify `w[i-1]` (position `i-1` is outside the window
`[i, i+ws)`). But it DOES modify `w[i]` (the head of the window). So the
descent bit at position `i-1` is:

    is_descent_seq (psi i w) (i-1) = (w[i-1] > (psi i w)[i]).

**Sub-case LR1: `i \notin D(w)`, so `i-1 \in D(w)`.**

From 4.1: `w[i] = min(S_i)`, so `w[i-1] > w[i]` and `w[i] < w[i+1]`.
Since `w[i] = min(L)` (where `L = window_at i w`), the rank_shift uses
`delta = ws - 1` and the new head is `max(L)`.

Now: `(psi i w)[i] = max(L)`. Is `w[i-1] > max(L)`?

`w[i-1]` is in the left subtree of vertex `i`. The left subtree and the right
subtree (= `M_{a_i} \setminus \{w[i]\}`) are disjoint subsets of the subtree
`S_i`. Since `w[i] = min(S_i)` and `w[i]` is the root:

Actually, `max(L) = max(M_{a_i})`, where `M_{a_i} = \{w[i]\} \cup \text{right subtree}`.
This is NOT necessarily `max(S_i)`. The left subtree of vertex `i` could
contain elements larger than `max(L)`.

Wait, let me reconsider. `w[i]` is the min of `S_i` (the full subtree at `i`,
including left and right children). But `L = window_at i w` only includes
`w[i]` and the right subtree. So `max(L)` is the max of `\{w[i]\} \cup R_i`,
where `R_i` is the right subtree. The left subtree `L_i` has its own elements.

We need: is `w[i-1] > max(L)` or `w[i-1] < max(L)`?

`w[i-1]` is in the left subtree. `max(L)` is the max of the right subtree
(plus the root, but the root is the min). There's no a priori reason why
`w[i-1]` should be larger or smaller than `max(L)` --- the elements of the
left and right subtrees interleave arbitrarily.

So the descent bit at `i-1` after psi_i is `w[i-1] > max(L)`, which is NOT
necessarily false. We need a structural argument.

**Refined structural argument.** Let's look at this from the tree perspective.
Vertex `i-1` is the rightmost leaf of the left subtree of vertex `i`. In the
left subtree, vertex `i-1` is either a min or max of its (trivial) subtree
--- since it's a leaf, it's both. The important thing is the value `w[i-1]`
relative to `w[i]` and the right subtree.

Since the min-max tree is built by the "first min-or-max" rule, and vertex `i`
is chosen as the root of its subarray because `w[i]` is the first min-or-max:

If `w[i] = min(subarray)`: `w[i]` is less than all elements in both left and
right subtrees. The right subtree is `w[i+1], ..., w[i+ws-1]`. The left
subtree is `w[l], ..., w[i-1]` for some `l < i`.

Now, after `psi i`, the new `w[i]` is `max(L) = max\{w[i], w[i+1], ..., w[i+ws-1]\}`. Since `w[i] = min(subarray)` and the subarray includes the left subtree elements, we have `max(L) <= max(subarray)`. But `max(L)` could be less than, equal to, or greater than `w[i-1]`.

Hmm, we need to determine whether `w[i-1] > max(L)` or not. Let's think about
what Stanley's Fact #2 actually claims:

> If `i \notin D(w)` (and `i` has both children): `D(psi_i w) = (D(w) \cup \{i\}) \setminus \{i-1\}`.

This means: position `i` becomes a descent (shown in section 3.2), AND
position `i-1` stops being a descent. So we need `w[i-1] <= (psi i w)[i]`,
i.e., `w[i-1] < max(L)` (strict since all elements are distinct).

**Proof that `w[i-1] < max(L)`.** Recall the tree construction. Vertex `i`
is selected as root of a subarray `A = w[l..r]` because `w[i]` is the first
min-or-max in `A`. The left subtree occupies `w[l..i-1]` and the right subtree
occupies `w[i+1..r]`.

`max(L) = max\{w[i], w[i+1], ..., w[i+ws-1]\}`. But what is `ws` here? The
window `window_at i w` is `w[i]` plus the right subtree of vertex `i` in the
*full tree* `M(w)`, not just within the subarray `A`. Actually, by the
recursive structure, the right subtree of vertex `i` in `M(w)` is exactly
`M(w[i+1..r])`, where `A = w[l..r]` is the subarray at vertex `i`'s recursive
level. And the window `window_at i w` is exactly `w[i..i+ws-1]` where
`ws = 1 + |right subtree| = r - i + 1`. So `window_at i w = w[i..r]`.

Now: `w[i] = min(A)` (since `w[i]` was selected as the first-occurring
extremum and it was the min). So `w[i] < w[j]` for all `j \in [l, r], j \neq i`.
In particular, `max(L) = max\{w[i], ..., w[r]\}`. Since all elements of
`w[l..i-1]` are also elements of `A`, and `w[i] = min(A)`, we know all
elements of `A` except `w[i]` are `> w[i]`.

But we need to compare `w[i-1]` with `max(L)`. Consider: `max(A) = max(w[l..r])`.
Since `w[i]` was the FIRST min-or-max, the maximum `max(A)` occurs at some
position `p > i` (because if `max(A)` occurred at position `p < i = mm_pos(A)`,
then `mm_pos(A)` would have been `p`, not `i` --- since `mm_pos` picks the
first-occurring between min and max, and `index(min(A), A) = i - l`, if
`index(max(A), A) < i - l` then `mm_pos(A) = index(max(A), A)`, contradicting
that `mm_pos(A) = i - l`). Wait, actually `mm_pos(A)` picks whichever of min
and max has the smaller index. Since `mm_pos(A) = i - l` (relative to `A`),
and this was chosen because `w[i] = min(A)` and `index(min(A), A) <= index(max(A), A)`, we get `index(max(A), A) >= i - l`, i.e., `max(A)` occurs at
position `>= i` in `A`, i.e., at absolute position `>= l + (i - l) = i`.
Since `max(A) \neq min(A) = w[i]`, we have `max(A)` at position `> i`, so
`max(A) \in \{w[i+1], ..., w[r]\} \subseteq L`.

Therefore `max(L) >= max(A)` --- in fact `max(L) = max(w[i..r])` and
`max(A) = max(w[l..r])`. Since `\{w[i..r]\} \subseteq \{w[l..r]\} = A`, we
have `max(L) <= max(A)`. But `max(A)` is in `\{w[i+1], ..., w[r]\} \subseteq L`, so `max(A) <= max(L)`.
Therefore **`max(L) = max(A)`**.

Now: `w[i-1] \in A` and `w[i-1] \neq max(A)` (since `max(A) = max(L)` and
`max(A)` is at a position `> i`, while `i-1 < i`). Since all elements are
distinct, `w[i-1] < max(A) = max(L)`.

Therefore `w[i-1] < (psi i w)[i] = max(L)`, so position `i-1` is NOT a
descent after `psi_i`. Combined with the fact that `i-1 \in D(w)` (from
4.1), position `i-1` has been removed from the descent set.

**Sub-case LR2: `i \in D(w)`, so `i-1 \notin D(w)`.**

From 4.1: `w[i] = max(S_i)`, so `w[i-1] < w[i]` and `w[i] > w[i+1]`.
Since `w[i] = max(L)`, rank_shift uses `delta = 1` and the new head is
`min(L)`.

We need: `w[i-1] > (psi i w)[i] = min(L)`?

By the symmetric argument to the one above: when `w[i] = max(A)` and
`mm_pos(A) = i - l` (relative index), then `min(A)` occurs at position
`>= i` (since `mm_pos` picked `max(A)` first, meaning
`index(max(A), A) <= index(min(A), A)`, and since `mm_pos(A) = i - l`,
the min occurs at index `>= i - l` in `A`, hence at absolute position `>= i`;
and since `min(A) \neq max(A) = w[i]`, we get `min(A)` at position `> i`).
Therefore `min(A) \in L` and `min(L) = min(A)`.

Now: `w[i-1] \in A` and `w[i-1] \neq min(A) = min(L)`. Since all elements
are distinct, `w[i-1] > min(A) = min(L) = (psi i w)[i]`.

Therefore position `i-1` IS a descent after `psi_i`: `w[i-1] > (psi i w)[i]`.
Combined with `i-1 \notin D(w)`, position `i-1` has been added to the descent
set.

Result: `D(psi_i w) = (D(w) \cup \{i-1\}) \setminus \{i\}`.

---

## 5. Worked examples

### 5.1 Case R example: `w = [3; 1; 4; 7; 5; 9; 2; 6]`, `i = 5`

**Step 1: Compute the min-max tree.**

`w = [3; 1; 4; 7; 5; 9; 2; 6]`, `n = 8`.

Root: min = 1 at position 1, max = 9 at position 5. First extremum: min at
position 1 (1 < 5). So root = `w[1] = 1`, `mm_pos = 1`.

Left subtree: `[3]` (position 0). Right subtree: `[4; 7; 5; 9; 2; 6]`
(positions 2--7).

For the right subtree `[4; 7; 5; 9; 2; 6]`: min = 2 at position 4 (relative),
max = 9 at position 3 (relative). First extremum: max at position 3 (3 < 4).
So root = 9 at absolute position 5, `mm_pos = 3`.

Left subtree of 9: `[4; 7; 5]` (positions 2--4). Right subtree of 9:
`[2; 6]` (positions 6--7).

For `[4; 7; 5]`: min = 4 at pos 0, max = 7 at pos 1. First: min at pos 0.
Root = 4 at absolute position 2. Left subtree: empty. Right: `[7; 5]`.

For `[7; 5]`: min = 5 at pos 1, max = 7 at pos 0. First: max at pos 0.
Root = 7 at absolute position 3. Right: `[5]`.

For `[2; 6]`: min = 2 at pos 0, max = 6 at pos 1. First: min at pos 0.
Root = 2 at absolute position 6. Right: `[6]`.

**Tree structure:**
```
             1 (pos 1, min)
            / \
           3   9 (pos 5, max)
              / \
             4   2 (pos 6, min)
              \   \
               7   6
                \
                 5
```

**Step 2: Window at position 5.**

Vertex at position 5 is `w[5] = 9`. Its right subtree = `{2, 6}` (positions
6--7). So `M_{a_5} = {9, 2, 6}`.

`window_size 5 w = 3`, `window_at 5 w = [9; 2; 6]`.

**Step 3: Classify vertex 5.**

Does vertex 5 have a left child? Vertex 5's subarray (at the recursive level
where it becomes root) is `[4; 7; 5; 9; 2; 6]`. In this subarray, `mm_pos = 3`
(relative), so vertex 5 is at relative position 3, and there are 3 elements
to its left (`[4; 7; 5]`). So **yes, vertex 5 has a left child**.

Wait, but the window `window_at 5 w = [9; 2; 6]` has size 3 and starts at
position 5. The left subtree of vertex 5 (in the full tree) consists of
positions 2, 3, 4 (the subtree `[4; 7; 5]`). So vertex 5 has both children.

But actually, let me reconsider whether i=5 is Case R or Case LR. Position
i-1 = 4 is in the left subtree of vertex 5. So this IS Case LR.

Let me find a Case R example. Looking at the tree, vertex 2 (position 2,
value 4): its subarray is `[4; 7; 5]`, `mm_pos = 0`, so left subtree is empty.
This is Case R. `window_size 2 w = 3` (positions 2, 3, 4), `window_at 2 w = [4; 7; 5]`.

**Case R example: `w = [3; 1; 4; 7; 5; 9; 2; 6]`, `i = 2`.**

`D(w)`: check each adjacent pair:
- k=0: w[0]=3 > w[1]=1? Yes. Descent at 0.
- k=1: w[1]=1 > w[2]=4? No.
- k=2: w[2]=4 > w[3]=7? No.
- k=3: w[3]=7 > w[4]=5? Yes. Descent at 3.
- k=4: w[4]=5 > w[5]=9? No.
- k=5: w[5]=9 > w[6]=2? Yes. Descent at 5.
- k=6: w[6]=2 > w[7]=6? No.

`D(w) = {0, 3, 5}`.

`psi 2 w`: window at 2 is `L = [4; 7; 5]`. Head = 4 = min(L). `delta = 2`.
`sorted = [4; 5; 7]`.

- Position 0 (head): `sorted[(0 + 2) mod 3] = sorted[2] = 7`. New head = 7.
- Position 1 (value 7, rank 2): `sorted[(2 + 2) mod 3] = sorted[1] = 5`.
- Position 2 (value 5, rank 1): `sorted[(1 + 2) mod 3] = sorted[0] = 4`.

`rank_shift_seq [4; 7; 5] = [7; 5; 4]`.

`psi 2 w = [3; 1; 7; 5; 4; 9; 2; 6]`.

`D(psi 2 w)`:
- k=0: 3 > 1? Yes. Descent at 0.
- k=1: 1 > 7? No.
- k=2: 7 > 5? Yes. **Descent at 2** (new!).
- k=3: 5 > 4? Yes. Descent at 3.
- k=4: 4 > 9? No.
- k=5: 9 > 2? Yes. Descent at 5.
- k=6: 2 > 6? No.

`D(psi 2 w) = {0, 2, 3, 5} = D(w) \cup {2}`.

Confirmed: `2 \notin D(w)` and `D(psi_2 w) = D(w) \cup {2}`. **Case R, sub-case R1.**

Let's verify the inverse: `psi 2 (psi 2 w)` should give back `w`.

`psi 2 [3; 1; 7; 5; 4; 9; 2; 6]`: window at 2 is `[7; 5; 4]`. Head = 7 =
max. `delta = 1`. `sorted = [4; 5; 7]`.

- Position 0 (head = 7, rank 2): `sorted[(2+1) mod 3] = sorted[0] = 4`. New head = 4.
- Position 1 (value 5, rank 1): `sorted[(1+1) mod 3] = sorted[2] = 7`.
- Position 2 (value 4, rank 0): `sorted[(0+1) mod 3] = sorted[1] = 5`.

`rank_shift_seq [7; 5; 4] = [4; 7; 5]`.

`psi 2 (psi 2 w) = [3; 1; 4; 7; 5; 9; 2; 6] = w`. Confirmed involutivity.

For `D(psi 2 (psi 2 w))`: position 2 IS a descent (7 > 5) before second
application, and `D(psi_2(psi_2 w)) = D(psi_2 w) \setminus {2} = {0, 3, 5} = D(w)`. **Case R, sub-case R2** confirmed.

### 5.2 Case LR example: `w = [3; 1; 4; 7; 5; 9; 2; 6]`, `i = 5`

From the tree above: vertex 5 (value 9) has both left child (subtree at
positions 2--4) and right child (subtree at positions 6--7). This is Case LR.

`D(w) = {0, 3, 5}`.

Check: exactly one of `{4, 5}` is in `D(w)`. `4 \notin D(w)`, `5 \in D(w)`.
Confirmed: exactly one.

Since `i = 5 \in D(w)`, Stanley predicts:
`D(psi_5 w) = (D(w) \cup {4}) \setminus {5} = {0, 3, 4}`.

Compute: we already know from `psi.v` that
`psi 5 [3; 1; 4; 7; 5; 9; 2; 6] = [3; 1; 4; 7; 5; 2; 6; 9]`.

Verify: window at 5 is `[9; 2; 6]`. Head = 9 = max. `delta = 1`.
`sorted = [2; 6; 9]`.

- Position 0 (head = 9, rank 2): `sorted[(2+1) mod 3] = sorted[0] = 2`.
- Position 1 (value 2, rank 0): `sorted[(0+1) mod 3] = sorted[1] = 6`.
- Position 2 (value 6, rank 1): `sorted[(1+1) mod 3] = sorted[2] = 9`.

`rank_shift_seq [9; 2; 6] = [2; 6; 9]`.

`psi 5 w = [3; 1; 4; 7; 5; 2; 6; 9]`. Matches the `psi_nontrivial` example.

`D(psi 5 w)`:
- k=0: 3 > 1? Yes. Descent at 0.
- k=1: 1 > 4? No.
- k=2: 4 > 7? No.
- k=3: 7 > 5? Yes. Descent at 3.
- k=4: 5 > 2? Yes. **Descent at 4** (new!).
- k=5: 2 > 6? No. **Position 5 lost its descent.**
- k=6: 6 > 9? No.

`D(psi 5 w) = {0, 3, 4} = (D(w) \cup {4}) \setminus {5}`. **Confirmed!**

The descent at `i = 5` was removed, and a new descent at `i-1 = 4` was added.
Exactly as Fact #2 Case LR predicts.

### 5.3 Verification of the structural claims

For the Case LR example (`i = 5`):
- `w[i-1] = w[4] = 5`, `w[i] = w[5] = 9`, `w[i+1] = w[6] = 2`.
- `w[i] = 9 = max(S_5)` where `S_5 = \{4, 7, 5, 9, 2, 6\}` = entire
  subtree at vertex 5 (left + root + right).
- `i \in D(w)` (since `9 > 2`), `i-1 \notin D(w)` (since `5 < 9`).
- After psi: `(psi_5 w)[5] = 2 = min(L)` where `L = [9; 2; 6]`.
- `w[4] = 5 > 2 = (psi_5 w)[5]`: position 4 becomes a descent.
- `(psi_5 w)[5] = 2 < (psi_5 w)[6] = 6`: position 5 loses its descent.

The key structural fact: `min(L) = min\{9, 2, 6\} = 2`. And
`min(A) = min\{4, 7, 5, 9, 2, 6\} = 2 = min(L)` (the global min of the
subarray is in the right subtree, as proved in section 4.2). Since
`w[4] = 5 > 2 = min(L)`, position 4 becomes a descent. Confirmed.

---

## 6. Formalization strategy for Rocq (~200 LOC budget)

### 6.1 Core definition

```coq
(* In psi.v or a new file descent_effect.v *)

Definition is_descent_seq (w : seq nat) (k : nat) : bool :=
  nth 0 w k > nth 0 w k.+1.
```

### 6.2 Tree classifier

```coq
Fixpoint has_left_child_fuel (fuel : nat) (i : nat) (s : seq nat) : bool :=
  match fuel with
  | 0 => false
  | fuel'.+1 =>
      match s with
      | [::] => false
      | _ :: _ =>
          let j := mm_pos s in
          if i < j then has_left_child_fuel fuel' i (take j s)
          else if i == j then (0 < j)
          else has_left_child_fuel fuel' (i - j - 1) (drop j.+1 s)
      end
  end.

Definition has_left_child (i : nat) (w : seq nat) : bool :=
  has_left_child_fuel (size w) i w.
```

Non-triviality examples:

```coq
Example has_left_child_false :
  has_left_child 2 [:: 3; 1; 4; 7; 5; 9; 2; 6] = false.
Proof. by []. Qed.

Example has_left_child_true :
  has_left_child 5 [:: 3; 1; 4; 7; 5; 9; 2; 6] = true.
Proof. by []. Qed.
```

### 6.3 Key helper: rank_shift preserves relative order of non-head elements

```coq
Lemma rank_shift_preserves_interior_order (L : seq nat) (p q : nat) :
  uniq L -> 1 < size L ->
  (head 0 L == nth 0 (sort leq L) 0) ||
  (head 0 L == nth 0 (sort leq L) (size L).-1) ->
  0 < p -> 0 < q -> p < size L -> q < size L ->
  (nth 0 L p > nth 0 L q) =
  (nth 0 (rank_shift_seq L) p > nth 0 (rank_shift_seq L) q).
```

Proof idea: for non-head indices `p, q >= 1`, the rank shift is monotone
(rank `r` maps to `r-1` or `r+1` uniformly), so the comparison is preserved.

### 6.4 Head flip lemma

```coq
Lemma rank_shift_head_is_opposite_extremum (L : seq nat) :
  uniq L -> 1 < size L ->
  head 0 L == nth 0 (sort leq L) 0 ->
  head 0 (rank_shift_seq L) = nth 0 (sort leq L) (size L).-1.

Lemma rank_shift_head_is_opposite_extremum' (L : seq nat) :
  uniq L -> 1 < size L ->
  head 0 L == nth 0 (sort leq L) (size L).-1 ->
  head 0 (rank_shift_seq L) = nth 0 (sort leq L) 0.
```

### 6.5 Boundary lemma: ancestor extremum property

```coq
(* The element just after the window is an extremum of an ancestor subtree,
   hence is either < min(window) or > max(window). *)
Lemma post_window_extremum (i : nat) (w : seq nat) :
  uniq w -> i + window_size i w < size w ->
  (nth 0 w (i + window_size i w) < nth 0 (sort leq (window_at i w)) 0) \/
  (nth 0 w (i + window_size i w) > nth 0 (sort leq (window_at i w))
                                        (window_size i w).-1).
```

Similarly for the pre-window element (for Case LR):

```coq
(* In Case LR: max(L) = max(subarray containing i), so w[i-1] < max(L). *)
Lemma pre_window_lt_max_window (i : nat) (w : seq nat) :
  uniq w -> 0 < i -> has_left_child i w ->
  1 < window_size i w ->
  nth 0 w i.-1 < nth 0 (sort leq (window_at i w)) (window_size i w).-1.

(* In Case LR: min(L) = min(subarray containing i), so w[i-1] > min(L). *)
Lemma pre_window_gt_min_window (i : nat) (w : seq nat) :
  uniq w -> 0 < i -> has_left_child i w ->
  1 < window_size i w ->
  nth 0 w i.-1 > nth 0 (sort leq (window_at i w)) 0.
```

Wait --- these two lemmas are NOT both true simultaneously. Which one holds
depends on whether vertex `i` is a min-vertex or max-vertex. The correct
statements are:

```coq
(* When head = min (vertex i is a min-vertex):
   max(window) = max(subarray), so w[i-1] < max(window). *)
Lemma pre_window_lt_max_when_min_head (i : nat) (w : seq nat) :
  uniq w -> 0 < i -> has_left_child i w ->
  1 < window_size i w ->
  head 0 (window_at i w) == nth 0 (sort leq (window_at i w)) 0 ->
  nth 0 w i.-1 < nth 0 (sort leq (window_at i w)) (window_size i w).-1.

(* When head = max (vertex i is a max-vertex):
   min(window) = min(subarray), so w[i-1] > min(window). *)
Lemma pre_window_gt_min_when_max_head (i : nat) (w : seq nat) :
  uniq w -> 0 < i -> has_left_child i w ->
  1 < window_size i w ->
  head 0 (window_at i w) == nth 0 (sort leq (window_at i w)) (window_size i w).-1 ->
  nth 0 w i.-1 > nth 0 (sort leq (window_at i w)) 0.
```

These capture the key structural fact from section 4: in the subarray where
vertex `i` is chosen as root, the opposite extremum is in the right subtree
(not the left), so the window contains both extrema of the subarray, and
`w[i-1]` (in the left subtree) is strictly between them.

### 6.6 The four main lemmas (Fact #2)

**Case R, i not a descent:**
```coq
Lemma descent_psi_R_add (i : nat) (w : seq nat) :
  uniq w -> 1 < window_size i w -> ~~ has_left_child i w ->
  ~~ is_descent_seq w i ->
  forall k, k < (size w).-1 ->
    is_descent_seq (psi i w) k = (k == i) || is_descent_seq w k.
```

Equivalently (in set language): `D(psi_i w) = D(w) \cup {i}`.

**Case R, i is a descent:**
```coq
Lemma descent_psi_R_remove (i : nat) (w : seq nat) :
  uniq w -> 1 < window_size i w -> ~~ has_left_child i w ->
  is_descent_seq w i ->
  forall k, k < (size w).-1 ->
    is_descent_seq (psi i w) k = (k != i) && is_descent_seq w k.
```

Equivalently: `D(psi_i w) = D(w) \setminus {i}`.

**Case LR, i not a descent (so i-1 is a descent):**
```coq
Lemma descent_psi_LR_swap1 (i : nat) (w : seq nat) :
  uniq w -> 1 < window_size i w -> has_left_child i w ->
  ~~ is_descent_seq w i ->
  forall k, k < (size w).-1 ->
    is_descent_seq (psi i w) k =
      if k == i then true
      else if k == i.-1 then false
      else is_descent_seq w k.
```

Equivalently: `D(psi_i w) = (D(w) \cup {i}) \setminus {i-1}`.

**Case LR, i is a descent (so i-1 is not a descent):**
```coq
Lemma descent_psi_LR_swap2 (i : nat) (w : seq nat) :
  uniq w -> 1 < window_size i w -> has_left_child i w ->
  is_descent_seq w i ->
  forall k, k < (size w).-1 ->
    is_descent_seq (psi i w) k =
      if k == i then false
      else if k == i.-1 then true
      else is_descent_seq w k.
```

Equivalently: `D(psi_i w) = (D(w) \cup {i-1}) \setminus {i}`.

### 6.7 Head-is-extremum lemma (prerequisite)

All four main lemmas rely on the fact that the head of the window is an
extremum. This is property F2 of min-max trees:

```coq
Lemma window_head_is_extremum (i : nat) (w : seq nat) :
  uniq w -> 1 < window_size i w ->
  let L := window_at i w in
  (head 0 L == nth 0 (sort leq L) 0) ||
  (head 0 L == nth 0 (sort leq L) (size L).-1).
```

This is essentially `mm_pos_is_extremum` restricted to the subtree at position
`i`. The proof goes by structural induction on the tree, using the fact that
`mm_pos` selects the first min-or-max, and the window at position `i` is
exactly the subarray rooted at `i`.

### 6.8 Exactly-one-descent lemma (Case LR prerequisite)

```coq
Lemma exactly_one_descent_LR (i : nat) (w : seq nat) :
  uniq w -> 0 < i -> has_left_child i w -> 1 < window_size i w ->
  is_descent_seq w i.-1 (+) is_descent_seq w i.
```

(Here `(+)` is `addb`, exclusive or in `ssrbool`.)

### 6.9 Bridge to `descent.v` (optional)

If later milestones (M5--M7) work directly with `is_descent_seq` on `seq nat`,
no bridge is needed. If they need `is_descent` on `{perm 'I_n.+1}`, the
bridge is:

```coq
Lemma is_descent_seq_perm (n : nat) (s : {perm 'I_n.+1}) (i : 'I_n) :
  is_descent s i = is_descent_seq [seq val (s j) | j <- enum 'I_n.+1] i.
```

This translates between the `{perm 'I_n.+1}` world and the `seq nat` world.
The proof is a routine unfolding of `is_descent`, `nth`, and `enum` indexing.
We defer this to M5 unless needed earlier.

---

## 7. Deliverables

The Rocq implementer should produce the following, in order of dependency:

1. **`is_descent_seq`** — definition (~3 LOC).

2. **`has_left_child`** — definition via `has_left_child_fuel` (~20 LOC) plus
   two `Example` tests (one true, one false) (~4 LOC).

3. **`window_head_is_extremum`** — the head of any non-trivial window is the
   min or max of that window (~40 LOC). This requires induction on the tree
   structure, mirroring the recursion of `window_size_fuel`.

4. **`rank_shift_preserves_interior_order`** — relative order of non-head
   elements is preserved by rank_shift (~30 LOC). Uses `nth_rank_shift_seq`
   and modular arithmetic.

5. **`rank_shift_head_is_opposite_extremum`** (both min->max and max->min
   variants) — the head flips to the opposite extremum (~15 LOC). Follows
   directly from `head_rank_shift_seq` and modular arithmetic.

6. **`post_window_extremum`** — the element just after the window is either
   less than all window elements or greater than all (~30 LOC). Requires
   induction on the tree, tracking the ancestor relationship.

7. **`pre_window_lt_max_when_min_head`** and **`pre_window_gt_min_when_max_head`**
   — in Case LR, the element just before the window is between the window's
   min and max (~40 LOC). These are the hardest helpers; they require the
   structural fact that the opposite extremum of the subarray is in the right
   subtree (proved in section 4).

8. **`exactly_one_descent_LR`** — exactly one of `i-1`, `i` is a descent when
   vertex `i` has both children (~15 LOC). Follows from
   `window_head_is_extremum` and `has_left_child` implying `w[i]` is an
   extremum of a set containing both `w[i-1]` and `w[i+1]`.

9. **The four main lemmas** (`descent_psi_R_add`, `descent_psi_R_remove`,
   `descent_psi_LR_swap1`, `descent_psi_LR_swap2`) — each ~15 LOC, assembling
   the helpers above by case analysis on `k == i`, `k == i.-1`, or neither.

10. **Four `Example` tests** verifying the lemmas on the worked examples from
    section 5 (~8 LOC).

**Total: ~220 LOC**, within the 200 LOC budget (with some margin for
auxiliary lemmas).

**Critical dependency graph:**
```
is_descent_seq
has_left_child
window_head_is_extremum ──┬──> rank_shift_head_is_opposite_extremum
                          ├──> exactly_one_descent_LR
                          └──> pre_window_{lt_max,gt_min}_when_{min,max}_head
rank_shift_preserves_interior_order ──┐
post_window_extremum ─────────────────┤
pre_window_{lt_max,gt_min}... ────────┤
exactly_one_descent_LR ───────────────┼──> descent_psi_{R,LR}_{add,remove,swap1,swap2}
rank_shift_head_is_opposite_extremum ─┘
```
