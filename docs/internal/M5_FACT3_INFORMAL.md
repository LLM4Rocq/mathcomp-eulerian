# Milestone 5: Fact #3 --- Phi_w(a+b, ab+ba) = Sum_{v in [w]} u_{D(v)}

**Source of truth.** Stanley, *Enumerative Combinatorics* vol. 1 (2nd ed.),
section 1.6.3, lines 274--329 of `refs/stanley_1_6_cdindex.txt`.

**Dependencies.**
- `psi.v` (Milestones 2--4): `psi`, `window_size`, `has_left_child`,
  `is_descent_seq`, `psi_comm`, `psi_involutive`, Fact #2 axioms
  (`descent_psi_R_add`, `descent_psi_R_remove`, `descent_psi_LR_swap1`,
  `descent_psi_LR_swap2`), `exactly_one_descent_LR`.
- `M2_PSI_INFORMAL.md`, `M4_DESCENT_EFFECT_INFORMAL.md`.

---

## 1. Setup and definitions

### 1.1 Characteristic monomial u_S

For a permutation w of [n], the **descent set** is

    D(w) = { k in {0, ..., n-2} | w[k] > w[k+1] }

(0-indexed; Stanley uses 1-indexed). The **characteristic monomial** of a
subset S of {0, ..., n-2} is the noncommutative word

    u_S = e_0 e_1 ... e_{n-2}

where e_k = b if k in S, e_k = a if k not in S (Stanley line 268--272).

For example, D(37485216) = {1,3,4,5} (0-indexed: positions where a descent
occurs), so u_{D(37485216)} = ababbba.

### 1.2 The tree classifier and Phi'_w, Phi_w

Let M(w) be the min-max tree of w. For each vertex at in-order position i
(0-indexed, 0 <= i <= n-1), define:

    f_i(w) =  c   if vertex i has a right child only (Case R: window_size > 1,
                    has_left_child = false),
              d   if vertex i has both children (Case LR: window_size > 1,
                    has_left_child = true),
              e   if vertex i is an endpoint (window_size = 1).

Set

    Phi'_w(c, d, e) = f_0 f_1 ... f_{n-1}

and

    Phi_w(c, d) = Phi'_w(c, d, 1)

where "1" denotes the empty word (i.e., delete all e-factors). Note that
Phi'_w and Phi_w depend only on the *unlabeled* tree shape of M(w), so they
are constant across the M-equivalence class [w] (Stanley line 291).

### 1.3 The M-equivalence class [w] and the group G_w

The group G_w = <psi_i : vertex i is internal> is isomorphic to
(Z/2Z)^{iota(w)}, where iota(w) = #{internal vertices} (Fact #1, psi.v
`psi_comm`, `psi_involutive`). Its elements are all products psi_{i_1} o
... o psi_{i_k} where {i_1, ..., i_k} ranges over subsets of the set
of internal vertices. The M-equivalence class is

    [w] = { psi(w) : psi in G_w }

and |[w]| = 2^{iota(w)}.

### 1.4 Statement (Fact #3)

**Fact #3.** For any w in S_n,

    Phi_w(a + b, ab + ba) = Sum_{v in [w]} u_{D(v)}.

That is: substitute c := a + b and d := ab + ba into the noncommutative
monomial Phi_w, expand (no commutativity!), and the result equals the sum
of characteristic monomials over the full M-equivalence class.

---

## 2. The independence structure

### 2.1 Affected positions of psi_i (from Fact #2)

By the Fact #2 axioms in `psi.v` (lines 960--992), each internal vertex i
modifies the descent set at a small, precisely determined set of positions:

- **Case R** (right-child only): psi_i toggles the descent bit at position i.
  Affected positions: {i}.

- **Case LR** (both children): psi_i swaps the descent bits at positions i-1
  and i (exactly one of which is a descent, by `exactly_one_descent_LR`).
  Affected positions: {i-1, i}.

- **Endpoint**: psi_i = id, no effect. Affected positions: empty.

### 2.2 Disjointness of affected position sets

**Claim.** For distinct internal vertices i and j, the affected position sets
are disjoint.

**Proof.** We must check that A(i) and A(j) are disjoint for every pair of
distinct internal vertices i != j, where A(i) in {{i}, {i-1, i}}.

The only potential overlap occurs when one of the following holds:

(a) A(i) = {i} and A(j) = {j} with i = j. Excluded since i != j.

(b) A(i) = {i-1, i} and A(j) = {j} with j = i-1 or j = i.
    - j = i is excluded.
    - j = i-1: vertex i is Case LR (both children), so by Stanley's key
      structural observation (line 259, formalized as the precondition structure
      in M4_DESCENT_EFFECT_INFORMAL.md section 1.3): when vertex i has both
      children, vertex i-1 is the rightmost leaf of the left subtree of vertex
      i, hence an **endpoint**. Therefore psi_{i-1} = id and vertex i-1 is not
      an internal vertex. So j = i-1 cannot be an internal vertex, and this
      case does not arise.

(c) A(i) = {i} and A(j) = {j-1, j} with i = j-1 or i = j.
    Symmetric to (b): if j has both children, then j-1 is an endpoint, so
    i = j-1 cannot be internal.

(d) A(i) = {i-1, i} and A(j) = {j-1, j} with {i-1, i} intersect {j-1, j}
    nonempty.
    - If i = j, excluded.
    - If i = j-1: vertex j is Case LR, so j-1 = i is an endpoint. But then
      vertex i is not internal, contradiction.
    - If i-1 = j: vertex i is Case LR, so i-1 = j is an endpoint, contradiction.
    - If i-1 = j-1: then i = j, excluded.

In every case, we reach either a contradiction or the disjointness follows.
QED.

### 2.3 Consequence: factored action on descent sets

The disjointness of affected position sets means that the action of G_w on
descent sets **factors** as a product of independent toggles/swaps at
non-overlapping positions. Concretely, for any subset I of the internal
vertices and any position k in {0, ..., n-2}:

    is_descent(psi_I w, k) =
      if k is the "main position" of some unique internal vertex i in I:
        (descent bit toggled according to Case R or Case LR for i)
      else:
        is_descent(w, k).

This factorization is the heart of Fact #3.

---

## 3. The product formula

### 3.1 Ordering and notation

Order the internal vertices as i_1 < i_2 < ... < i_{iota} where
iota = iota(w). Let I = {i_1, ..., i_iota}. For a subset S of I, write

    psi_S = composition of psi_{i} for i in S

(order does not matter by commutativity). The M-equivalence class is

    [w] = { psi_S(w) : S subseteq I }.

### 3.2 Decomposition by vertex type

Group the positions 0, 1, ..., n-1 into three types:

- **Type-e positions** (endpoints): the set E = {0, ..., n-1} \ I. These have
  window_size = 1, so psi_i = id. The descent bit at each position k in
  {0, ..., n-2} that is "owned" only by an endpoint is constant across [w].

- **Type-c positions** (right-child only): the set C of internal vertices i
  with has_left_child i w = false. Each such i has A(i) = {i}, and psi_i
  toggles the descent bit at position i.

- **Type-d positions** (both children): the set D_LR of internal vertices i
  with has_left_child i w = true. Each such i has A(i) = {i-1, i}, and psi_i
  swaps the descent bits at positions i-1 and i (toggling both).

### 3.3 The sum as a product

**Claim.**

    Sum_{S subseteq I} u_{D(psi_S(w))}
      = Product over positions 0, ..., n-2 of (contributions)

We decompose u_{D(v)} = e_0 e_1 ... e_{n-2} and factor the sum
over subsets S as a product over independent groups of positions.

For each internal vertex i_j, define the **local contribution** when
i_j is or is not included in S:

**Case c (right-child only, A(i) = {i}):**

  - i not in S: descent bit at position i is is_descent(w, i). Contributes
    letter e_i = a (if not descent) or b (if descent).
  - i in S: descent bit toggles. Contributes the opposite letter.
  - Sum over {in, out}: e_i + e_i' = a + b, regardless of the initial state.

**Case d (both children, A(i) = {i-1, i}):**

  - i not in S: descent bits at i-1 and i are (d_{i-1}, d_i). By
    `exactly_one_descent_LR`, exactly one is a descent. So the pair of letters
    is either (a, b) or (b, a).
  - i in S: the bits swap, so the pair flips: (a, b) -> (b, a) or vice versa.
  - Sum over {in, out}: ab + ba, regardless of the initial state.

  Note: position i-1 is an endpoint (Stanley line 259), so it has no
  independent toggle of its own. The pair {i-1, i} is "owned" entirely by
  vertex i.

**Endpoints** contribute a fixed letter (a or b) that does not vary across [w].

### 3.4 Assembly

Now write the sum:

    Sum_{S subseteq I} u_{D(psi_S(w))}
      = Sum_{S subseteq I} (e_0(S) e_1(S) ... e_{n-2}(S))

where e_k(S) is the letter at position k for the permutation psi_S(w).

Because the positions affected by different internal vertices are disjoint,
and the sum ranges over all 2^iota subsets (each internal vertex independently
in or out), the sum factors:

    = [product over endpoint positions k not paired with any d-vertex]
      * [product over c-vertices i_j of (a + b)]
      * [product over d-vertices i_j of (ab + ba)]

with the products taken in position order (left to right). The endpoint
positions contribute fixed letters, so they sit between the (a+b) and (ab+ba)
factors in the correct order.

Formally, walk through positions k = 0, 1, ..., n-2:

- If k is an endpoint position (not "owned" by any internal vertex):
  it contributes the fixed letter a or b.
- If k is the main position of a c-vertex: it contributes the factor (a + b).
- If k = i-1 for a d-vertex i: it contributes the first letter of (ab + ba).
  If k = i (the main position of a d-vertex): it contributes the second letter.
  Together the pair {i-1, i} contributes (ab + ba).

Now delete the endpoint factors (replace e -> empty word). What remains is
exactly the product of (a + b) for each c-vertex and (ab + ba) for each
d-vertex, in position order. This is precisely

    Phi_w(c := a + b, d := ab + ba).

QED.

### 3.5 Why deleting endpoints is correct

When we form Phi'_w = f_0 ... f_{n-1} and set e = 1 (empty word) to get
Phi_w, we delete the e-factors. On the sum side, the endpoint positions
contribute fixed letters that sit between the (a+b) and (ab+ba) factors.
But these endpoint letters are *not* part of the u_S monomials at those
positions --- wait, they are. Let us be more precise.

The u_S monomial has n-1 letters (for positions 0, ..., n-2), whereas Phi'_w
has n letters (for vertices 0, ..., n-1). The vertex at position i
corresponds to descent-set position i (the bit between w[i] and w[i+1]). An
endpoint at position i contributes a fixed letter in u_S at position i, and
a c-vertex at position i contributes (a + b) at position i, and a d-vertex
at position i contributes (ab + ba) at positions i-1 and i.

The key subtlety: Phi'_w has n factors (one per vertex) while u_S has n-1
letters (one per descent position). The alignment works as follows:

- The last vertex (position n-1) has no descent position (there is no w[n]).
  If it is an endpoint (e), it is deleted anyway when passing to Phi_w.
  If it is a c-vertex or d-vertex, its contribution to (a+b) or (ab+ba)
  involves position n-1 of the descent set. But position n-1 does not exist
  in D(w) since D(w) is a subset of {0, ..., n-2}. In fact, vertex n-1 is
  always an endpoint (the rightmost element in the in-order traversal is
  always a leaf of M(w)), so this issue does not arise.

Wait --- that is not quite right in general. The rightmost vertex could be
internal if it has a right child. But the in-order traversal's last element
is the rightmost node of the tree, which has no right subtree, so it is
indeed an endpoint. Correct: vertex n-1 is always an endpoint.

Therefore Phi'_w = f_0 ... f_{n-2} e (the last factor is always e), and
Phi_w = f_0 ... f_{n-2} (the last factor is deleted). The remaining n-1
factors align exactly with the n-1 descent positions.

For these n-1 factors: the correspondence vertex i <-> descent position i
(for 0 <= i <= n-2) gives exactly the product formula above. Endpoint
factors become fixed letters (matching the fixed descent bits), c-factors
become (a+b), d-factors become (ab+ba). Deleting the fixed-letter factors
and replacing them with 1 on both sides gives Phi_w(a+b, ab+ba).

Actually, we should **not** delete the fixed letters on the sum side! The
correct statement is: the full sum Sum u_{D(v)} with all its letters (fixed
and varying) equals the product of all factors including the fixed endpoint
letters. This is Phi'_w(a+b, ab+ba, a-or-b). To get the clean statement
Fact #3, we observe:

    Phi_w(a+b, ab+ba) = Phi'_w(a+b, ab+ba, 1)

and on the sum side, "deleting" the endpoint factors corresponds to...
no, this is not how it works.

Let me restate cleanly. The substitution Phi_w(c := a+b, d := ab+ba)
replaces each c by (a+b) and each d by (ab+ba) in the word Phi_w. This
gives a sum of noncommutative monomials in a, b. Each monomial in the
expansion has deg(Phi_w) letters, where deg(Phi_w) = #{c-vertices} +
2 * #{d-vertices} = #{c-vertices} + 2 * #{d-vertices}.

On the other hand, u_{D(v)} has n-1 letters. So the equality
Phi_w(a+b, ab+ba) = Sum u_{D(v)} requires:

    #{c-vertices} + 2 * #{d-vertices} = n - 1.

**Verification:** Each c-vertex contributes 1 to the letter count (position
i). Each d-vertex contributes 2 (positions i-1 and i). Each endpoint
contributes 1 fixed letter. Total letters in Phi'_w(a+b, ab+ba, a-or-b):

    #{e-vertices} + #{c-vertices} + 2 * #{d-vertices}.

But Phi'_w has n factors (positions 0 to n-1), and vertex n-1 is an
endpoint, so positions 0 to n-2 have n-1 factors. The letter count for
positions 0 to n-2 is:

    #{endpoints in 0..n-2} + #{c-vertices} + 2 * #{d-vertices}.

We need this to equal n-1. This holds because each position 0 to n-2 is
either an endpoint (contributing 1 letter), a c-vertex (contributing 1
letter), or a d-vertex (contributing 2 letters, but one of those letters is
at position i-1 which is an endpoint). So the count is:

    (n-1) - #{d-vertices} + 2 * #{d-vertices} = n - 1 + #{d-vertices}.

That is wrong. The issue is that d-vertex i "absorbs" position i-1 (an
endpoint) into its (ab+ba) factor. Let me count more carefully.

**Correct counting.** The descent positions 0, ..., n-2 partition as:

- Free endpoints: positions that are endpoints and NOT i-1 for any d-vertex.
- Paired endpoints: positions i-1 for d-vertices (these are endpoints by
  Stanley line 259).
- c-positions: positions that are c-vertices.
- d-positions: positions that are d-vertices.

Number of letters in the u_S monomial: n-1 (one per descent position).

In Phi_w (with e deleted), the factors are c (for c-vertices) and d (for
d-vertices). Substituting c := a+b gives 2 terms per c-factor, each of
length 1. Substituting d := ab+ba gives 2 terms per d-factor, each of
length 2. A generic monomial in the expansion has length:

    #{c-vertices} + 2 * #{d-vertices}.

For this to match n-1, we need:

    #{c-vertices} + 2 * #{d-vertices}
      = #{free-endpoints} + #{paired-endpoints} + #{c-vertices} + #{d-vertices}
      = (n-1).

So: #{free-endpoints} + #{paired-endpoints} = #{d-vertices}... no.

The (n-1) descent positions partition into:
- Endpoints (not paired): #E' of them.
- Endpoints (paired = i-1 for d-vertex i): exactly #{d-vertices} of them.
- c-vertices: #C of them.
- d-vertices: #D of them.

So #E' + #D + #C + #D = n-1, i.e., #E' + #C + 2#D = n-1.

And Phi_w has #C factors of c and #D factors of d. The letter count of
Phi_w(a+b, ab+ba) expanded as monomials is #C * 1 + #D * 2 = #C + 2#D.

For this to equal n-1 we need #E' = 0, i.e., every endpoint in {0, ..., n-2}
is paired with some d-vertex. This is clearly false in general (consider a
path tree with all right children: every vertex except the last is a
c-vertex, there are no d-vertices, no endpoints in {0,...,n-2}, so #E' = 0
and #C = n-1, which gives #C = n-1. That works.)

But for a tree with endpoints that are not paired: consider w = [2,1,3].
Tree: root=1 (min), left=2, right=3. Vertex 0 (label 2): endpoint. Vertex 1
(label 1): right child only (c-vertex). Vertex 2 (label 3): endpoint.
Phi'_w = ece. Phi_w = c. Phi_w(a+b) = a+b, which has 1 letter.
u_{D(v)} has 2 letters. [w] = {213, 312} (psi_1 swaps 213 -> 312).
u_{D(213)} = ba. u_{D(312)} = ab. Sum = ba + ab = ab + ba. But Phi_w = c,
so Phi_w(a+b, ab+ba) = a+b. And ab + ba != a+b.

Wait --- I made an error. Let me recompute. w = [2,1,3] = 213.
- mm_pos([2,1,3]): min=1 at pos 1, max=3 at pos 2. min_pos=1 <= max_pos=2,
  so mm_pos = 1. Root = w[1] = 1.
- Left subtree: take 1 [2,1,3] = [2]. Tree: Leaf with label 2.
- Right subtree: drop 2 [2,1,3] = [3]. Tree: Leaf with label 3.
- Vertex 0 (label 2): endpoint. Vertex 1 (label 1): has right child (3) but
  left child (2), so BOTH children! Type d.
- Vertex 2 (label 3): endpoint.

So Phi'_w = ede. Phi_w = d. Phi_w(a+b, ab+ba) = ab+ba.
D(213) = {0} (2 > 1). u_{D(213)} = ba.
psi_1(213): window at 1 is [1,3], rank_shift gives [3,1]. psi_1(213) = [2,3,1] = 231.
D(231) = {1} (3 > 1). u_{D(231)} = ab.
Sum = ba + ab = ab + ba. Matches! Good.

Note that vertex 1 is type d (both children), so Phi_w = d, and the
endpoint at position 0 is the paired endpoint (i-1 = 0 for d-vertex i=1).
The only free endpoint is position 2 (vertex 2), but vertex 2 = n-1 is
deleted. So #E' = 0 among positions {0, ..., n-2}.

The general argument: among positions {0, ..., n-2}, every endpoint that is
not paired with a d-vertex would contribute a fixed letter on the sum side
but no corresponding factor in Phi_w. However, such "free" endpoints do not
exist. Why? Consider an endpoint at position k (0 <= k <= n-2). Vertex k has
window_size 1, so it has no right child. Since k < n-1, vertex k+1 exists.
In the in-order traversal, vertex k is immediately followed by vertex k+1,
which means vertex k is the rightmost node of the left subtree of some
ancestor. Specifically, vertex k+1 is the nearest ancestor of vertex k that
is to its right. This means vertex k is the rightmost leaf of the left
subtree of vertex k+1. Hence vertex k+1 has a left child (vertex k is in its
left subtree), so vertex k+1 is either type d or... vertex k+1 may have
vertex k deep in its left subtree, not as an immediate left child.

Actually, the correct statement from Stanley line 259 is more specific: if
vertex i has both children, then vertex i-1 is an endpoint AND is in the left
subtree of vertex i. The converse is what we need: if k is an endpoint with
k < n-1, then k = i-1 for some d-vertex i. This is indeed the case:

**Lemma.** If vertex k (0 <= k <= n-2) is an endpoint (leaf) of M(w), then
vertex k+1 has a left child, i.e., vertex k+1 is a d-vertex (assuming k+1 is
internal) or... vertex k+1 could also be an endpoint.

Hmm, consider w = [1, 2]. Tree: mm_pos = 0 (min=1 at pos 0). Root = 1.
Left subtree empty. Right subtree = [2]. Vertex 0 (label 1): right child
only, type c. Vertex 1 (label 2): endpoint. There are no free endpoints in
{0, ..., 0} = {0} since vertex 0 is type c. OK.

Consider w = [1, 3, 2]. mm_pos: min=1 at pos 0, max=3 at pos 1.
min_pos=0 <= max_pos=1, so root at pos 0, label 1. Type c (right only).
Right subtree = [3, 2]. mm_pos([3,2]): min=2 at pos 1, max=3 at pos 0.
max_pos=0 <= min_pos=1, so root at pos 0 of [3,2], i.e., pos 1 of w. Label
3. Left subtree of [3,2]: empty. Right subtree: [2]. So vertex 1 (label 3):
right child only, type c. Vertex 2 (label 2): endpoint.
Phi'_w = cce. Phi_w = cc. Phi_w(a+b, ab+ba) = (a+b)(a+b).
[w] has 4 elements (2 internal vertices, 0 d-vertices, iota=2).
- w = 132: D = {1} (3>2). u = ab.
- psi_0(132) = 312 (rank_shift [1,3,2] at 0: window = [1,3,2], shift to
  [3,2,1]... wait, let me just trust the formula). Actually psi_0: window at
  0 is the whole thing [1,3,2], size 3. rank_shift maps min-head 1 to max
  head 3, so [3,2,1]. psi_0(132) = 321. D(321) = {0,1}. u = bb.
- psi_1(132): window at 1 is [3,2], size 2. rank_shift: max-head 3 -> min
  head 2. [2,3]. psi_1(132) = [1,2,3] = 123. D(123) = {}. u = aa.
- psi_0 psi_1(132) = psi_0(123). Window at 0 is [1,2,3], size 3. rank_shift
  min-head 1 -> max 3: [3,2,1]... no: rank_shift [1,2,3]: head=1=min,
  replace by max=3, rest keep relative order: [3,2,...]. Rest is [2,3], ranks
  shifted by -1: [1,2] -> nah. rank_shift_seq [1,2,3]: sorted = [1,2,3].
  head=1=sorted[0]. Shift: map x -> (x-1 mod 3). 1->0, 2->1, 3->2. Using
  the actual rank_shift_seq: each element v maps to sorted[(index(v,sorted)+1)
  mod n] if head=min, or sorted[(index(v,sorted)-1) mod n] if head=max.
  Head=1=min. 1 -> sorted[(0+1)%3] = sorted[1] = 2. No wait, rank_shift
  replaces head with the opposite extremum and shifts others. The definition
  in psi.v: rank_shift_seq L replaces head (the extremum) with the opposite
  extremum, and the remaining elements keep their relative order but with
  shifted ranks. For [1,2,3] with head=1=min: new head = 3 (max). Remaining
  [2,3] get ranks shifted: they become the smallest |L|-1 = 2 elements of
  the new range. Since head went from min to max, the remaining elements'
  ranks decrease by 1: [2,3] -> [1,2]. So rank_shift [1,2,3] = [3,1,2].
  psi_0(123) = [3,1,2] = 312. D(312) = {0}. u = ba.
- [w] = {132, 321, 123, 312}. Sum = ab + bb + aa + ba = (a+b)(a+b). Matches
  Phi_w = cc -> (a+b)(a+b). Good.

Note: no free endpoints among {0, 1} since vertices 0 and 1 are both
type c.

**General proof that #E' = 0:** An endpoint at position k with 0 <= k <= n-2
means vertex k is a leaf. In the in-order traversal, vertex k is followed by
vertex k+1 (its in-order successor). By a standard property of binary trees,
the in-order successor of a leaf is its lowest ancestor that has the leaf in
its left subtree. This ancestor has vertex k+1 at in-order position k+1 and
has vertex k in its left subtree, hence has a left child. So vertex k+1 has
a left child (type d), and k = (k+1) - 1 is the paired endpoint for vertex
k+1.

But wait: vertex k+1 also needs to be internal (have a right child). Could
vertex k+1 be an endpoint too? If vertex k+1 is an endpoint, then it has no
right child. Since the in-order successor of vertex k is vertex k+1, and
vertex k+1 is an ancestor of vertex k with vertex k in its left subtree,
vertex k+1 has at least a left child. But "endpoint" means no children at
all (window_size = 1). So if vertex k+1 has a left child, it cannot be an
endpoint. Hence vertex k+1 is internal with a left child, i.e., type d.

Actually, I need to be more careful. "Endpoint" in Stanley's terminology
for min-max trees means "has no right child" (since no vertex has only a
left child, by property F1). Having no right child means window_size = 1.
But a vertex CAN have a left child while having no right child --- except
that property F1 says this cannot happen! So "endpoint" = "leaf" (no
children at all), confirming the argument above.

Therefore: every endpoint in {0, ..., n-2} is the paired endpoint i-1 of
some d-vertex i, and #E' = 0. This gives:

    n - 1 = #{paired-endpoints} + #{c-vertices} + #{d-vertices}
          = #{d-vertices} + #{c-vertices} + #{d-vertices}
          = #C + 2#D

which matches the letter count of Phi_w(a+b, ab+ba). The product formula
is valid.

---

## 4. Worked example: w = 315426

From Stanley Figure 1.12 (lines 304--329).

### 4.1 Tree construction

w = [3, 1, 5, 4, 2, 6].

- mm_pos([3,1,5,4,2,6]): min=1 at pos 1, max=6 at pos 5. min first.
  Root at pos 1, label 1. Type: left subtree = [3] (nonempty), right subtree
  = [5,4,2,6]. Has both children -> type d.
- Left subtree [3]: leaf. Vertex 0 (label 3): endpoint.
- Right subtree [5,4,2,6]:
  mm_pos([5,4,2,6]): min=2 at pos 2, max=6 at pos 3. min first.
  Root at pos 2 of [5,4,2,6] = pos 4 of w, label 2. Left subtree = [5,4],
  right subtree = [6]. Has both children -> type d.
  - Left subtree [5,4]:
    mm_pos([5,4]): min=4 at pos 1, max=5 at pos 0. max first.
    Root at pos 0 of [5,4] = pos 2 of w, label 5. Right subtree = [4].
    No left subtree -> type c.
    - Right subtree [4]: leaf. Vertex 3 (label 4): endpoint.
  - Right subtree [6]: leaf. Vertex 5 (label 6): endpoint.

Summary of vertices (0-indexed):

| Position | Label | Type     | Phi'_w factor |
|----------|-------|----------|---------------|
| 0        | 3     | endpoint | e             |
| 1        | 1     | d (LR)   | d             |
| 2        | 5     | c (R)    | c             |
| 3        | 4     | endpoint | e             |
| 4        | 2     | d (LR)   | d             |
| 5        | 6     | endpoint | e             |

Phi'_w = edcede. Phi_w = dcd.

### 4.2 Internal vertices and their affected positions

Internal vertices: {1, 2, 4} (iota = 3).

| Vertex | Type | A(vertex)   |
|--------|------|-------------|
| 1      | d    | {0, 1}      |
| 2      | c    | {2}         |
| 4      | d    | {3, 4}      |

Sets are pairwise disjoint: {0,1}, {2}, {3,4}. Check.

### 4.3 The 8 permutations and their descent sets

G_w = <psi_1, psi_2, psi_4> ~ (Z/2Z)^3. The 8 elements of [w]:

| Subset S      | psi_S(w)  | D(psi_S(w)) (0-indexed) | u_{D}  |
|---------------|-----------|-------------------------|--------|
| {}            | 315426    | {0, 3}                  | babba  |
|               |           | (3>1, 4>2)              |        |
| {2}           | 314526    | {0, 2, 3}               | baaba  |
|               |           | Wait, let me recompute. |        |

Let me be more careful. w = 315426.
D(315426): 3>1 yes(0), 1<5 no(1), 5>4 yes(2)... wait:

w = [3, 1, 5, 4, 2, 6]:
- pos 0: 3 > 1? yes. Descent at 0.
- pos 1: 1 > 5? no.
- pos 2: 5 > 4? yes. Descent at 2.
- pos 3: 4 > 2? yes. Descent at 3.
- pos 4: 2 > 6? no.

D(w) = {0, 2, 3}. u = baba b a -> wait, u has 5 letters for n=6.
u = e_0 e_1 e_2 e_3 e_4 = b a b b a = babba.

Hmm, but D = {0, 2, 3} gives e_0=b, e_1=a, e_2=b, e_3=b, e_4=a = babba.
Yes, matches Stanley line 318.

Now from Stanley Figure 1.12:

| Permutation | Stanley name | u_{D} |
|-------------|-------------|--------|
| 315426      | w           | babba  |
| 364215      | psi_2 w     | abbba  |
| 314526      | psi_3 w     | baaba  |
| 315462      | psi_5 w     | babab  |
| 362415      | psi_2 psi_3 w | ababa |
| 364251      | psi_2 psi_5 w | abbab |
| 314562      | psi_3 psi_5 w | baaab |
| 362451      | psi_2 psi_3 psi_5 w | abaab |

Note: Stanley uses 1-indexed psi. His psi_2, psi_3, psi_5 correspond to our
psi_1, psi_2, psi_4 (subtracting 1 for 0-indexing).

Sum = babba + abbba + baaba + babab + ababa + abbab + baaab + abaab.

Group by the affected position sets:
- Positions {0,1} (vertex 1, type d): varies over {ba, ab} (first two letters).
- Position {2} (vertex 2, type c): varies over {b, a} (third letter).
- Positions {3,4} (vertex 4, type d): varies over {ba, ab} (last two letters).

The sum factors as:

    (ba + ab)(b + a)(ba + ab)
    = (ab + ba)(a + b)(ab + ba)
    = d * c * d

with c = a+b, d = ab+ba. This is Phi_w(a+b, ab+ba) = dcd(a+b, ab+ba).
Matches Stanley line 310. QED for the example.

### 4.4 Verification of each permutation

Let us verify a few using our psi:

**psi_2 w (our psi_1):** Vertex 1 is type d, has_left_child = true.
Window at 1 of [3,1,5,4,2,6] = take (window_size 1 w) (drop 1 w).
We need window_size 1 w. In the tree, vertex 1 (label 1) is the root of
subtree with right subtree [5,4,2,6], so window_size = 1 + 4 = 5.
Window = [1,5,4,2,6]. Head = 1 = min. rank_shift: replace 1 with max = 6,
shift rest down: [5,4,2,6] -> [5,4,2,... ] with ranks shifted.
Actually: sorted window = [1,2,4,5,6]. Head=1=sorted[0]. rank_shift maps
each to sorted[(index+1) mod 5]. So 1->2, 5->6, 4->5, 2->4, 6->1.
Wait no, rank_shift replaces head by opposite extremum and others keep
relative order. So: head 1 -> 6. Others [5,4,2,6] keep relative order
but map to {1,2,4,5}: 5->5, 4->4, 2->2, 6->1. No: they keep relative
ORDER and fill in the remaining values {2,4,5} (sorted: 2,4,5). The
relative order of [5,4,2] is [large, medium, small], so they become [5,4,2].
And the last element 6 also shifts. Let me just check against Stanley:
psi_2 w = 364215 (Stanley). So our psi_1([3,1,5,4,2,6]) should give
[3,6,4,2,1,5]. Hmm, that is 364215 in 1-indexed Stanley notation?
Stanley writes permutations as values, so 364215 means w(1)=3, w(2)=6,
w(3)=4, w(4)=2, w(5)=1, w(6)=5, i.e., the sequence [3,6,4,2,1,5].

D([3,6,4,2,1,5]):
- 3<6 no, 6>4 yes(1), 4>2 yes(2), 2>1 yes(3), 1<5 no.
D = {1,2,3}. u = a b b b a = abbba. Matches Stanley.

---

## 5. Formalization strategy

### 5.1 Recommended approach: Option A (direct, no polynomial ring)

We avoid introducing noncommutative polynomial rings entirely. Instead, we
state Fact #3 as an identity about finite sums of sequences (words in {a, b}),
using MathComp's `bigop` machinery.

The key insight: both sides of Fact #3 are **formal sums of words** in the
free monoid {a, b}*. We can represent each word as a `seq bool` (false = a,
true = b), so u_S is a `seq bool` of length n-1. The sum is a multiset
(or equivalently, a function `seq bool -> nat` counting multiplicities).

However, for the formalization it is cleaner to state Fact #3 as: the multiset
of characteristic monomials {u_{D(v)} : v in [w]} equals the multiset obtained
by expanding Phi_w(a+b, ab+ba). We can avoid multisets entirely by proving the
equivalent **pointwise** statement: for each word m in {a, b}^{n-1}, the number
of v in [w] with u_{D(v)} = m equals the number of ways to expand Phi_w(a+b,
ab+ba) to get m.

But even simpler: since the proof is by a product decomposition over
independent bit positions, the most natural Rocq statement is:

**For each subset S of {internal vertices}, define v_S = psi_S(w). Then
D(v_S) is determined position-by-position: at each non-affected position k,
the descent bit equals is_descent(w, k); at the affected positions of each
internal vertex i, the descent bit pattern is determined by whether i is in S.**

This is already essentially what Fact #2 says, applied independently at each
internal vertex.

### 5.2 Concrete Rocq definitions (~40 LOC)

```coq
(* The set of internal vertices *)
Definition is_internal (i : nat) (w : seq nat) : bool :=
  (i < size w) && (1 < window_size i w).

(* Apply a subset of psi operators *)
Definition apply_psis (S : seq nat) (w : seq nat) : seq nat :=
  foldl (fun w' i => psi i w') w S.

(* Characteristic monomial as a seq bool *)
Definition char_mono (w : seq nat) : seq bool :=
  [seq is_descent_seq w k | k <- iota 0 (size w).-1].

(* Phi'_w as a seq of {c, d, e} *)
Inductive cde := C_letter | D_letter | E_letter.

Definition phi'_w (w : seq nat) : seq cde :=
  [seq if window_size i w <= 1 then E_letter
       else if has_left_child i w then D_letter
       else C_letter
  | i <- iota 0 (size w)].

(* Phi_w: delete E_letter entries *)
Definition phi_w (w : seq nat) : seq cde :=
  [seq x <- phi'_w w | x != E_letter].
```

### 5.3 The main theorem (~60 LOC statement + proof skeleton)

The cleanest formalization avoids expanding Phi_w into a polynomial and
instead proves the equivalent **descent-bit decomposition** directly:

```coq
(* For each internal vertex i in a uniq sequence w, and each choice
   bit b_i in {true, false}, applying psi_i (when b_i = true) or not
   (when b_i = false) toggles the descent pattern at A(i) exactly as
   described by Fact #2, independently of the other choices. *)

(* Key lemma: descent set of psi_S(w) at position k depends only on
   whether the unique "owner" of k (if any) is in S. *)
Lemma descent_psi_subset (w : seq nat) (S : {set 'I_(size w)}) :
  uniq w ->
  forall k : 'I_(size w).-1,
    is_descent_seq (apply_psis_set S w) k =
      match owner k w with
      | None => is_descent_seq w k  (* endpoint-owned: fixed *)
      | Some i =>
          if i \in S then negb (is_descent_seq w k)  (* toggled *)
          else is_descent_seq w k                     (* unchanged *)
      end.
```

where `owner k w` returns `Some i` if position k is in the affected set A(i)
of internal vertex i, and `None` if k is not affected by any internal vertex.

The proof proceeds by induction on |S|, peeling off one element at a time and
using the Fact #2 axioms plus the disjointness of affected sets.

### 5.4 Connecting to Phi_w (the polynomial identity, ~40 LOC)

Once `descent_psi_subset` is proved, Fact #3 follows by:

1. Enumerating all 2^{iota(w)} subsets S of the internal vertices.
2. For each S, computing the characteristic monomial via `descent_psi_subset`.
3. Observing that the collection of monomials exactly matches the expansion
   of Phi_w(a+b, ab+ba) by the distributive law.

For the Rocq formalization, step 3 can be stated as: the multiset of
char_mono(psi_S(w)) over all S equals the multiset produced by expanding the
product [seq expand(f) | f <- phi_w w] where expand(C_letter) = {[false],
[true]} (i.e., {a, b}) and expand(D_letter) = {[false; true], [true; false]}
(i.e., {ab, ba}).

This multiset equality can be proved by showing that both sides, viewed as
functions from (seq bool of length n-1) to nat, agree on every input. The key
is that the product structure on the Phi_w side mirrors the independent-toggle
structure on the G_w side, with each factor contributing exactly the right set
of local patterns.

### 5.5 LOC estimate

| Component | LOC |
|-----------|-----|
| Definitions (is_internal, apply_psis, char_mono, phi_w, owner) | 40 |
| Disjointness of affected position sets (section 2.2) | 30 |
| descent_psi_subset (main inductive lemma) | 60 |
| Free-endpoint lemma (#E' = 0, section 3.5) | 30 |
| Multiset expansion equality (Phi_w side = G_w side) | 40 |
| **Total** | **~200** |

---

## 6. The key inductive step

### 6.1 Setup

Fix a uniq sequence w of length n. Let I = {i_1, ..., i_iota} be the set of
internal vertices (ordered). We prove `descent_psi_subset` by induction on
|S|.

**Base case** (S = empty): apply_psis_set {} w = w, and the formula says
is_descent(w, k) = is_descent(w, k) for all k. Trivial.

**Inductive step:** Let S = S' union {i} where i not in S'. We need to show:

    is_descent(psi_i(apply_psis_set S' w), k)
      = [formula with i added to S'].

Write v = apply_psis_set S' w. By induction hypothesis, is_descent(v, k) is
known for all k. We apply psi_i to v and use Fact #2.

The crucial point: to apply the Fact #2 axioms to v, we need:
- uniq v: holds because psi preserves uniq (psi is a permutation of values).
- window_size i v = window_size i w: holds because psi_j for j != i does not
  change the tree structure at position i (this follows from the disjointness
  of the affected position sets and the fact that the tree shape is invariant
  under psi).
- has_left_child i v = has_left_child i w: same reason.

Wait --- these invariance properties need to be established. They follow from
the stronger fact: **M(v) and M(w) have the same unlabeled tree shape** for
any v in [w] (Stanley line 291). In `psi.v` terms, this means:

```coq
Lemma window_size_psi (j i : nat) (w : seq nat) :
  uniq w -> window_size i (psi j w) = window_size i w.

Lemma has_left_child_psi (j i : nat) (w : seq nat) :
  uniq w -> has_left_child i (psi j w) = has_left_child i w.
```

These should be provable from the definition of psi (it only changes values,
not the tree structure determined by relative orderings within windows).
`window_size_psi_ancestor` in psi.v (line 687) is a partial version; the full
version is needed here.

### 6.2 The inductive step in detail

Given v = apply_psis_set S' w and the inductive hypothesis:

    is_descent(v, k) = F(k, S')    (known for all k)

Apply psi_i to v. By Fact #2 (using uniq(v), window_size i v = window_size i w,
has_left_child i v = has_left_child i w):

**Case R (vertex i has right child only):**

    is_descent(psi_i v, k) =
      if k = i then negb(is_descent(v, i))
      else is_descent(v, k)

    = if k = i then negb(F(i, S'))
      else F(k, S')

    = F(k, S' union {i}).    [since F(k, S union {i}) toggles at k=i]

**Case LR (vertex i has both children):**

    is_descent(psi_i v, k) =
      if k = i then negb(is_descent(v, i))
      else if k = i-1 then negb(is_descent(v, i-1))
      else is_descent(v, k)

    = F(k, S' union {i}).    [since F toggles at k in {i-1, i}]

In both cases, the induction goes through.

### 6.3 Why commutativity matters

The induction peels off generators in any order. We need the result to be
independent of the order. This is guaranteed by `psi_comm`: since the
generators commute, apply_psis_set S w is well-defined (does not depend on
the ordering of S). Formally:

```coq
Lemma apply_psis_comm (i j : nat) (w : seq nat) :
  psi i (psi j w) = psi j (psi i w).
```

This is `psi_comm` from psi.v (line 727).

---

## 7. Deliverables for the Rocq implementer

### 7.1 New file: `fact3.v` (~200 LOC)

**Imports:** `psi.v`, `mathcomp.ssreflect`, `mathcomp.fingroup` (for `{set}`).

**Section 1: Definitions (~40 LOC)**

```coq
Definition is_internal (i : nat) (w : seq nat) : bool :=
  (i < size w) && (1 < window_size i w).

Definition internal_verts (w : seq nat) : seq nat :=
  [seq i <- iota 0 (size w) | is_internal i w].

(* Sequential application of psi for indices in a list *)
Definition apply_psis (S : seq nat) (w : seq nat) : seq nat :=
  foldl (fun acc i => psi i acc) w S.

(* The "owner" of descent position k: the unique internal vertex
   whose affected set contains k, or None *)
Definition owner (k : nat) (w : seq nat) : option nat :=
  if is_internal k.+1 w && has_left_child k.+1 w then Some k.+1
  else if is_internal k w then Some k
  else None.

(* Characteristic monomial *)
Definition char_mono (w : seq nat) : seq bool :=
  [seq is_descent_seq w k | k <- iota 0 (size w).-1].

(* Tree-shape classifier *)
Inductive vertex_type := VT_e | VT_c | VT_d.

Definition classify_vertex (i : nat) (w : seq nat) : vertex_type :=
  if window_size i w <= 1 then VT_e
  else if has_left_child i w then VT_d
  else VT_c.

(* Phi_w as a sequence of vertex types, with VT_e removed *)
Definition phi_w_seq (w : seq nat) : seq vertex_type :=
  [seq x <- [seq classify_vertex i w | i <- iota 0 (size w)] | x != VT_e].
```

**Section 2: Structural lemmas (~30 LOC)**

```coq
(* Tree shape invariance under psi *)
Lemma window_size_psi_inv (j i : nat) (w : seq nat) :
  uniq w -> window_size i (psi j w) = window_size i w.

Lemma has_left_child_psi_inv (j i : nat) (w : seq nat) :
  uniq w -> has_left_child i (psi j w) = has_left_child i w.

(* Disjointness of affected position sets *)
Lemma owner_unique (k : nat) (w : seq nat) :
  uniq w ->
  forall i j, is_internal i w -> is_internal j w -> i != j ->
    k \in affected i w -> k \notin affected j w.

(* Every non-last endpoint is paired with a d-vertex *)
Lemma endpoint_paired (k : nat) (w : seq nat) :
  uniq w -> k < (size w).-1 ->
  ~~ is_internal k w ->
  is_internal k.+1 w && has_left_child k.+1 w.
```

**Section 3: Main theorem (~60 LOC)**

```coq
(* The core inductive lemma *)
Lemma descent_apply_psis (w : seq nat) (S : seq nat) :
  uniq w -> uniq S -> all (fun i => is_internal i w) S ->
  forall k, k < (size w).-1 ->
    is_descent_seq (apply_psis S w) k =
      if owner k w is Some i then
        if i \in S then negb (is_descent_seq w k)
        else is_descent_seq w k
      else is_descent_seq w k.
```

Proof sketch (by induction on S):
- Base: S = [::], apply_psis = id. Both sides equal is_descent_seq w k.
- Step: S = i :: S'. Apply IH to S', then apply Fact #2 for psi_i.
  The disjointness lemma ensures that adding i to S only affects positions
  in A(i), and the IH gives the correct formula for all other positions.

```coq
(* Fact #3: the multiset identity *)
Theorem fact3 (w : seq nat) :
  uniq w ->
  let n := size w in
  let I := internal_verts w in
  (* The multiset of char_mono(apply_psis S w) over all subsets S of I
     equals the expansion of Phi_w(a+b, ab+ba). *)
  perm_eq
    [seq char_mono (apply_psis S w) | S <- powerset I]
    (expand_phi (phi_w_seq w)).
```

where `expand_phi` computes the Cartesian product expansion:

```coq
Fixpoint expand_phi (fs : seq vertex_type) : seq (seq bool) :=
  match fs with
  | [::] => [::[::]]
  | VT_c :: fs' =>
      [seq [:: b & m] | b <- [:: false; true], m <- expand_phi fs']
  | VT_d :: fs' =>
      [seq [:: b1, b2 & m] | (b1, b2) <- [:: (false, true); (true, false)],
                               m <- expand_phi fs']
  | VT_e :: fs' => expand_phi fs'  (* should not occur in phi_w_seq *)
  end.
```

Note: The exact `perm_eq` statement may need adjustment depending on whether
we track position-aligned monomials or just collect them. An alternative
statement that avoids multisets entirely:

```coq
(* Alternative: for each word m, count occurrences on both sides *)
Theorem fact3_count (w : seq nat) :
  uniq w ->
  forall m : seq bool,
    count (pred1 m) [seq char_mono (apply_psis S w) | S <- powerset I]
    = count (pred1 m) (expand_phi (phi_w_seq w)).
```

### 7.2 Required new axioms or lemmas from psi.v

The following are NOT yet in `psi.v` and must be either axiomatized or proved:

1. **`window_size_psi_inv`**: `window_size i (psi j w) = window_size i w`.
   (Partially covered by `window_size_psi_ancestor` at line 687, but that
   only handles the ancestor case. The full statement is needed.)

2. **`has_left_child_psi_inv`**: `has_left_child i (psi j w) = has_left_child i w`.
   (Not in psi.v at all. Same justification as above: tree shape is invariant.)

3. **`psi_preserves_uniq`**: `uniq w -> uniq (psi i w)`.
   (Should follow from psi being a value-permutation. May already be implicit
   in the psi.v development but needs an explicit lemma.)

4. **`apply_psis_comm`** (derived from `psi_comm`): order-independence of
   foldl for commuting involutions. Standard group theory, ~20 LOC.

### 7.3 What NOT to formalize

- Do NOT introduce a noncommutative polynomial ring type. The free monoid
  `seq bool` suffices.
- Do NOT formalize the group G_w as an actual `finGroupType`. The set of
  subsets of internal vertices, combined with `apply_psis`, is a concrete
  enough representation.
- Do NOT attempt to prove `window_size_psi_inv` or `has_left_child_psi_inv`
  from first principles in this milestone. Axiomatize them (with non-triviality
  examples) and defer the proofs to a dedicated tree-invariance milestone.

### 7.4 Non-triviality tests

```coq
(* Fact #3 for w = [3;1;5;4;2;6] (Stanley's [315426] example) *)
Example fact3_ex :
  let w := [:: 3; 1; 5; 4; 2; 6] in
  let I := internal_verts w in  (* should be [:: 1; 2; 4] *)
  sort leq [seq char_mono (apply_psis S w) | S <- powerset I]
  = sort leq (expand_phi (phi_w_seq w)).
Proof. by native_compute. Qed.

(* Phi_w for [315426] is dcd *)
Example phi_w_315426 :
  phi_w_seq [:: 3; 1; 5; 4; 2; 6] = [:: VT_d; VT_c; VT_d].
Proof. by native_compute. Qed.

(* Internal vertices of [315426] *)
Example internal_315426 :
  internal_verts [:: 3; 1; 5; 4; 2; 6] = [:: 1; 2; 4].
Proof. by native_compute. Qed.

(* Non-trivial: the 8 permutations are all distinct *)
Example class_size_315426 :
  let w := [:: 3; 1; 5; 4; 2; 6] in
  let I := internal_verts w in
  uniq [seq apply_psis S w | S <- powerset I].
Proof. by native_compute. Qed.
```

---

## Summary

Fact #3 follows from three ingredients:

1. **Fact #2** (descent-set effect): each psi_i toggles/swaps descent bits at
   a known set of 1 or 2 positions.

2. **Disjointness** (from Stanley line 259): the affected position sets are
   pairwise disjoint, because whenever vertex i has both children, vertex i-1
   is an endpoint (hence not an internal vertex, hence no other psi_j affects
   position i-1).

3. **Completeness** (no free endpoints): every descent position in {0,...,n-2}
   is either owned by a c-vertex (contributing a+b) or paired with a d-vertex
   (contributing ab+ba). No position is left unaccounted for.

The product Phi_w(a+b, ab+ba) encodes exactly the independent choices at each
internal vertex, and the sum over [w] exhausts all 2^{iota(w)} combinations.
