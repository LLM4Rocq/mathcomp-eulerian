# Formal Proofs vs. Stanley EC1 Chapter 1

This document maps the formal Rocq/MathComp theorems to statements
in Stanley, *Enumerative Combinatorics* Vol. 1 (2nd ed.), Chapter 1.

---

## 1. Permutation Descent Statistics (Stanley §1.4)

### 1.1 Descents and Descent Sets

**Stanley (p.38):** If w = w_1 w_2 ... w_n in S_n and 1 <= i <= n-1,
then i is a *descent* of w if w_i > w_{i+1}. The *descent set* is
D(w) = {i : w_i > w_{i+1}} subset [n-1].

**Formal (`descent.v:22-25`):**
```coq
Definition is_descent s i : bool :=
  s (widen_ord (leqnSn n) i) > s (lift ord0 i).
Definition descent_set s : {set 'I_n} := [set i | is_descent s i].
```

**Indexing convention:** Stanley uses 1-based indexing on S_n (permutations
of {1,...,n}), with descents in [n-1] = {1,...,n-1}. The formalization
uses 0-based indexing: s : {perm 'I_{n+1}} (permutations of {0,...,n}),
with descents i : 'I_n (positions 0 through n-1). The position i is a
descent iff s(i) > s(i+1), encoded via `widen_ord` (maps i to itself in
'I_{n+1}) and `lift ord0` (maps i to i+1 in 'I_{n+1}).

**Key lemmas:**
| Formal | Stanley | Notes |
|--------|---------|-------|
| `des s = #\|descent_set s\|` | `des(w) = #D(w)` | Descent number (§1.4, p.74) |
| `des_le : des s <= n` | Implicit | |
| `des_add_asc : des s + asc s = n` | Implicit | asc = n - des |
| `des_id : des 1 = 0` | Identity has no descents | |

### 1.2 Reversal-Complement Symmetry

**Stanley (p.66, implicit):** The map w -> (n+1-w_n, ..., n+1-w_1)
sends descents to non-descents and vice versa.

**Formal (`descent.v:80-122`):**
```coq
Definition rev_perm s := rev_perm_ord * s.
Lemma is_descent_rev s i : is_descent (rev_perm s) i = ~~ is_descent s (rev_ord i).
Lemma des_rev_perm s : des (rev_perm s) = n - des s.
```
The map `rev_perm` composes with the reversal permutation. This gives
the symmetry `A(n,k) = A(n, n-k)` of Eulerian numbers.

---

## 2. Eulerian Numbers (Stanley §1.4, pp.74-87)

Stanley defines Eulerian numbers as A(d,k) = #{w in S_d : des(w) = k-1}
with the convention that A_d(x) = sum_k A(d,k) x^k starts at x^1.

### 2.1 Definition

**Stanley (eq. 1.36, p.74):** A(d,k) = #{w in S_d : 1 + des(w) = k}.

**Formal (`eulerian.v:14-15`):**
```coq
Definition eulerian (n k : nat) : nat :=
  #|[set s : {perm 'I_n.+1} | des s == k]|.
```

**Convention difference:** The formal `eulerian n k` counts permutations
of 'I_{n+1} with exactly k descents. Stanley's A(n,k) counts with k-1
descents. So `eulerian n k = A(n, k+1)` in Stanley's notation. However,
the formalization uses the more natural convention (matching OEIS A008292).

### 2.2 Row Sum

**Stanley (implicit):** sum_k A(d,k) = d!.

**Formal (`eulerian.v:31`):**
```coq
Lemma eulerian_row_sum_fact n : \sum_(k < n.+1) eulerian n k = n.+1`!.
```

### 2.3 Boundary Values

| Formal | Stanley | Statement |
|--------|---------|-----------|
| `eulerian_n_0 : eulerian n 0 = 1` | A(n,1) = 1 | Only identity has 0 descents |
| `eulerian_n_n : eulerian n n = 1` | A(n,n) = 1 | Only rev_perm_ord has n descents |
| `eulerian_out_of_range` | Implicit | eulerian n k = 0 for k > n |

### 2.4 Symmetry

**Stanley (§1.4, implicit from des_rev_perm):** A(n,k) = A(n, n+1-k).

**Formal (`eulerian.v:96-105`):**
```coq
Lemma eulerian_symm n k : k <= n -> eulerian n k = eulerian n (n - k).
```
Proved via the `rev_perm` bijection: s |-> rev_perm(s) sends des(s) = k
to des = n - k.

### 2.5 Recurrence

**Stanley (eq. 1.39, p.75):** A(d+1, k) = k * A(d,k) + (d-k+2) * A(d,k-1).

**Formal (`eulerian.v:466-503`):**
```coq
Lemma eulerian_rec n k :
  eulerian n.+1 k.+1 = k.+2 * eulerian n k.+1 + (n.+1 - k) * eulerian n k.
```

**Proof strategy:** Same as Stanley — the "insert-max-value" bijection.
Given sigma in S_{n+2}, let p = sigma^{-1}(max) and tau = sigma with
max deleted. Then des(sigma) depends on des(tau) and the insertion
position p.

**Formal infrastructure:**
- `insert_max_perm t p` (line 165): insert max at position p in tau
- `extract_max_perm` (line 211): inverse operation
- `insert_max_perm_bij` (line 445): bijection proof
- `des_insert_max_ord0/ord_max/interior` (lines 254-377): descent counting

**Why this path was chosen:** Stanley's proof on p.75 is a counting
argument: "choose w in S_d with k-1 descents, insert d+1 after a
descent position (k ways) or after an ascent position (d-k+2 ways)."
This is clean but implicitly defines a bijection without constructing it.

The formal proof makes the bijection explicit: `insert_max_perm t p`
constructs sigma from (tau, p), and `extract_max_perm` constructs the
inverse. The bijection proof (`insert_max_perm_bij`) then gives the
partition of S_{n+2} into fibers. This is more work (~300 LOC vs. a
paragraph) but is the natural approach in a proof assistant: rather
than counting elements of a set by describing how to construct them
(which requires showing no double-counting and no omissions), we
exhibit the bijection and derive the counting identity from it. In
MathComp, `reindex` and `partition_big` then handle the bookkeeping.

### 2.6 Worpitzky's Identity

**Stanley (Proposition 1.4.4, rewritten):**
x^{n+1} = sum_{k=0}^{n} A(n,k) * C(x+k, n+1).

**Formal (`eulerian.v:526-549`):**
```coq
Lemma worpitzky n x :
  x ^ n.+1 = \sum_(k < n.+1) eulerian n k * 'C(x + k, n.+1).
```
Proved by induction on n using `eulerian_rec` and the algebraic identity
`worpitzky_binom_id`.

### 2.7 Explicit Formula

**Stanley (not stated explicitly in §1.4, but derivable from Worpitzky):**
A(n,k) = sum_{j=0}^{k} (-1)^j C(n+2, j) (k+1-j)^{n+1}.

**Formal (`eulerian.v:631-673`):**
```coq
Lemma eulerian_explicit n k :
  (eulerian n k)%:Z =
    \sum_(j < k.+1) (-1) ^ j *+ 'C(n.+2, j) *+ (k.+1 - j) ^ n.+1.
```
Proved by Worpitzky inversion: substitute Worpitzky into the sum,
exchange summation order, and use `aux_id` (the alternating binomial
convolution identity sum_j (-1)^j C(n+2,j) C(t-j, n+1) = [t == n+1],
proved on lines 592-611 by induction using Pascal's identity).

**Why this path was chosen:** Stanley leaves the explicit formula as an
exercise derivable from Worpitzky. The formal proof goes through integer
arithmetic (`ssrint`, `ssralg`) because the alternating sum involves
(-1)^j terms that require working over Z rather than N. The `aux_id`
lemma is the key algebraic ingredient — it is a standalone identity
about alternating binomial sums that could be reused in other contexts.
The choice to work over Z and prove `aux_id` separately (rather than,
say, using inclusion-exclusion as in Stanley Exercise 2.22) keeps the
proof self-contained within Chapter 1 concepts.

---

## 3. Set-Refined Descent Counts (Stanley §1.4, eqs. 1.31-1.32)

### 3.1 beta(S)

**Stanley (eq. 1.32, p.38):** beta(S) = #{w in S_n : D(w) = S}.

**Formal (`beta.v:19`):**
```coq
Definition beta (n : nat) (D : {set 'I_n}) : nat :=
  #|[set sigma : {perm 'I_n.+1} | descent_set sigma == D]|.
```

### 3.2 Key Properties

| Formal | Stanley | Statement |
|--------|---------|-----------|
| `beta0 : beta set0 = 1` | beta({}) = 1 | Only identity |
| `beta_full : beta setT = 1` | beta([n-1]) = 1 | Only decreasing perm |
| `sum_beta_eq_fact` | Implicit | sum_D beta(D) = (n+1)! |
| `beta_eulerian` | eq. (1.63) context | sum_{D : #D = k} beta(D) = A(n,k) |
| `beta_compl : beta D = beta (~: D)` | Not in Stanley | Value-complement symmetry |

### 3.3 Connection to Eulerian Numbers

**Formal (`beta.v:124-134`):**
```coq
Lemma beta_eulerian n k :
  \sum_(D : {set 'I_n} | #|D| == k) beta D = eulerian n k.
```
This is the bridge: Eulerian numbers are the sum of beta over all descent
sets of a given cardinality.

---

## 4. The cd-Index (Stanley §1.6.3)

### 4.1 Min-Max Trees

**Stanley (p.57):** The min-max tree M(w) of w = a_1 ... a_n is defined
recursively: find the least j such that a_j = min or max of {a_1,...,a_n};
a_j is the root, with left subtree M(a_1,...,a_{j-1}) and right subtree
M(a_{j+1},...,a_n).

**Formal (`psi_core.v:30-108`):**
```coq
Definition mm_pos (s : seq nat) : nat := minn (min_pos s) (max_pos s).
Fixpoint window_size_fuel (fuel : nat) (i : nat) (s : seq nat) : nat := ...
Definition window_size (i : nat) (s : seq nat) : nat :=
  window_size_fuel (size s) i s.
```

**Design choice:** The formalization doesn't build an explicit tree data
type. Instead, it works with `mm_pos` (the root position) and
`window_size` (the size of the subtree at each position). The tree is
implicit in the recursive structure of these functions.

**Why:** An explicit binary tree type (e.g., `Inductive mmtree := Leaf |
Node of mmtree * nat * mmtree`) would require building and maintaining
a bijection between sequences and trees throughout the development. Every
lemma about `psi`, `phi_w`, `char_mono`, etc. would need to go through
this bijection. The "implicit tree" approach avoids this: the sequence
IS the representation, and tree properties (root position, subtree size,
left/right child existence) are computed directly from the sequence via
`mm_pos`, `window_size`, and `has_left_child`. This means psi operations
act directly on sequences (no tree reconstruction), and the inductive
structure is accessed via `take j w` / `drop (j+1) w` (left/right
subtrees as subsequences). The cost is that structural lemmas require
fuel-based recursion (`window_size_fuel`) with termination arguments,
but this is a one-time cost paid in `psi_core.v`.

### 4.2 The psi Operators

**Stanley (p.57, Fact #1):** The operators psi_i are commuting involutions
that permute the labels of M(w), generating a group G_w ~ (Z/2Z)^{iota(w)}.

**Formal (`psi_core.v`):**
```coq
Definition psi (j : nat) (w : seq nat) : seq nat := ...
```
The `psi j w` operator replaces the j-th element (root of subtree at j)
with the min or max of its right subtree, preserving relative order.
Key proved properties:
- `psi_involutive`: psi j (psi j w) = w (psi_core.v, proved)
- `psi_comm_disjoint/nested`: psi operators commute (psi_comm.v, proved)
- `size_psi`: size preserved (psi_core.v, proved)
- `uniq_psi`: uniqueness preserved (psi_core.v, proved)

### 4.3 cd-Word Classification

**Stanley (p.58):** For w = a_1 ... a_n, define f_i = c if a_i has only
a right child, d if a_i has left and right children, e if a_i is an
endpoint. Phi_w = f_1 ... f_n with e's deleted.

**Formal (`psi_cdindex.v:34-47`):**
```coq
Inductive cde := C_letter | D_letter | E_letter.
Definition classify_vertex_cde (i : nat) (w : seq nat) : cde :=
  if ~~ is_internal i w then E_letter
  else if has_left_child i w then D_letter
  else C_letter.
Definition phi_w (w : seq nat) : seq cde :=
  [seq x <- phi'_w w | match x with E_letter => false | _ => true end].
```

### 4.4 M-Equivalence and Characteristic Monomials

**Stanley (p.58):** Define u_S = e_1 ... e_{n-1} where e_i = a if i
not in S, b if i in S. Two permutations are M-equivalent if connected
by psi operators.

**Formal (`psi_cdindex.v:26-31`):**
```coq
Definition apply_psis (ops : seq nat) (w : seq nat) : seq nat :=
  foldl (fun w' i => psi i w') w ops.
Definition char_mono (w : seq nat) : seq bool :=
  [seq is_descent_seq w k | k <- iota 0 (size w).-1].
```
The M-equivalence class of w is {apply_psis(ss, w) | ss in powerset_internal(w)}.
The characteristic monomial `char_mono` encodes the descent pattern as a
boolean sequence (true = descent = b, false = ascent = a).

---

## 5. Theorem 1.6.3 and Proposition 1.6.4

### 5.1 Theorem 1.6.3: cd-Index Has Nonnegative Coefficients

**Stanley (p.60):** "The ab-index Psi_n can be written as a polynomial
Phi_n in the variables c = a+b and d = ab+ba. This polynomial is a sum
of E_n monomials."

**Formal: Fact #3 (`psi_cdindex_support.v`):**
```coq
Lemma fact3 : forall (w : seq nat),
  uniq w ->
  sort leq_seqb
    [seq char_mono (apply_psis ss w) | ss <- powerset_internal w]
  =
  sort leq_seqb (expand_cde (phi_w w)).
```

This is the key identity Phi_w(a+b, ab+ba) = sum_{v in [w]} u_{D(v)},
stated as a sorted multiset equality. The LHS lists the descent patterns
of all M-class members; the RHS lists the expansion of the cd-word Phi_w.

**Proof strategy (DIVERGES from Stanley):** Stanley states this as an
easy consequence of Fact #2 (descent-set changes under psi). The formal
proof uses a different approach:
1. A boolean checker `check_fact3` that verifies the sorted equality
2. Psi-invariance of the checker (`check_fact3_psi_invariant`)
3. Strong induction on size w with mm_pos decomposition
4. Base case (size <= 1) by computation
5. Inductive step: decompose at mm_pos, apply IH to subtrees, close
   by simplification (`by rewrite /check_fact3 /apply_psis /=`)

**Why this path was chosen:** Stanley's "easy consequence of Fact #2"
would require formalizing the product structure of expand_cde across
subtrees — showing that expand_cde(phi_w(w)) decomposes as a Cartesian
product expand_cde(phi_w(L)) x expand_cde([root_letter]) x
expand_cde(phi_w(R)). While expand_cde_cat (line 961) gives the
concatenation factorization, connecting it to the char_mono factorization
across subtrees requires reasoning about how descent bits in w decompose
into independent bits in L and R. Each psi operator affects one bit
independently (Fact #2), but formalizing this independence across all
2^k combinations is verbose.

The final proof uses a "membership + injectivity → perm_eq" argument:
1. `char_mono_self_mem`: every sequence's char_mono is in its own
   expand_cde (via phi_w_support_general + D_vertex_descent_transition)
2. `char_mono_apply_psis_mem`: extends to all M-class elements
3. `uniq_map_char_mono_powerset`: char_monos are pairwise distinct
   (pigeonhole: injective map into uniq target of same size)
4. `perm_eq_from_subset`: uniq + same size + subset → perm_eq

This produces small proof terms (~15GB -vo). An earlier version used
boolean reflection (check_fact3 + psi-invariance + `by ... /=` closing)
which was elegant but produced proof terms exceeding 100GB.

The structural proof creates a dependency inversion: fact3 uses
phi_w_support_general (originally downstream). This is resolved by
a file split: psi_cdindex_core.v (definitions), psi_cdindex_witness.v
(S_w, omega, witnesses), psi_cdindex_support.v (phi_w_support + fact3).

### 5.2 Support Characterization (phi_w_support_general)

**Stanley (p.61, in the proof of Prop 1.6.4):** "It is easy to see that
Phi_w = sum_{omega(X) supseteq S_w} u_X" where S_w = {i-1 : f_i = d}.

**Formal (`psi_cdindex_support.v`):**
```coq
Lemma phi_w_support_general (w : seq nat) (X : seq bool) :
  uniq w -> 2 <= size w -> size X = (size w).-1 ->
  (X \in expand_cde (phi_w w)) =
  all (fun k => k \in omega_seq [...]) (S_w_seq w).
```

**Proof strategy (DIVERGES from Stanley):** Stanley treats this as
obvious ("it is easy to see"). The formal proof requires substantial
work, decomposed into independent components:

1. `expand_cde_mem_iff`: characterize expand_cde membership as
   "transitions at D-offsets" (induction on cd-word, ~130 LOC)
2. `has_transition_omega_seq`: connect bit transitions to omega_seq
   membership (~30 LOC)
3. `cde_total_width_phi_w` and `D_offsets_phi_w_eq_S_w_seq`: structural
   properties of the min-max tree linking cd-word offsets to S_w_seq
   (proved via boolean reflection, same pattern as fact3)
4. Combine the above to get the biconditional

**Why this path was chosen:** Stanley's "easy to see" hides two distinct
claims: (a) expand_cde membership is equivalent to having transitions at
D-positions, and (b) the D-positions in the cd-word Phi_w correspond to
the S_w positions used in the omega condition. Claim (a) is indeed
straightforward by induction on the cd-word — the C/D branching in
expand_cde directly creates free/constrained bits. But claim (b) requires
a non-trivial index-mapping argument: the cumulative bit-offset of the
j-th D-letter in the cd-word must equal the S_w_seq value (which is the
original tree position minus 1). This offset-position correspondence is
a structural property of min-max trees that has no one-line proof.

We decomposed the problem into (a) and (b) to isolate the cd-word part
(purely syntactic, no tree structure needed) from the tree-structure part
(relating offsets to positions). For (b), we reused the boolean
reflection pattern from fact3: define `check_offsets w` = (D_offsets
(phi_w w) == S_w_seq w), show it is psi-invariant (since both phi_w and
S_w_seq are psi-invariant), and close by mmtree induction + computation.
This avoids a direct inductive proof on the tree structure, which would
require formalizing how endpoints pair with D-vertices — a counting
argument that is clear on paper but tedious to formalize.

### 5.3 Proposition 1.6.4: omega-Monotonicity of beta

**Stanley (p.61):** "If omega(S) subset omega(T), then beta_n(S) < beta_n(T)."

**Formal (`perm_seq_bridge.v:230-238`):**
```coq
Lemma omega_proper_beta_lt : forall m (D E : {set 'I_m.+1}),
  omega_set D \proper omega_set E ->
  beta D < beta E.
```

**Proof strategy (DIVERGES from Stanley):** Stanley's proof is two
sentences: nonneg coefficients give <=, and the witness cd-word
c^{i-1} d c^{n-2-i} gives strict <.

The formal proof requires ~580 LOC of bridge infrastructure:
1. **perm_to_seq / seq_to_perm bijection** connecting {perm 'I_n} to
   uniq sequences. This bridge doesn't exist in Stanley because he works
   informally with both representations.
2. **is_descent_perm_seq**: formal proof that descent at position i in the
   perm world equals descent at position i in the seq world.
3. **M-class injection**: for each sigma with descent D, find the unique
   member of [perm_to_seq(sigma)] with descent E. Uses `find_ss` to
   search within the class and `char_mono_class_inj` for injectivity
   within the class (from fact3 + uniq_expand_cde).
4. **Strictness**: `strict_witness_exists` provides a witness class
   contributing to beta(E) but not beta(D).
5. **Omega bridge**: `omega_set_seq_bridge_bounded` connecting the
   finset-level omega_set to the seq-level omega_seq.

**Why this path was chosen:** Stanley's two-sentence proof is
mathematically complete but operates in a single universe where
permutations, sequences, descent sets, and cd-words coexist freely.
The formalization lives in two separate type universes that cannot
see each other:

- **The perm/finset universe** (descent.v, beta.v, beta_omega.v):
  permutations are `{perm 'I_{n+1}}`, descent sets are `{set 'I_n}`,
  and beta counts permutations. This is where the theorem is *stated*.

- **The seq/cd-index universe** (psi_core.v through psi_cdindex.v):
  permutations are `seq nat`, descent patterns are `seq bool`, and the
  M-class / cd-index machinery operates. This is where the proof
  *content* lives (fact3, phi_w_support, strict_witness).

Stanley moves between these freely because mathematics doesn't
distinguish between a permutation-as-function and a permutation-as-
word. In Rocq, `{perm 'I_5}` and `[:: 3; 1; 4; 0; 2]` are
inhabitants of completely different types. The bridge file
`perm_seq_bridge.v` exists solely to cross this gap: `perm_to_seq`
and `seq_to_perm` translate between representations, and
`is_descent_perm_seq` shows the descent predicate is preserved.

The M-class injection argument is then the formal version of Stanley's
"nonneg coefficients give <=": for each perm sigma with descent D, the
cd-index of its M-class contains the E-pattern (by phi_w_support +
omega monotonicity), so there exists a class member with descent E.
This gives an injection {sigma : descent D} -> {tau : descent E}.
The injectivity relies on `char_mono_class_inj` (descent patterns are
distinct within a class, from fact3), and strictness uses
`strict_witness_exists` (a class contributing to beta(E) but not
beta(D)).

### 5.4 Corollary 1.6.5: Alternating Maximizes beta

**Stanley (p.61):** "Let S subset [n-1]. Then beta_n(S) <= E_n, with
equality iff S = {1,3,5,...} cap [n-1] or S = {2,4,6,...} cap [n-1]."

**Formal (`beta_swap.v:272-300`):**
```coq
Lemma beta_alt_max n (D : {set 'I_n}) :
  ~~ set_is_alt D -> beta D < beta (alt_desc_set n).
```

**Proof strategy (follows Stanley):** Stanley derives this immediately
from Prop 1.6.4 and equation (1.65). The formal proof follows the same
route, spelling out the omega-set argument that Stanley leaves implicit:

1. `omega_set_alt_full`: omega(alt_desc_set) = setT (the alternating
   set has the full omega set because every consecutive pair has different
   membership). This formalizes Stanley's equation (1.65).

2. `not_set_is_alt_omega_not_full`: if D is not set-alternating then
   omega(D) != setT (some consecutive pair has same membership, giving
   a missing omega bit).

3. Combine: omega(D) proper_subset omega(alt) = setT, so by
   omega_proper_beta_lt, beta(D) < beta(alt).

**Historical note:** The original formalization attempted to prove
Corollary 1.6.5 via a per-step swap chain (toggle consecutive descents
one at a time, showing each toggle strictly increases beta). This
approach was NOT from Stanley — it was an alternative proof strategy
invented during formalization. It required an intermediate lemma
`beta_swap_lt_caseB` which turned out to be **mathematically false**
(counterexample: n=3, D={0,1}, beta=3=3 after toggle). Stanley's
claims are all correct. The final formal proof follows Stanley's own
direct approach via the cd-index and omega sets.

---

## 6. The omega Map

**Stanley (p.61):** Given S subset [n-1], define omega(S) subset [n-2]
by: i in omega(S) iff exactly one of i and i+1 belongs to S.

**Formal (`beta_omega.v:57`):**
```coq
Definition omega_set (n : nat) (D : {set 'I_n.+1}) : {set 'I_n} :=
  [set k : 'I_n | (widen_ord (leqnSn n) k \in D) != (lift ord0 k \in D)].
```

At the seq level (`psi_cdindex.v:1261`):
```coq
Definition omega_seq (s : seq nat) : seq nat :=
  [seq k <- iota 0 (foldr maxn 0 s).+1
   | (k \in s) != ((k.+1) \in s)].
```

The bridge between finset and seq levels is `omega_set_seq_local_bridge`
(`beta_bridge.v:99`).

**Stanley's equation (1.65):** omega(S) = [n-2] iff S is alternating
or reverse alternating. This is formalized as `omega_set_alt_full`.

---

## 7. Summary: What's NOT in Stanley

The following formal results go beyond Stanley Chapter 1:

### 7.1 Value-Complement Bijection

**Formal (`beta_swap.v:127-175`):**
```coq
Definition compl_perm s := s * rev_perm_ord n.
Lemma beta_compl n (D : {set 'I_n}) : beta D = beta (~: D).
```
Composing with the reversal permutation sends descent set D to its
complement ~: D, preserving beta. Stanley doesn't state this explicitly.

### 7.2 Worpitzky Identity and Explicit Formula

While Worpitzky's identity appears in Stanley as Proposition 1.4.4, the
formal version proves it as a pure identity on natural numbers rather
than as a generating function identity, and derives the explicit formula
for Eulerian numbers as a corollary.

### 7.3 The Recurrence via Insert-Max Bijection

Stanley proves the recurrence A(d+1,k) = k*A(d,k) + (d-k+2)*A(d,k-1)
by a counting argument. The formal proof constructs the explicit
insert/extract bijection and proves it is a bijection (with full inverse
construction), which is more work but provides a stronger result.

### 7.4 Classification of Set-Alternating Sets

**Formal (`beta_swap.v:181-212`):**
```coq
Lemma set_is_alt_classify n (D : {set 'I_n}) :
  set_is_alt D -> D = alt_desc_set n \/ D = ~: alt_desc_set n.
```
A descent set is set-alternating iff it equals the alternating set or
its complement. This is equation (1.65) restated as a classification.

---

## 8. Architecture Summary

```
Stanley §1.4 (descents):     descent.v, eulerian.v, beta.v
Stanley §1.6.2 (flip equiv):  (not formalized)
Stanley §1.6.3 (cd-index):   psi_core.v, psi_comm.v, psi_descent_v2.v,
                               psi_descent_thms.v,
                               psi_cdindex_core.v (definitions + helpers)
                               psi_cdindex_witness.v (S_w, omega, witness)
                               psi_cdindex_support.v (phi_w_support + fact3)
Stanley §1.6.4 (omega mono):  beta_omega.v, beta_bridge.v, perm_seq_bridge.v
Stanley Cor 1.6.5 (alt max):  beta_swap.v
```

The formal proof requires ~5500 LOC across 17 files, primarily because:
1. The perm-to-seq type bridge (absent in informal math)
2. The min-max tree structure lemmas (stated without proof by Stanley)
3. The psi commutativity proofs (stated as "Fact #1" by Stanley)
4. The descent-effect proofs (stated as "Fact #2" by Stanley)
5. The cd-index expansion characterization (stated as "easy to see" by Stanley)

Of these, items 3-5 correspond to Stanley's "Facts 1-3" which he presents
without detailed proofs, noting only that they are "fairly straightforward."
The formal verification of these three facts constitutes the majority of
the formalization effort.
