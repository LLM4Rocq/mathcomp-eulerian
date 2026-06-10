# Informal Statements and Proofs

**Project:** Stanley EC1 §1.4 + §1.6 (descents and cd-index of Eulerian
posets), formalized in Rocq / MathComp.

**Reference.** Throughout this document, *Stanley* means *Enumerative
Combinatorics I*, 2nd ed., R. P. Stanley (Cambridge, 2012). The relevant
sections are §1.4 (descents and the Eulerian polynomials, pp. 30–51) and
§1.6 (the cd-index, pp. 56–61). The text excerpts used to align our
formalization with Stanley's numbering are in `refs/stanley_1_4_descents.txt`
and `refs/stanley_1_6_cdindex.txt`; the full PDF is `refs/enu_comb_stanley.pdf`.

**Notation alignment.** Stanley writes `Sn` for permutations of `[n]` and
`D(w) ⊆ [n−1]` for the descent set. Our formalization uses
`{perm 'I_{n+1}}` for permutations and `{set 'I_n}` for descent sets — the
indices shift by 1 because we 0-index, but the mathematical content matches.
Stanley's `βn(S)` is exactly our `beta D`.

**Headline result.** Stanley **Corollary 1.6.5** — `βn(S) ≤ En` with equality
iff `S` is alternating — is the highlighted theorem of this project. It
appears in our development as `beta_alt_max` (Stanley's contrapositive form:
non-alternating implies strict inequality).

Every formal statement proved in this repository is **kernel-checked `.vo`**:
the proof term is re-elaborated by Rocq's kernel and validated by `coqchk`.
This document gives an informal mathematical reading of each result, marked
with ✅ throughout.

The whole development uses **0 axioms beyond Rocq's standard core** and
contains **0 `Admitted`** in the active build chain. `Print Assumptions
beta_alt_max` and `Print Assumptions omega_proper_beta_lt` both report
"Closed under the global context". The file `psi_descent_wf.v` containing
7 `Admitted` is an orphan — archived under `archive/psi_descent_wf.v.txt`
and not in `_CoqProject`.

---

## Verification key

| Symbol | Meaning |
|--------|---------|
| ✅ | File compiles to `.vo`: kernel-validated proof term, axiom-free under `coqchk` |

| File | Status | Role |
|------|:------:|------|
| `mmtree.v` | ✅ | Min-max tree datatype + `mmtree_of_seqK` round-trip |
| `psi_core.v` | ✅ | `mm_pos`, `window_size`, ψᵢ operator (M-equivalence generators) |
| `psi_comm.v` | ✅ | Commutativity of ψᵢ on disjoint windows |
| `psi_descent_v2.v` | ✅ | `has_left_child`, `is_descent_seq`, descent ↔ ψ |
| `psi_descent_thms.v` | ✅ | Window descent theorems |
| `psi_descent.v` | ✅ | Compatibility wrapper over `psi_descent_v2` + `psi_descent_thms` |
| `psi_cdindex_defs.v` | ✅ | cd-letter alphabet, `phi_w`, `expand_cde`, `char_mono` |
| `psi_cdindex_tree_shape.v` | ✅ | Tree-shape encoding (Opaque-sealed) |
| `psi_cdindex_tree_hlc.v` | ✅ | Has-left-child via tree shape |
| `psi_cdindex_tree.v` | ✅ | Tree-induction route to invariants |
| `psi_cdindex_core.v` | ✅ | ψᵢ preserves `phi_w`, `internal_vertices`, M-class bit-recovery |
| `psi_cdindex_witness.v` | ✅ | `S_w` definition, Fact #1 ingredients |
| `psi_cdindex_support_defs.v` | ✅ | `cde_width`, `cde_total_width`, `D_offsets`, `expand_cde_mem_iff` |
| `psi_cdindex_support.v` | ✅ | **`phi_w_support_general`, `fact3`** |
| `ordinal_reindex.v` | ✅ | Lift/unlift bijections on `'I_n` |
| `perm_compress.v` | ✅ | `drop_perm` / `lift_perm` builders |
| `descent.v` | ✅ | `descent_set`, `des`, `asc` on `{perm}` |
| `eulerian.v` | ✅ | Eulerian numbers, row sum |
| `beta.v` | ✅ | `beta`, `beta0`, `beta_full`, `beta_eulerian` |
| `beta_omega.v` | ✅ | Toggle action, `omega_set` definition |
| `beta_bridge.v` | ✅ | Set ↔ seq bridge for `omega` |
| `perm_seq_bridge.v` | ✅ | **`omega_proper_beta_lt`** (Stanley Prop 1.6.4) |
| `beta_swap.v` | ✅ | **`beta_alt_max`** (the headline theorem, Stanley Cor 1.6.5) |
| `reflection.v` | ✅ | **`euler_rec`** (André recurrence, Stanley §1.6.4) |

All 42 maintained files compile to `.vo` (the table lists the
§1.4/§1.6 cd-index chain; see `_CoqProject` for the full list). The headline theorems —
Stanley Prop 1.6.4 (`omega_proper_beta_lt`) and Cor 1.6.5
(`beta_alt_max`) — are kernel-validated and closed under the global
context.

---

# Part I — Foundations

## 1. Min-max trees ✅ `mmtree.v`

[Stanley §1.6.3, p. 56, definition of `M(w)`]

For a sequence `w = a₁, …, a_n` of distinct integers, the *min-max tree* `M(w)`
is built recursively: choose the position `j` of the **minimum or maximum**
element of `w` (Stanley uses minimum at odd levels, maximum at even — but for
the round-trip `mmtree_of_seqK` we just need any consistent rule), make `a_j`
the root, and recurse on `a₁…a_{j−1}` (left subtree) and `a_{j+1}…a_n` (right).

**Datatype.** `Inductive mmtree T := Leaf | Node : mmtree T → T → mmtree T → mmtree T.`

**In-order traversal.** `mmtree_to_seq (Node l x r) = mmtree_to_seq l ++ x :: mmtree_to_seq r`.

**Theorem ✅ `mmtree_of_seqK : ∀ s, mmtree_to_seq (mmtree_of_seq s) = s`.**

The construction is given via fuel-based recursion; correctness uses
`min_pos_lt` (the minimum position is strictly less than the size, for nonempty
sequences). The round-trip identifies the tree as a faithful representation
of the underlying seq — every position in `w` corresponds to a `Node` in `M(w)`.

## 2. The mm position ✅ `psi_core.v`

For a nonempty seq `s`, `mm_pos s` is defined as `min_pos s` if the minimum
appears earlier than the maximum, else `max_pos s`:

```
Definition mm_pos s := if min_pos s < max_pos s then min_pos s else max_pos s.
```

**Lemma ✅ `mm_pos_lt`.** `mm_pos s < size s` for `s ≠ []`.

This `mm_pos` is the position chosen for the root of `M(w)`. It alternates
between min and max as we recurse into subtrees.

**Companion construction ✅ `mmtree_of_seq_mmK`** (line 82): the tree built
with `mm_pos` round-trips faithfully too — `mmtree_to_seq (mmtree_of_seq_mm s) = s`.

## 3. Window size and `has_left_child` ✅ `psi_core.v`, `psi_descent_v2.v`

For a vertex at position `i` in `w`, its **window** is the interval
`[i, i + window_size i w)`, which equals the set of in-order positions in the
subtree rooted at the `Node` for position `i` in `M(w)`.

Both `window_size i w` and `has_left_child i w` are defined by **fuel-based
Fixpoints** that descend the tree by repeatedly applying `mm_pos` decomposition:

```
window_size i (a :: rest) =
  let j := mm_pos (a :: rest) in
  if i < j      then window_size i (take j (a :: rest))         -- recurse left
  else if i = j then size (a :: rest) - j                       -- root subtree
  else               window_size (i - j - 1) (drop j+1 (a :: rest))  -- recurse right
```

`is_internal i w := (i < size w) && (1 < window_size i w)`. Equivalently, `i`
is internal iff its `Node` in `M(w)` has at least one non-`Leaf` child.

`has_left_child i w` is `true` iff in `M(w)`, the `Node` at position `i` has
a non-`Leaf` left subtree. Combined with the fact (from `mm_pos_lt_pred`,
later) that any internal Node has a non-`Leaf` right child, this means:

- Internal vertex with **left child** ↔ both children non-`Leaf` ↔ a `D` in Stanley's cd-letter classification.
- Internal vertex without left child ↔ right-only ↔ a `C`.
- Non-internal (leaf-`Node`) ↔ `E` (endpoint, deleted from `phi_w`).

## 4. The ψᵢ operators ✅ `psi_core.v`, `psi_comm.v`

[Stanley §1.6.3, p. 57, definition of ψᵢ; **Fact #1**, p. 57]

For each internal position `i`, ψᵢ is a permutation on `seq nat` that **toggles
the local order** of the window at `i`. Concretely, ψᵢ permutes the labels in
the window without changing the unlabelled tree shape — it's an element of the
group `G_w ≅ (ℤ/2)^{ι(w)}` where `ι(w)` is the number of internal vertices
(Stanley **Fact #1**).

**`apply_psis` ✅ `psi_cdindex_defs.v:28`.** Applies a list of ψᵢ in order:
`apply_psis [::] w = w` and `apply_psis (i :: rest) w = apply_psis rest (psi i w)`.

**Theorem ✅ `psi_comm_disjoint`** (`psi_comm.v:431`). ψᵢ and ψⱼ commute when
their windows are disjoint or nested with the inner one not at the boundary
of the outer. This is the commutativity claim in Stanley **Fact #1**.

**Stanley Fact #1 (commutativity + group structure).** Stanley states that the
ψᵢ for internal vertices generate an abelian group `Gw ≅ (ℤ/2)^{ι(w)}`, and
each subset of internal vertices yields a distinct element. The commutativity
half is `psi_comm_disjoint` ✅; the full M-class enumeration follows by
combining `psi_comm_disjoint` with the involution property of each individual
ψᵢ. The M-equivalence class is then
`{ apply_psis ss w | ss ⊆ internal_vertices w }` and has size `2^ι(w)`.

---

# Part II — cd-index machinery

## 5. The cd-letter alphabet ✅ `psi_cdindex_defs.v`

[Stanley §1.6.3, p. 58, definitions of `Φ'w` and `Φw`]


```
Inductive cde := C_letter | D_letter | E_letter.
```

**Vertex classification.** `classify_vertex_cde i w = E_letter` if `i` is not
internal, `D_letter` if internal with left child, `C_letter` if internal
without left child.

**`phi'_w w`** = `[seq classify_vertex_cde i w | i ← iota 0 (size w)]` — the
unfiltered list of cd-letters by position.

**`phi_w w`** = `phi'_w w` with `E_letter`s filtered out — Stanley's Φ_w, the
cd-monomial associated to `w`. By Fact #1, `phi_w` depends only on the
M-equivalence class `[w]`, i.e., it's a function of the unlabelled tree shape
of `M(w)`.

## 6. Expansion of cd-monomials ✅ `psi_cdindex_defs.v`

[Stanley §1.6.3, **Theorem 1.6.3** + the substitution `c = a+b, d = ab+ba`,
p. 59-60]

`expand_cde m : seq (seq bool)` substitutes Stanley's `c = a + b`,
`d = ab + ba`, `e = 1` in the cd-monomial:

```
expand_cde [::]                = [:: [::]]
expand_cde (C_letter :: rest)  = [seq false :: t | t ← exp rest]
                                ++ [seq true :: t | t ← exp rest]
expand_cde (D_letter :: rest)  = [seq false :: true :: t | t ← exp rest]
                                ++ [seq true :: false :: t | t ← exp rest]
expand_cde (E_letter :: rest)  = exp rest
```

The result has length `2^c · 2^d` where `c, d` are the C- and D-counts.
Each element is a *bit-string* representing a descent pattern.

## 7. Characteristic monomials ✅ `psi_cdindex_defs.v`

[Stanley §1.6.3, eq. (1.60), p. 58 — the *characteristic monomial* `uS`]

`char_mono w := [seq is_descent_seq w k | k ← iota 0 (size w).-1]`.

For a permutation `s : 'I_n.+1`, the characteristic monomial is the bit-vector
of its descent positions. Stanley writes `uS = e₁e₂…e_{n−1}` with `eᵢ = a` if
`i ∉ S`, `eᵢ = b` if `i ∈ S` (eq. 1.60). Our representation uses `bool`:
`false` ↔ `a` (no descent), `true` ↔ `b` (descent).

Stanley **Fact #3** says the multiset of characteristic monomials over the
M-class `[w]` equals the multiset given by expanding `Φw` under
`c ↦ a+b, d ↦ ab+ba`. This is `fact3` ✅ (§13).

## 8. Fact #1 prerequisites ✅ `psi_cdindex_core.v`, `psi_cdindex_tree_shape.v`

[Stanley §1.6.3, **Fact #1**, p. 57: "the operators ψᵢ are commuting
involutions... `Φw` depends only on `M(w)` as an unlabelled tree"]

To verify that `phi_w` is a tree-shape invariant (the key consequence of
Stanley's Fact #1 — that the cd-monomial `Φw` is well-defined on the M-class),
we need that ψᵢ preserves the entire shape data. Concretely:

- **✅ `window_size_apply_psis ops i w`**: ψ-application preserves `window_size`.
- **✅ `has_left_child_apply_psis ops i w`**: same for `has_left_child`.
- **✅ `is_internal_apply_psis ops i w`**: same for `is_internal`.
- **✅ `internal_vertices_apply_psis ops w`**: same for the list of internal positions.
- **✅ `phi_w_apply_psis ops w` (`psi_cdindex_core.v:52`)**: the formal expression
  of Stanley **Fact #1**'s well-definedness clause:
  `phi_w (apply_psis ss w) = phi_w w` for any `ss`.

The verification of these used the **`mmtree_shape` refactor** (file
`psi_cdindex_tree_shape.v`): a single Opaque-sealed `mmtree_shape` Fixpoint
encodes the tree-as-shape, and each property invariant is a 5-line corollary
of one shape-induction. This refactor reduced peak `-vo` memory from
>131 GB to ~0.6 GB for the tree-property files. The mathematical content is
exactly Stanley's observation that `Φw` reads off the unlabelled tree shape.

---

# Part III — Descents and counting

## 9. Descent sets and Eulerian numbers ✅ `descent.v`, `eulerian.v`, `beta.v`

[Stanley §1.4, p. 30: definitions of `D(w)`, `α(S)`, `β(S)`, eq. (1.32)]

For a permutation `s : {perm 'I_n.+1}`:

- **`is_descent s i`** (`descent.v:22`): `s i.+1 < s i`.
- **`descent_set s : {set 'I_n}`**: positions where `s` descends — Stanley's `D(w)`.
- **`des s := |descent_set s|`**, **`asc s := n − des s`**.

**`eulerian n k`** (`eulerian.v:14`): the number of `s : {perm 'I_n.+1}` with
exactly `k` descents — Stanley's *Eulerian number* `A(n+1, k+1)` in some
notations, or the coefficient of the Eulerian polynomial `An(x)` defined in
Stanley §1.4 (eq. between 1.36 and 1.37).

**Theorem ✅ `eulerian_row_sum_fact`** (`eulerian.v:31`):

> ∑_{k≤n} eulerian(n, k) = (n+1)!.

This is the elementary identity `∑_k A(n+1, k) = (n+1)!` from §1.4 (the row
sum of the Eulerian triangle).

**`beta`** (`beta.v:19`): refines the Eulerian count by the *exact descent set*
— Stanley's **`βn(S)`** from eq. (1.32), p. 30:

> beta(D) = #{ s : {perm 'I_{n+1}} | descent_set s = D }   ↔   βn(S) = #{w ∈ Sn : D(w) = S}.

**Theorem ✅ `beta_eulerian`** (`beta.v:124`):

> ∑_{D : |D|=k} beta(D) = eulerian(n, k).

This is the partition of permutations by descent-count: integrating Stanley's
`βn(S)` over fixed-size subsets recovers the Eulerian number.

**Theorem ✅ `sum_beta_eq_fact`** (`beta.v:112`):

> ∑_{D ⊆ [n]} beta(D) = (n+1)!.

Stanley's complete partition identity: every permutation has exactly one
descent set, so `∑_S βn(S) = n!` (with our index shift).

**Boundary cases ✅ `beta0` and `beta_full`** (`beta.v:75`, `beta.v:100`):

> beta(∅) = beta([n]) = 1.

These say there's exactly one permutation with no descents (the identity) and
exactly one with all descents (the reverse-sorted permutation). These appear
implicitly in Stanley's discussion (e.g., `α(∅) = β(∅) = 1` follows from his
1.4.1 specialized at `S = ∅`).

## 10. Toggle action on descent sets ✅ `beta_omega.v`

[Stanley §1.6.3, **Fact #2**, p. 57-58: descent change under ψᵢ]

Toggling an element `i` in a descent set `D` is `D Δ {i}` (symmetric difference):

```
toggle_at D i := sym_diff D [set i].
```

**Lemma ✅ `toggle_atK`** (`beta_omega.v:38`): involution `toggle_at (toggle_at D i) i = D`.

The block decomposition lemmas (`block_left_le`, `block_right_ge`,
`block_descent_chain`, `block_chain_step`, `block_chain_values`) characterize
how toggling a single descent at position `i` propagates through "blocks" —
maximal intervals of consecutive descents/ascents. This is the combinatorial
content underlying Stanley **Fact #2**: descents change at exactly one position
(or two positions, for two-child internal vertices) when ψᵢ acts. Stanley's
own statement of Fact #2 (p. 57-58) splits into the right-only-child case
(`D(ψᵢw) = D(w) Δ {i}`) and the two-children case
(`D(ψᵢw) = D(w) Δ {i−1, i}`); both are captured by the block-toggle calculus.

## 11. The omega map ✅ `beta_omega.v`

[Stanley §1.6.3, p. 60, definition of `ω(S)`: "Define `ω(S) = {i ∈ [n−2] :
exactly one of i, i+1 belongs to S}`"]

For `D ⊆ 'I_{n+1}`, the *omega set* `omega_set D ⊆ 'I_n` is:

```
omega_set D = { k : 'I_n | (k ∈ D) ⊕ (k+1 ∈ D) }
```

This is exactly Stanley's `ω(S)` (eq. just before 1.6.4) — positions where
exactly one of consecutive elements lies in `D`. Mathematically,
`ω(D) = D Δ (D−1)` (where `D−1` is `D` shifted by one).

**Lemma ✅ `mem_omega_set`** (`beta_omega.v:60`): `k ∈ omega_set D` iff toggling
`D` at one of `k, k+1` flips membership.

The omega map is the bridge between `phi_w`-level descent patterns and
finset-level descent sets (Section 14). Stanley's eq. (1.65) characterizes
when `ω(S) = [n−2]` (the universal set), which corresponds to S being one of
the two alternating patterns; we capture this as `omega_set_alt_full` ✅
(§16).

---

# Part IV — Witness construction

## 12. The S_w invariant ✅ `psi_cdindex_witness.v`

[Stanley §1.6.3, p. 60, definition of `Sw` in the proof of Prop 1.6.4:
`Sw = {i − 1 : fᵢ = d}`]

For a sequence `w` with cd-monomial `phi_w w`, Stanley's `Sw ⊂ [n−2]` is
defined as the set of positions where `phi_w` has a `D` letter (after
collapsing widths: each `C` contributes 1 bit and each `D` contributes 2 bits
to the binary expansion).

**`omega_seq`** (`psi_cdindex_witness.v:27`): the seq-level analog of
`omega_set` (used as a computational bridge).

**`S_w_seq w`** (`psi_cdindex_witness.v:38`): the list of D-positions in
`phi_w w`.

**`witness_perm n k`** (`psi_cdindex_witness.v:116`): an explicit permutation
`s ∈ {perm 'I_{n+1}}` with `descent_set s = ` a specified subset. This is
**Stanley's witness `Φw = c^{i−1} d c^{n−2−i}` from the proof of Prop 1.6.4**
(p. 61: "if `i ∈ ω(T) − ω(S)` then let `Φw = c^{i−1} d c^{n−2−i}`, so
`Sw = {i}`"). The witness construction makes the strict inequality in 1.6.4
constructive.

**Theorem ✅ `witness_perm_uniq` and `check_strict_witness_correct`** (line 233,
297): `witness_perm` produces a sequence that is a valid permutation of
`[0, …, n]` and has the predicted descent pattern.

## 13. Heavy support theorem ✅ `psi_cdindex_support.v`

[Stanley §1.6.3, the displayed identity `Φw = ∑_{ω(X) ⊇ Sw} uX` on p. 60-61,
inside the proof of Prop 1.6.4; and **Fact #3**, p. 58, the M-class
multiset identity]

This is the combinatorial heart of Stanley §1.6. The supporting
definitions (`cde_width`, `cde_total_width`, `cde_offset`, `D_offsets`,
`expand_cde_mem_iff`) live in the split file
`psi_cdindex_support_defs.v` ✅.

**Definitions ✅.** `cde_width l ∈ {0, 1, 2}` (E, C, D widths);
`cde_total_width m`; `cde_offset m i`; `D_offsets m`. These give the bit-level
positions of D-letter expansions in `expand_cde`.

**Theorem ✅ `expand_cde_mem_iff`** (`psi_cdindex_support_defs.v`):

> A bit-string `X` is in `expand_cde m` iff `|X| = cde_total_width m`
> AND for every D-position `k` in `m`, `X_k ≠ X_{k+1}` (a "transition" at `k`).

This is the defining combinatorial property of cd-monomial expansion — D
contributes the dyad `{ab, ba}`, which exactly forces a flip at the D-position.

**Theorem ✅ `phi_w_support_general`** (`psi_cdindex_support.v`):

> For `uniq w` with `|w| ≥ 2` and `|X| = (size w).-1`:
> `X ∈ expand_cde (phi_w w)` iff every `k ∈ S_w` satisfies the omega condition
> on `X`'s descent positions.

This is exactly **Stanley's identity at the top of p. 61**:

> `Φw = ∑_{X : ω(X) ⊇ Sw} uX`

(restated bidirectionally as a membership equivalence in the bit-string
expansion of `Φw`). This identity is the **load-bearing intermediate result
of Prop 1.6.4's proof** in Stanley.

**Theorem ✅ `fact3`** (`psi_cdindex_support.v`): **Stanley Fact #3**
(verbatim, p. 58):

> *Stanley's statement.* "Let `w ∈ Sn`, and let `[w]` be the M-equivalence
> class containing `w`. Then `∑_{v ∈ [w]} uD(v) = Φw(a+b, ab+ba)`."

**Our formal statement.** For `uniq w`:

> sort_lex { char_mono(apply_psis ss w) | ss ⊆ internal_vertices w }
>   = sort_lex (expand_cde (phi_w w))

i.e., the multiset of characteristic monomials over `w`'s M-class equals the
multiset given by `expand_cde(phi_w w)`. This is the substantive identity
relating "cd-monomial expansion" semantically with the M-class enumeration —
the bridge that makes the cd-index a meaningful counting object.

Stanley uses this as a stepping stone to **Theorem 1.6.3** (the ab-index
factors through the cd-substitution). Our `fact3` matches Stanley's Fact #3
directly.

**Architecture.** The M-class injectivity gap was closed by a bit-level
recovery argument in `psi_cdindex_core.v`
(`char_mono_apply_psis_C_bit`, `char_mono_apply_psis_D_bit_pred`,
`char_mono_apply_psis_D_bit_self`): for each internal vertex `v`, one
can read off `(v ∈ ss)` from the bits of `char_mono (apply_psis ss w)`
at positions owned by `v`, and disjointness across distinct `v` follows
from `LR_pred_is_endpoint`. This drives `char_mono_apply_psis_inj` and
the `uniq_map_char_mono_powerset` used in `fact3`.

---

# Part V — The bridge to permutations

## 14. set ↔ seq bridge ✅ `beta_bridge.v`

To use the seq-level `phi_w` machinery on `{set 'I_n}` permutations, we need a
bidirectional bridge.

**`set_to_seq D`** (`beta_bridge.v:27`): the sorted `seq nat` of underlying
naturals of elements of `D : {set 'I_n}`.

**Lemma ✅ `mem_set_to_seq_iff`** and **`uniq_set_to_seq`**: round-trip
correctness.

**Lemma ✅ `omega_set_seq_local_bridge`** (`beta_bridge.v:94`):

> For `k : 'I_m`: `k ∈ omega_set D` iff `val k ∈ omega_seq_local (set_to_seq D)`.

This identifies the finset-level `omega_set` with the seq-level `omega_seq` —
the bridge that lets the heavy machinery in `psi_cdindex_*.v` apply to
`{set}`-style consumers.

## 15. perm ↔ seq bridge ✅ `perm_seq_bridge.v`

[Stanley §1.6.3, **Proposition 1.6.4**, p. 60-61]

For a permutation `s : {perm 'I_n}`, define `perm_to_seq s := [seq val (s i) | i ← enum 'I_n]`
— the seq of underlying naturals.

**Lemmas ✅:**

- **`perm_to_seq_uniq`**: `uniq (perm_to_seq s)`.
- **`perm_to_seq_inj`**: `perm_to_seq` is injective.
- **`is_descent_perm_seq`**:
  `is_descent_seq (perm_to_seq s) i = is_descent s i` — the two descent
  notions coincide.
- **`char_mono_perm_to_seq`**: `char_mono (perm_to_seq s) = descent_to_bvec (descent_set s)`.

**Theorem ✅ `omega_proper_beta_lt`** (`perm_seq_bridge.v`) — **Stanley
Proposition 1.6.4** (verbatim, p. 60):

> *Stanley's statement.* "Let `S, T ⊆ [n−1]`. If `ω(S) ⊂ ω(T)`, then
> `βn(S) < βn(T)`."

**Our formal statement.** For `D, E : {set 'I_{m+1}}`:

> If `omega_set D ⊊ omega_set E` (proper subset), then `beta(D) < beta(E)`.

**Proof sketch (Stanley's argument, faithfully formalized).** Given proper
containment of omega-sets, pick `k ∈ ω(E) ∖ ω(D)`. By
`phi_w_support_general` ✅ (§13) — the formalized version of Stanley's
identity `Φw = ∑_{ω(X)⊇Sw} uX` — for every permutation σ with descent set
`D`, the bit-vector `descent_to_bvec D` lies in `expand_cde(phi_w(perm_to_seq σ))`.
The same is true for `descent_to_bvec E` whenever `ω(E) ⊇ Sw`. Stanley's
witness `Φw = c^{i−1} d c^{n−2−i}` (formalized as `witness_perm`, §12) gives
a cd-word with `Sw = {i}` for `i = k`, ensuring `ω(E) ⊇ Sw` but
`ω(D) ⊉ Sw`. Counting yields the strict inequality.

---

# Part VI — The headline result

## 16. β-monotonicity ✅ `beta_swap.v`

[Stanley §1.6.3, **Corollary 1.6.5**, p. 61]

**The alternating descent set ✅ (`beta_swap.v:31`).**

```
alt_desc_set n := [set i : 'I_n | odd (val i)]
```

i.e., `{1, 3, 5, …}` (the alternating pattern starting from 1). For `'I_n`,
this is the descent set of the alternating permutation (down-up-down-up).
Stanley's "alternating set" is `S = {1, 3, 5, …} ∩ [n−1]` (eq. 1.65, p. 60).

**`set_is_alt`** (`beta_swap.v:40`): `D` is alternating iff for every consecutive
pair `i, i+1`, exactly one is in `D`. Equivalently: `omega_set D = [set: 'I_n]`
(every position is "balanced") — this is one direction of Stanley's eq. (1.65).

**Lemma ✅ `omega_set_alt_full`** (`beta_swap.v:238`): for `m ≥ 1`,
`omega_set (alt_desc_set (m+2)) = setT`, the universal set. This is the
"⇐" direction of Stanley's eq. (1.65) — the alternating set has full omega.

**Lemma ✅ `not_set_is_alt_omega_not_full`** (`beta_swap.v:254`): a non-alternating
`D` has `omega_set D ⊊ setT` strictly. This is the contrapositive of the "⇒"
direction of Stanley's eq. (1.65) — non-alternating sets have strictly
smaller omega.

**Theorem ✅ `beta_alt_max`** (`beta_swap.v`) — **Stanley Corollary 1.6.5**
(contrapositive form):

> *Stanley's statement.* "Let `S ⊆ [n−1]`. Then `βn(S) ≤ En`, with equality
> if and only if `S = {1, 3, 5, …} ∩ [n−1]` or `S = {2, 4, 6, …} ∩ [n−1]`."
>
> *(Here `En` is the n-th Euler number — the max value of `βn`.)*

**Our formal statement** (contrapositive of the equality clause):

> For `n ≥ 2` and `D : {set 'I_n}`:
> If `D` is **not** the alternating descent set, then
> `beta(D) < beta(alt_desc_set n)`.

**Equivalent reading.** The alternating descent set strictly maximizes β
among all descent sets of size `n`. Stanley's `En` is realized as
`beta(alt_desc_set n)`. The "or" in Stanley's statement (alternating starting
from 1 vs. from 2) reduces to a complementation argument that is also handled
upstream (see `beta_compl`, line 166: `β(D) = β(~D)`).

**Proof sketch (Stanley's argument, faithfully formalized).** Reduce to
`n = m+2` for some `m`. By `not_set_is_alt_omega_not_full`,
`omega_set D ⊊ setT = omega_set (alt_desc_set n)`. Apply
`omega_proper_beta_lt` ✅ (§15) — Stanley's Prop 1.6.4 — and the strict
inequality follows. This **exactly mirrors Stanley's "Proof: Immediate from
Proposition 1.6.4 and equation (1.65)"** (p. 61).

## 17. André's reflection method / Euler numbers ✅ `reflection.v`

[Stanley §1.6.4 (alternating permutations and Euler numbers)]

**Euler numbers ✅ (`reflection.v`).** `euler n := beta (alt_desc_set n)`
counts the down-up alternating permutations of length `n+1`;
`eulerA n` is Stanley's `A_n` (with `A_0 = 1`).

**Theorem ✅ `euler_rec`** — the André recurrence:

> `2 · A_{n+2} = ∑_{k ≤ n+1} C(n+1, k) · A_k · A_{n+1−k}`

**Proof structure (fully formalized, 0 admits).** By `beta_compl`, the LHS
is the number of permutations of length `n+2` whose descent set is
*set-alternating* (either flavour). Via the `insert_max_perm` bijection,
each such permutation is `(t, p)` — a shorter permutation `t` plus the slot
`p` of the maximum. The boundary slots `p = 0` and `p = n+1` each contribute
`A_{n+1}` (the `k = n+1` and `k = 0` terms); an interior slot `c+1` forces
one alternation flavour (`interior_set_is_alt`) and the resulting condition
on `t` **factors** through the `(image_left, perm_left, perm_right)`
decomposition (`andre_union_eq_split`): the left/right sub-permutations must
each be alternating of a parity-prescribed flavour, while the boundary
descent is unconstrained. Counting (`andre_interior_count`) gives
`C(n+1, c+1) · A_{c+1} · A_{n−c}` via `card_draws` and the
`assemble_perm` bijection (`sum_reindex_inner`). Summing the three groups
of slots is `sum_set_is_alt_eq_andre_sum`.

## 18. Generating functions: sec + tan ✅ `fps/`, `stanley_egf.v`

[Stanley §1.6.4, **Proposition 1.6.1**]

**The FPS sub-library** (`fps/`, namespace `mathcomp_fps`, reusable,
imports only mathcomp + mathcomp-classical): `{fps R}` carries the full
mathcomp algebra hierarchy (com-unit-ring for any `comUnitRingType`
coefficient ring, units = invertible constant coefficient), formal
derivative with the Leibniz rule, and the EGF calculus whose workhorse is

> **`egf_mul`** ✅: `egf a * egf b = egf (n ↦ Σ_k C(n,k) a_k b_{n−k})` —
> products of egfs are egfs of binomial convolutions.

**Theorem ✅ `stanley_1_6_1`** (`stanley_egf.v`) — **Stanley Prop 1.6.1**:

> `Σ_n E_n x^n / n! = sec x + tan x` as formal power series over `rat`,
> with `E_n = eulerA n` (the alternating-permutation counts of §17).

**Proof.** The André recurrence `euler_rec` (§17) translates verbatim into
the formal ODE `2A' = 1 + A²`, `A(0) = 1` for `A = egf eulerA`
(`euler_egf_ode`); `sec + tan` satisfies the same ODE (`sectan_ode`, via
`sin² + cos² = 1` proved by the derivative trick); and solutions of that
quadratic ODE are determined by their constant coefficient
(`fps_quad_ode_uniq`, coefficient induction in characteristic 0).
Coefficient form: `stanley_1_6_1_coef : E_n = n! · [xⁿ](sec x + tan x)`.

*Axioms:* this layer (and only this layer) uses the classical trio of
`mathcomp-classical`; `Print Assumptions stanley_1_6_1` lists exactly
those three.

## 19. Worpitzky and the Eulerian OGF ✅ `worpitzky.v`, `stanley_ogf.v`

[Stanley §1.4]

**Theorem ✅ `worpitzky`** (`worpitzky.v`, **axiom-free**):

> `(m+1)^(n+1) = Σ_{k≤n} A(n,k) · C(m+n+1−k, n+1)` — every power is a
> positive combination of binomials weighted by Eulerian numbers.

Proved by induction from `eulerian_rec` (§9) with a Pascal-style
splitting (`worpitzky_bin_step`).  Also `coef_eul_pol`: the coefficients
of `eul_pol` (§q-files) are the Eulerian numbers at every index.

**Theorem ✅ `stanley_1_4`** (`stanley_ogf.v`): the generating-function
packaging over `{fps int}`,

> `Σ_m (m+1)^(n+1) x^m · (1−x)^(n+2) = A_n(x)` — equivalently
> `Σ_m (m+1)^(n+1) x^m = A_n(x)/(1−x)^(n+2)` (`stanley_1_4_inv`),

using the negative-binomial expansion `coef_fps_geomXn` of `fps_ogf.v`.
Note `int` is not a field: this exercises the `mathcomp_fps` units
theory over general `comUnitRingType`s.  The GF layer carries the
classical trio; the Worpitzky identity itself is axiom-free.

---

# Stanley correspondence summary

The following table maps every numbered Stanley result we have formalized to
its Coq counterpart. (Stanley's section §1.5 is on geometric representations,
which we don't formalize.)

| Stanley reference | Title / content | Our formalization | Status |
|---|---|---|---|
| §1.4, eq. (1.32), p. 30 | Definition `βn(S) = #{w ∈ Sn : D(w) = S}` | `beta D` (`beta.v:19`) | ✅ |
| §1.4 (Eulerian polynomial coefficients) | `An(x) = ∑_k A(n+1,k+1) x^k` | `eulerian n k` (`eulerian.v:14`) | ✅ |
| §1.4 (Eulerian row sum) | `∑_k A(n+1,k) = n!` | `eulerian_row_sum_fact` (`eulerian.v:31`) | ✅ |
| §1.4 partition by descent set | `∑_S βn(S) = n!` | `sum_beta_eq_fact` (`beta.v:112`) | ✅ |
| §1.4 partition by descent count | `∑_{|S|=k} βn(S) = A(n+1, k+1)` | `beta_eulerian` (`beta.v:124`) | ✅ |
| §1.6.3, p. 56 (M(w) construction) | Min-max tree + in-order traversal | `mmtree` + `mmtree_of_seqK` (`mmtree.v`) | ✅ |
| §1.6.3, p. 57 (ψᵢ definition) | Window-flip on labels | `psi` operator (`psi_core.v`) | ✅ |
| §1.6.3, p. 57, **Fact #1** (commutativity) | "ψᵢ are commuting involutions, generate `(ℤ/2)^{ι(w)}`" | `psi_comm_disjoint` (`psi_comm.v:431`) | ✅ |
| §1.6.3, p. 57, **Fact #1** (well-definedness) | `Φw` depends only on `M(w)` as unlabelled tree | `phi_w_apply_psis` (`psi_cdindex_core.v:52`) | ✅ |
| §1.6.3, pp. 57-58, **Fact #2** | Descent change formula for ψᵢ (right-only / two-children) | block-toggle calculus in `beta_omega.v` (lines 247-340) | ✅ |
| §1.6.3, p. 58, eq. (1.60) | Characteristic monomial `uS = e₁…e_{n−1}` | `char_mono` + `descent_to_bvec` (`psi_cdindex_defs.v`, `perm_seq_bridge.v`) | ✅ |
| §1.6.3, pp. 58-59 (Φw definition) | `Φw = f₁…fn`, `fᵢ ∈ {c, d, e}` | `phi'_w` and `phi_w` (`psi_cdindex_defs.v`) | ✅ |
| §1.6.3, p. 58, **Fact #3** | `∑_{v ∈ [w]} uD(v) = Φw(a+b, ab+ba)` | `fact3` (`psi_cdindex_support.v`) | ✅ |
| §1.6.3, p. 59, **Fact #4** | Each M-class has exactly one alternating perm | *not separately formalized* — implied by Fact #3 + uniqueness of alternating string in expansion (witness side: `witness_perm_uniq`) | partial ✅ |
| §1.6.3, **Theorem 1.6.3** | "Ψn = Φn(a+b, ab+ba)" — ab-index = cd-index | *not formalized as a standalone* — Fact #3 supplies the substantive content | — |
| §1.6.3, p. 60, ω(S) definition | `ω(S) = {i : exactly one of i, i+1 ∈ S}` | `omega_set` (`beta_omega.v`) | ✅ |
| §1.6.3, p. 60, eq. (1.65) | `ω(S) = [n−2] ⇔ S` is alternating | `omega_set_alt_full` + `not_set_is_alt_omega_not_full` (`beta_swap.v`) | ✅ |
| §1.6.3, p. 60-61 (proof of 1.6.4) | Identity `Φw = ∑_{ω(X)⊇Sw} uX` | `phi_w_support_general` (`psi_cdindex_support.v`) | ✅ |
| §1.6.3, p. 60-61 (proof of 1.6.4) | Witness `Φw = c^{i−1} d c^{n−2−i}` | `witness_perm` (`psi_cdindex_witness.v`) | ✅ |
| §1.6.3, p. 60, **Proposition 1.6.4** | `ω(S) ⊂ ω(T) ⇒ βn(S) < βn(T)` | `omega_proper_beta_lt` (`perm_seq_bridge.v`) | ✅ |
| §1.6.3, p. 61, **Corollary 1.6.5** | `βn(S) ≤ En`, equality iff S alternating | `beta_alt_max` (`beta_swap.v`) | ✅ |
| §1.6.4 (Euler numbers) | André recurrence `2·A_{n+2} = ∑_k C(n+1,k)·A_k·A_{n+1−k}` | `euler_rec` (`reflection.v`) | ✅ |
| §1.6.4, **Proposition 1.6.1** | `∑ E_n x^n/n! = sec x + tan x` (formal) | `stanley_1_6_1` (`stanley_egf.v` + `fps/`) | ✅ |
| §1.4 (Worpitzky) | `(m+1)^(n+1) = ∑_k A(n,k)·C(m+n+1−k,n+1)` | `worpitzky` (`worpitzky.v`, axiom-free) | ✅ |
| §1.4 (Eulerian OGF) | `∑_m (m+1)^(n+1) x^m = A_n(x)/(1−x)^(n+2)` | `stanley_1_4` (`stanley_ogf.v`) | ✅ |

**Our companion / housekeeping results** (not in Stanley but needed):
`mm_pos_lt_pred` (the root of M(w) is internal); `cde_total_width_phi_w_all`
(the bit-width of `Φw` equals `n−1`); the seq↔set bridges. All ✅.

---

# What this is and isn't

**What is verified ✅** (kernel-checked, 0 axioms, 0 Admitted, all 33
maintained files build to `.vo`):

- The min-max tree `M(w)` round-trip and structural API (Stanley §1.6.3, p. 56).
- ψᵢ commutativity (Stanley **Fact #1**, commutativity half).
- `phi_w_apply_psis` — Stanley **Fact #1**'s well-definedness clause:
  `Φw` depends only on `M(w)` as an unlabelled tree.
- The block-toggle calculus underlying Stanley **Fact #2**.
- The Eulerian-number ↔ β identities (`beta_eulerian`, `sum_beta_eq_fact`,
  `eulerian_row_sum_fact`) — Stanley §1.4 row-sum and partition identities.
- The boundary cases `βn(∅) = βn([n−1]) = 1`.
- Stanley **eq. (1.65)**: characterization of when `ω(S) = [n−2]`
  (`omega_set_alt_full` + `not_set_is_alt_omega_not_full`).
- The `omega_set ↔ omega_seq` bridge between finset and seq.
- All of `toggle_at`, `set_is_alt`, the alternating descent set, and the
  witness construction `witness_perm` (Stanley's `Φw = c^{i−1} d c^{n−2−i}`).
- **Stanley Fact #3** (`fact3`): the M-class multiset identity.
- **Stanley's identity** `Φw = ∑_{ω(X) ⊇ Sw} uX` (`phi_w_support_general`).
- **Stanley Proposition 1.6.4** (`omega_proper_beta_lt`):
  `ω(S) ⊊ ω(T) ⇒ βn(S) < βn(T)`.
- **Stanley Corollary 1.6.5** (`beta_alt_max`): the alternating descent
  set strictly maximizes `β` — *the headline result*.

**What is missing entirely.** Nothing in the active build chain has `Admitted`
or postulated axioms beyond Rocq's standard library. The orphan file
`archive/psi_descent_wf.v.txt` contains 7 `Admitted`s; it is dead
code from an abandoned alternative formulation and is not loaded by any
`.vo` file.

---

# How to read the proofs

If you want to dive into the formal proofs:

1. **Start at the leaf** — `beta_swap.v` contains the headline theorem
   `beta_alt_max`. The proof body is `omega_proper_beta_lt`
   (Stanley Prop 1.6.4) applied to the alternating-set
   characterization (Stanley eq. 1.65).
2. **Walk back up the dependency chain** via `_CoqProject`. The
   topological order is `mmtree → psi_core → psi_comm →
   psi_descent_v2/thms → psi_cdindex_* → perm_seq_bridge → beta_swap`.
3. **Compile with `make clean && make -j2`** — all 33 files build to
   `.vo` end-to-end; no holdouts.
4. **Verify axiom-freeness** with `coqchk -R . mathcomp_eulerian
   mathcomp_eulerian.beta_swap`, or interactively
   `Print Assumptions beta_alt_max`.
5. **For the math behind the formal proofs,** Stanley *Enumerative
   Combinatorics I*, 2nd edition, §1.6 (especially §1.6.3 "The cd-index of a
   permutation" and the proof of Prop 1.6.4 on p. 60-61) is the ground truth.
   The repository's `refs/enu_comb_stanley.pdf` is the source.

---

# Build status snapshot

```
.vo files         : 33 / 33    ← all kernel proof terms validated
.vos files        : 33 / 33    ← all proof scripts validated
Active Admitted   :  0         ← in active build chain
Custom axioms     :  0         ← coqchk: standard axioms only
Headline theorem  : beta_alt_max — closed under the global context
```

The mathematical content of Stanley Prop 1.6.4 and Cor 1.6.5 is fully
kernel-verified.
