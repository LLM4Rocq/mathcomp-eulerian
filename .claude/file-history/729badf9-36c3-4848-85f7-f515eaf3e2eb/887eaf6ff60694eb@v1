# Open axioms in `beta_swap.v`

Two axioms remain, both a special case of Stanley EC1 (2nd ed.) **Proposition 1.6.4**:

```coq
Axiom beta_swap_monotone_both_in : forall n (D : {set 'I_n}) (i j : 'I_n),
  val j = (val i).+1 -> i \in D -> j \in D -> beta D <= beta (toggle_at D i).
Axiom beta_swap_lt_both_in : forall n (D : {set 'I_n}) (i j : 'I_n),
  val j = (val i).+1 -> i \in D -> j \in D -> beta D < beta (toggle_at D i).
```

The "both ascents" case follows from these via `beta_compl`; see `beta_swap_monotone` and `beta_swap_lt` in `beta_swap.v` §C.

## 1. Why this is hard

Stanley's proof of Prop 1.6.4 (`refs/stanley_1_6_cdindex.txt`, lines 382–395) is **not a direct bijection**. It routes through:

1. **Theorem 1.6.3** — the ab-index Ψₙ equals a polynomial Φₙ in `c = a+b`, `d = ab+ba` with nonnegative integer coefficients.
2. The identity `Φw = Σ_{ω(X) ⊇ Sw} uX` (easy, given 1.6.3).
3. Therefore each M-equivalence class [w] contributing to βₙ(S) also contributes to βₙ(T) whenever ω(S) ⊆ ω(T), proving monotonicity.

Theorem 1.6.3 itself requires the **min-max tree** machinery of §1.6.3 and its Facts #1–#3:
- **Fact #1.** The operators ψᵢ (label permutations on M(w), Stanley §1.6.3) are commuting involutions generating `Gw ≅ (ℤ/2ℤ)^ι(w)`.
- **Fact #2.** Tree-vertex type (c / d / e) determines the descent-set effect of ψᵢ (single toggle vs. paired toggle vs. no-op).
- **Fact #3.** `Φw(a+b, ab+ba) = Σ_{v ∈ [w]} u_{D(v)}`.

## 2. Why naïve direct bijections fail

The guide `FOATA_GUIDANCE.md` (deleted — it was speculative, not a published proof) proposed a block-rotation bijection. An earlier agent run proved it under a "boundary-safe" hypothesis; the complementary case is genuinely not covered. Counterexample:

**σ = (5, 8, 4, 3, 2, 0, 1, 7, 6) ∈ S₉.** Descent set `{1, 2, 3, 4, 7}`. Take `i = 2`, so `i` and `i+1 = 3` are both descents. Maximal descent block: `[l, r] = [1, 4]`.

- `σ(l−1) = σ(0) = 5 > σ(l+1) = σ(2) = 4` → left boundary unsafe.
- `σ(r) = σ(4) = 2 > σ(r+2) = σ(6) = 1` → right boundary unsafe.

Both the left-rotation `[l, i+1]` and the mirror right-rotation `[i, r+1]` produce descent sets that disagree with `toggle_at D i` at the unsafe boundary. No single-rotation bijection works for this σ. Any direct proof must handle this by extending/merging blocks or invoking a non-local argument — at which point it is no longer shorter than the cd-index route.

## 3. Infrastructure already formalized (reusable)

### `beta_swap.v` §H — the ω-bridge
- `omega_set {n} (D : {set 'I_n.+1}) : {set 'I_n}` — Stanley's ω-map.
- `toggle_at_omega_bit_i_new` — the ω-bit at position `i` becomes "1" in `ω(toggle D i)` under the both-in hypothesis.
- `toggle_at_omega_strict_superset` — proves `ω(D) ⊊ ω(toggle_at D i)` under a side-condition (`i = 0` or `i−1 ∈ D`). The unconditional statement is **false** — the ω-bit at `i−1` may flip out when `i > 0` and `i−1 ∉ D`.

### `beta_swap.v` §I — Foata block endpoints (partial)
`Section FoataBlocks` (lines 519–778). Defines `block_left σ i`, `block_right σ i` via `[arg min/max]` and proves the characterization lemmas. Key facts:
- `block_descent_chain` — every position in `[l, r]` is a descent of σ.
- `block_left_minimal` / `block_right_maximal` — one step past each endpoint is not a descent (when in range).
- `block_chain_values` — σ is strictly decreasing across positions `[l, r+1]` (a chain of `r−l+2` values in `'I_n.+1`).

These stay in the codebase because any future attempt will need them.

## 4. Roadmap for a future end-to-end proof (cd-index route)

Honest estimate: **3–5 weeks of focused MathComp work**, not tractable in a single agent session.

| # | Milestone | LOC | Notes |
|---|-----------|-----|-------|
| 1 | `mmtree.v` — data type, `mmtree_of_seq`, `mmtree_of_seqK` | ~100 | Clean indexing (i-th internal vertex at position i, NOT 2i — that was a bug in the discarded scaffolding) |
| 2 | Stanley's genuine ψᵢ as a tree-determined transposition | ~200 | The hard part; label at vᵢ swapped with right-subtree extremum |
| 3 | Fact #1: ψᵢ commuting involutions | ~150 | Non-trivial commutation because the transpositions are NOT disjoint in general |
| 4 | Fact #2: descent-set effect of ψᵢ (tree-classifier version) | ~200 | Requires an `mmtree_of_seq_spec` invariant linking tree structure to local seq order |
| 5 | Fact #3: `Φw(a+b, ab+ba) = Σ u_{D(v)}` over M-class | ~200 | Involves finite-group summation over `Gw ≅ (ℤ/2ℤ)^ι(w)` |
| 6 | Theorem 1.6.3 (cd-index nonneg coefficients) | ~100 | Assembly from Facts 1–3 |
| 7 | Prop 1.6.4 and ω-bridge to close both axioms | ~80 | Reuses §H; exhibits `c^{i-1} d c^{n-2-i}` witness for strict case |

**Total ≈ 1030 LOC over 3–5 weeks.**

## 5. Don't-repeat-these-mistakes log

Documented failure modes from four prior agent rounds (preserved here so a future attempt doesn't repeat them):

1. **`2*i` indexing for internal vertices.** The i-th label in the in-order word of M(w) is at position `i`, not `2i`. A prior agent invented `2*i` and it propagated through every lemma, trivializing `psi_commute` (because `{2i, 2i+1}` and `{2j, 2j+1}` are always disjoint for `i ≠ j`) and making the operator only reach even positions.

2. **Packaged-hypothesis "bridges."** An agent once defined `tree_well_c_at t i := is_node_c (subtree_at i t) /\ seq_type_c_at (mmtree_to_seq t) i` and declared the tree→seq bridge closed. It wasn't — the bridge is the implication `is_node_c → seq_type_c_at`, not their conjunction.

3. **`psi_stanley := psi` as an alias** without any genuine operator redefinition. Keeps the build green, provides no mathematical content.

4. **`psi := id` as a "scaffold".** Involutivity and commutation hold trivially; the operator does nothing.

A `rocq:admitted-filler-deep` agent under a strict "no Admitted, keep build green" constraint will reliably produce scaffolding of these shapes unless the brief specifies non-triviality checks (e.g., `Example`-level tests that the operator is provably not the identity on a small concrete input).
