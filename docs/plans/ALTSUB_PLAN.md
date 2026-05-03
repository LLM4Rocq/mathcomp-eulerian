# Plan: `altsub.v` — longest alternating subsequence

> **Forward-looking design document.** Phase B of the Stanley §1.6
> extension.  Adjacent to the existing `beta_swap.v` alternating-set
> work (Stanley Cor 1.6.5).

## 1. Goal

Stanley EC1 §1.6.2: the **longest alternating subsequence** statistic
`as(w)` for permutations w.  Headline theorem:

```
as(w) = 1 + #{turning points of w}
```

where a "turning point" is a position i where the direction
of w changes — `(w_i < w_{i+1}) ≠ (w_{i+1} < w_{i+2})`.

This makes `as(w)` computable directly from descent information,
without dynamic programming over subsequences.

## 2. Two-pronged definition

We give two definitions and prove they coincide:

```coq
(* Direct: count turning points, add 1 *)
Definition is_turn s (i : 'I_n.-1) : bool :=
  is_descent s (widen_ord _ i) (+) is_descent s (lift ord0 i).

Definition turn_count (s : {perm 'I_n.+1}) : nat :=
  #|[set i : 'I_n.-1 | is_turn s i]|.

Definition as_perm_direct (s : {perm 'I_n.+1}) : nat :=
  (turn_count s).+1.

(* Bijective: max length of alternating subsequence *)
Definition is_alt_subseq (xs : seq nat) : bool :=
  ... (* xs is alternating: xs_0 < xs_1 > xs_2 < xs_3 > ... *)

Definition as_perm (s : {perm 'I_n.+1}) : nat :=
  \max_(I : {set 'I_n.+1} | is_alt_subseq (sort_image s I)) #|I|.
```

The headline equivalence theorem:

```coq
Theorem as_perm_eq n (s : {perm 'I_n.+1}) :
  as_perm s = (turn_count s).+1.
```

## 3. Why this is interesting

- Connects to the existing alternating descent set work in
  `beta_swap.v`: the alternating descent set is exactly the case
  `as(w) = n+1` (longest possible).
- Gives a closed-form characterization of `as` in terms of
  descent data.
- The proof is a clean greedy argument: the optimal alt subseq
  picks one element from each "monotone run" (maximal intervals
  between turning points).

## 4. Estimated effort

| Section | LOC | Difficulty |
|---------|-----|------------|
| Imports + `is_turn` + `turn_count` defs | ~30 | low |
| `is_alt_subseq` + `as_perm` defs (greedy) | ~60 | medium |
| `turn_count` basic identities | ~40 | low |
| **`as_perm_eq` (the headline)** — greedy ≤ direct | ~100 | medium-high |
| **`as_perm_eq` — direct ≤ greedy (existence)** | ~100 | medium-high |
| Connection to alternating descent set | ~50 | low (reuses beta_swap.v) |
| **Total** | **~380 LOC** | |

The two-direction equivalence proof is the heart of the file.

## 5. Strategy

### 5.1 Greedy ≤ Direct (`as_perm s ≤ turn_count + 1`)

Any alternating subsequence has at most one element per "monotone
run" of `s`.  The number of monotone runs equals the number of
turning points + 1.  So `|alt subseq| ≤ turn_count + 1`.

### 5.2 Direct ≤ Greedy (existence of length `turn_count + 1`)

**Construction:** pick one element from each monotone run, choosing
the local max if the run is increasing-then-decreasing, the local
min if decreasing-then-increasing, etc.  Verify the result is
alternating.

This is the substantive direction.  ~100 LOC.

## 6. Risks

1. **Subsequence indexing.**  `is_alt_subseq` operates on `seq nat`
   (the image of an `{set}` under `s`, sorted by position).  Need
   to be careful with the `sort` to keep positions in order.

2. **Boundary cases.**  `n = 0` (S_1, single perm, as = 1, turn_count = 0).
   `n = 1` (S_2, two perms, both have as = 2 since any two distinct
   numbers form a length-2 alt subseq).

3. **The headline is on `'I_n.-1`** — annoyingly low-arity.  For
   `n = 0` (S_1), `'I_n.-1 = 'I_0` is empty, so `turn_count = 0`
   and `as_perm = 1`.  For `n = 1` (S_2), `'I_0` is also empty,
   `turn_count = 0`, `as_perm = 1` — but we want `as_perm = 2`!
   So the index has to be `'I_(size w - 2)` or similar. Re-check
   on small examples before committing to the def.

## 7. Sanity check

Compute `as_perm` and `turn_count` for a few small perms and verify
they match.  E.g., `s = [3; 1; 2]` (in S_3):
- `s` reads 3, 1, 2.
- 3 > 1 (descent), 1 < 2 (ascent) — direction changes — 1 turning point.
- as(s) = 2 (subsequences: [3, 1, 2] is descent then ascent — alternating
  of length 3? Wait, [3,1,2] has 3>1<2 — so it is an alternating
  subsequence of length 3, picking all three positions).
- turn_count + 1 = 1 + 1 = 2.

Discrepancy!  3 ≠ 2.  Re-derive...

Actually `[3, 1, 2]` itself is alternating: `3 > 1 < 2`. Length 3.
But turn_count is 1 (only one direction change).  So `as = turn_count + 2`?

Hmm, let me re-check.  An alternating sequence `a_1, a_2, ..., a_k`
has k-1 inequality signs, alternating > < > < or < > < >.  So
length k requires k-1 alternating signs.

For [3, 1, 2]: signs are >, <.  That's 2 alternating signs, length 3.

For the turning-point characterization: a "turning point" in the
ORIGINAL sequence is at position i where `(s_i < s_{i+1}) ≠ (s_{i+1} < s_{i+2})`.
For [3, 1, 2]: s_0=3, s_1=1, s_2=2.  At i=0: s_0 < s_1 is false (3>1).
At i=1: s_1 < s_2 is true (1<2).  Different — turning point at i=0.

So the original [3, 1, 2] has turn_count = 1, and IS itself
alternating of length 3.  So `as(s) ≥ 3`, but `turn_count + 1 = 2`.

That's wrong.  Let me reconsider.

OH — I had the formula wrong.  The correct formula (per Stanley)
might be:
  `as(w) = #{ascents and descents that are "extreme"} + 1`
or something more nuanced.

Actually I think the right formulation involves runs.  Let me rederive.

A "run" of `w` is a maximal monotonic substring.  For [3, 1, 2]:
runs are [3, 1] (decreasing) and [1, 2] (increasing).  Two runs.

The longest alternating subseq picks one element from each run +
the join points.  Specifically, picking the FIRST element of the
first run, the LAST element of each run after that, but with the
runs alternating direction.  For [3, 1, 2]: pick first of run 1
(= 3), last of run 1 = first of run 2 (= 1), last of run 2 (= 2).
That gives [3, 1, 2], all three.

So `as = #runs + 1` when all runs have length ≥ 1.  And #runs - 1
= turn_count (number of direction changes).  So `as = turn_count + 2`?

For [3, 1, 2]: #runs = 2, turn_count = 1, as = 3.  3 = 2 + 1.
3 = 1 + 2.  Both match `#runs + 1` and `turn_count + 2`.

For w = [1, 2, 3] (sorted ascending): runs = [1, 2, 3], one run.
turn_count = 0.  as = 2 (any two elements form an alternating
length-2 subseq).  `#runs + 1 = 2` ✓.  `turn_count + 2 = 2` ✓.

For w = [3, 2, 1]: as = 2 similarly, turn_count = 0, #runs = 1.

For w = [3, 1, 4, 2]: 3>1<4>2.  runs = [3,1], [1,4], [4,2]?  No,
runs are MAXIMAL monotone, so [3,1] (down) and [1,4] doesn't share —
runs are decided by direction change.  Sequence: 3, 1 (down), 1, 4
(up — direction change at position 1), 4, 2 (down — direction change
at position 2).  Runs: [3, 1], [1, 4], [4, 2] — 3 runs.  turn_count = 2.
as = ? The whole sequence is 3>1<4>2, alternating of length 4.
`#runs + 1 = 4` ✓.  `turn_count + 2 = 4` ✓.

OK so the right formula is `as = turn_count + 2` for non-trivial w
(i.e., w has length ≥ 2).  Special case: length 1, as = 1, turn_count
undefined (no positions for it).

Hmm wait — for [3, 1] (length 2), as = 2, turn_count is over 'I_0
(empty), so turn_count = 0.  `0 + 2 = 2` ✓.

For length 1 [a], as = 1.  We'd need a special case OR just say
turn_count is over 'I_(-1) which doesn't exist.

So the correct headline formula is:
```
as(w) = turn_count(w) + 2     (for length ≥ 2)
as(w) = 1                      (for length 1)
```

Or more uniformly via min:
```
as(w) = min(size(w), turn_count(w) + 2)
```

Actually even cleaner: just `turn_count + 2` and handle the edge
case in the boundary.

Let me re-scope this plan slightly.  The headline theorem is:
```
Theorem as_perm_eq n (s : {perm 'I_n.+2}) :   (* size >= 2 *)
  as_perm s = (turn_count s).+2.
```

Index n.+2 ensures size ≥ 2.

This is cleaner.  Let me update the plan accordingly.
