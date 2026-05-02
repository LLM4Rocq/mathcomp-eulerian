# Plan: `foata.v` — Foata's first fundamental bijection

> **Forward-looking design document.** Companion to
> [`INVERSIONS_PLAN.md`](INVERSIONS_PLAN.md).  Phase 3-4 of the §1.3
> extension.

## 1. Goal

Prove the classical **MacMahon equidistribution** of `inv` and `maj`
over permutations:

```coq
Theorem inv_maj_equidistr n k :
  #|[set s : {perm 'I_n.+1} | inv s == k]|
  = #|[set s : {perm 'I_n.+1} | maj s == k]|.
```

via Foata's first fundamental bijection `φ : S_n → S_n` satisfying
`maj(φ(w)) = inv(w)` for all `w`.

## 2. Strategy: work on seqs, then transport

Foata's bijection is most naturally defined on **sequences of distinct
naturals** (a.k.a. word permutations).  We already have
`perm_seq_bridge.v` connecting `{perm 'I_n}` to `seq nat`:

- `perm_to_seq : {perm 'I_n} -> seq nat` (image of `enum 'I_n`)
- `seq_to_perm` for the inverse direction
- `is_descent_seq` and `char_mono` for descent-pattern bridges

So the plan is:

1. Define `foata : seq nat -> seq nat` directly on words.
2. Prove the seq-level invariants:
   - `size (foata w) = size w`
   - `perm_eq (foata w) w`
   - `maj_seq (foata w) = inv_seq w`  (the key invariant)
   - `foata` is injective (and hence bijective, since size and
     multiset are preserved)
3. Define the seq versions `inv_seq` and `maj_seq` if not already
   present.
4. Lift to `{perm 'I_n.+1}` via the existing bridge and conclude
   equidistribution.

## 3. Foata's first fundamental bijection — definition

The classical recursive definition (see Stanley EC1 §1.3.3, p. 23 of
2nd ed.):

> Read `w = w_1 w_2 ... w_n` from left to right.  Maintain a "current
> word" `u_k = φ(w_1 ... w_k)`.  Start with `u_1 = w_1`.  At step
> `k+1`, look at the rightmost letter `x` of `u_k`:
>
> - If `x < w_{k+1}`: split `u_k` into maximal "blocks" each ending
>   with a letter that is **less than** `w_{k+1}`.  In each such
>   block, cyclically rotate so that the largest letter (which was at
>   the end of the block, but is "less than `w_{k+1}`") moves to the
>   front.  Append `w_{k+1}` to the end.
>
> - If `x > w_{k+1}`: do the symmetric thing — split into blocks ending
>   with letters **greater than** `w_{k+1}`, rotate each, append.
>
> - If `x = w_{k+1}`: impossible since the word has distinct letters.
>
> If `u_k` has only one letter, define the empty rotation result as
> `u_k`, then append.

There are a few equivalent formulations.  For a cleaner Rocq encoding,
consider the following operational form using a helper function
`foata_step`:

```coq
(* Cyclic rotation of a single block: move last letter to front. *)
Definition cyc_left (s : seq nat) : seq nat :=
  if s is x :: rest then rest ++ [:: x] else [::].
(* Wait — Foata moves last to front, so need: *)
Definition cyc_right (s : seq nat) : seq nat :=
  match s with
  | [::] => [::]
  | _ => last 0 s :: belast 0 s   (* careful with default *)
  end.

(* Split a word into blocks, each maximal s.t. last letter
   has property P (last is the "block separator"). *)
Definition split_blocks (P : nat -> bool) (s : seq nat) : seq (seq nat) :=
  ... (* fold or fixpoint that emits a new block whenever P fires *)

Definition foata_step (a : nat) (u : seq nat) : seq nat :=
  match u with
  | [::] => [:: a]
  | x :: _ =>
    let P := if x < a then (fun y => y < a) else (fun y => a < y) in
    flatten (map cyc_right (split_blocks P u)) ++ [:: a]
  end.

Fixpoint foata (w : seq nat) : seq nat :=
  match w with
  | [::] => [::]
  | a :: rest => foata_step a (foata rest)  (* careful: order matters *)
  end.
```

Actually the recursion is the other way — Foata processes `w`
left-to-right, so:

```coq
Definition foata (w : seq nat) : seq nat :=
  foldl (fun u a => foata_step a u) [::] w.
```

The exact direction (last-to-front vs first-to-back rotation, and
left-to-right vs right-to-left fold) is a convention choice; Stanley's
description must be matched precisely or the bijection breaks.

## 4. The key invariant

```coq
Lemma foata_step_maj_inv (a : nat) (u : seq nat) :
  uniq u -> a \notin u ->
  maj_seq (foata_step a u) = maj_seq u + (count (fun y => a < y) u).
```

Stanley's version: each `foata_step a u` adds `cinv(a, u)` (the number
of letters in `u` greater than `a`, the "left inversions" contributed
by `a`) to the major index.

By induction on the length of `w`:
- `inv_seq w = sum over k of (count (fun y => w_k < y) (w_1..w_{k-1}))`
- `maj_seq (foata w) = sum over k of (count (fun y => w_k < y) (foata_step's fragment)) = inv_seq w`

This is the heart of the bijection.

## 5. Bijectivity

`foata` is bijective on permutations of any finite set because:
- `size (foata w) = size w` (each step appends one letter).
- `perm_eq (foata w) w` (each step is a permutation of its input).
- It's injective on uniq seqs because there's an explicit inverse
  `foata_inv : seq nat -> seq nat` (by reversing each step: peel off
  the last letter, undo the cyclic rotations of blocks).

Alternatively, since size and multiset are preserved, `foata` is a
function `S_n → S_n`, and any function `S_n → S_n` that preserves a
nontrivial cardinality structure must be bijective if proven injective.

For the purposes of equidistribution, only **size + multiset
preservation + the key maj/inv invariant + injectivity** are needed.

## 6. Lifting to `{perm 'I_n.+1}`

```coq
Definition foata_perm (s : {perm 'I_n.+1}) : {perm 'I_n.+1} :=
  seq_to_perm (foata_size_eq s)
              (foata_uniq s)
              (foata_bnd s).

Lemma foata_perm_inv_maj s :
  maj (foata_perm s) = inv s.
```

via the seq-level invariants and the bridges in `perm_seq_bridge.v`.

## 7. Equidistribution

```coq
Theorem inv_maj_equidistr n k :
  #|[set s : {perm 'I_n.+1} | inv s == k]|
  = #|[set s : {perm 'I_n.+1} | maj s == k]|.
Proof.
(* Set up the bijection foata_perm; show it maps the inv-k set
   to the maj-k set bijectively via foata_perm_inv_maj. *)
...
Qed.
```

## 8. Estimated effort

| Section | LOC | Difficulty |
|---------|-----|------------|
| seq-level helpers (`cyc_right`, `split_blocks`) | ~80 | low |
| `foata_step` definition + size/uniq/perm_eq | ~60 | low |
| `inv_seq`, `maj_seq` (if not already there) | ~40 | low |
| `foata_step_maj_inv` (key invariant) | ~150 | **high** |
| `foata` definition + invariant chain | ~80 | medium |
| Injectivity (or explicit inverse) | ~100 | high |
| Lift to `{perm}` + equidistribution | ~80 | medium |
| **Total** | **~590 LOC** | |

This is roughly the size of `stirling_fiber.v` + half of
`perm_seq_bridge.v`.  Devil's advocate would estimate 2-3 days
single-developer, with the key invariant proof (`foata_step_maj_inv`)
being the make-or-break step.

## 9. Risks

1. **Convention mismatch.** Foata's bijection has multiple
   equivalent descriptions in the literature (rotate left vs right,
   process left-to-right vs right-to-left, blocks ending in
   greater-than vs less-than letters).  A cleanly-formalized version
   needs to commit to one set of conventions and stick with it.
   Picking wrong wastes time.

2. **The key invariant proof.** `foata_step_maj_inv` requires a
   careful sum manipulation: each cyclic rotation moves descents in
   a precise way, and the count of "letters greater than `a`"
   exactly matches the descent shift.  Off-by-ones likely.

3. **Sanity-check baked in.** Before the invariant proof, compute
   `foata [:: 3; 1; 4; 1; 5; 9; 2; 6]` (or similar) by hand and via
   `vm_compute`, and verify the `maj` matches the `inv` of the input.
   If the bijection is wrong, this catches it early.

4. **Bijectivity vs. just-injective.** For the equidistribution we
   only need foata to be a *function*  whose image is the same finite
   set; that follows from size + multiset preservation.  No need for
   an explicit inverse — saves ~100 LOC.  Use:
   ```
   bij_on_card_inj : (forall x in A, f x in A) -> #|A| = #|f @: A|
                  -> {in A &, injective f} -> {in A, bijective f}
   ```
   or build a bijection between `{s | inv s == k}` and `{s | maj s == k}`
   via foata + `foata_perm_inv_maj` directly.

## 10. Quick-start for the interactive session

1. Open `/workspace/foata.v` (new file).
2. Define `cyc_right`, `split_blocks`, `foata_step`, `foata` first.
3. **Sanity check**: `Compute foata [:: 3; 1; 4; 1; 5; 9; 2; 6]`
   (or with distinct letters: `[:: 3; 1; 4; 5; 9; 2; 6]`) and verify
   maj/inv match.  Fix conventions before proceeding.
4. Prove size, uniq, perm_eq lemmas.
5. Prove `foata_step_maj_inv` interactively, with `rocq_check` on
   each subgoal.
6. Lift to `{perm}` via the bridges.
7. Equidistribution.
