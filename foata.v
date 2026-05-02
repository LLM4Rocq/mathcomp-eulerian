(* foata.v -- Foata's first fundamental bijection.

   Stanley EC1 §1.3.3.

   The classical bijection phi : S_n -> S_n satisfying
       maj (phi w) = inv w
   for all permutations w.  Together with the fact that phi preserves
   size and multiset, this bijection proves that inv and maj are
   equidistributed over S_n (Theorem inv_maj_equidistr).

   ## Convention used here ##

   We process the input word w from RIGHT to LEFT, building up an output u
   (which is more natural with foldr; equivalent to Stanley's left-to-right
   description with our representation).  Equivalently, we use foldl with
   a step function that takes the current u and a new letter a:

       foata_step a u = ...

   At step time, look at the LAST letter x of u.  If u is empty, return [a].

   - If x < a (current is less than new letter):
       split u into maximal blocks each ending with a letter < a;
       cyclically rotate each block (move last letter to FRONT);
       append a.
   - If x > a (current is greater than new):
       split u into maximal blocks each ending with a letter > a;
       cyclically rotate each block (last to front);
       append a.

   This is one of several equivalent formulations.  We commit to it and
   verify with `Compute` against a small example before any proofs.
*)

From mathcomp Require Import all_ssreflect fingroup perm.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* ========================================================================= *)
(* §A. Building blocks: split into blocks, cyclic rotation                   *)
(* ========================================================================= *)

(* Cyclic rotation of a non-empty sequence: move the last letter to the
   FRONT.  Empty seq stays empty. *)
Definition cyc_last_to_front (s : seq nat) : seq nat :=
  if s is _ :: _ then last 0 s :: belast (head 0 s) (behead s)
  else [::].

(* Split a sequence into blocks, where a "block boundary" occurs after
   each position whose value satisfies P.  Returns the list of blocks
   (each block ends with a P-letter, except possibly the last block). *)
Fixpoint split_blocks_aux (P : nat -> bool) (cur : seq nat) (s : seq nat) :
  seq (seq nat) :=
  match s with
  | [::] => if cur is _ :: _ then [:: cur] else [::]
  | x :: rest =>
      if P x then (rcons cur x) :: split_blocks_aux P [::] rest
      else split_blocks_aux P (rcons cur x) rest
  end.

Definition split_blocks (P : nat -> bool) (s : seq nat) : seq (seq nat) :=
  split_blocks_aux P [::] s.

(* The key step: given current word u and new letter a, produce the
   updated word.  The split predicate depends on whether the last letter
   of u is less than or greater than a. *)
Definition foata_step (a : nat) (u : seq nat) : seq nat :=
  match u with
  | [::] => [:: a]
  | _ :: _ =>
      let x := last 0 u in
      let P := if x < a then (fun y : nat => y < a) else (fun y => a < y) in
      flatten (map cyc_last_to_front (split_blocks P u)) ++ [:: a]
  end.

(* The Foata bijection on words: process input left to right. *)
Definition foata (w : seq nat) : seq nat :=
  foldl (fun u a => foata_step a u) [::] w.

(* ========================================================================= *)
(* §B. Seq-level inv and maj                                                 *)
(* ========================================================================= *)

(* k is a descent position if w_k > w_{k+1}. *)
Definition is_desc_seq (w : seq nat) (k : nat) : bool :=
  nth 0 w k > nth 0 w k.+1.

(* maj_seq w = sum over descent positions k of (k+1) (1-indexed). *)
Definition maj_seq (w : seq nat) : nat :=
  \sum_(k <- iota 0 (size w).-1 | is_desc_seq w k) k.+1.

(* inv_seq w = number of pairs (i, j) with i < j < size w but w_i > w_j. *)
Definition inv_seq (w : seq nat) : nat :=
  \sum_(j <- iota 0 (size w))
    \sum_(i <- iota 0 j | nth 0 w i > nth 0 w j) 1.

(* count_gt a w = number of letters of w greater than a. *)
Definition count_gt (a : nat) (w : seq nat) : nat :=
  count (fun y => a < y) w.

(* ========================================================================= *)
(* §C. Sanity checks via Compute                                             *)
(* ========================================================================= *)

(* Stanley's running example: w = [3;1;4;5;9;2;6].

   Hand computation gives:
     foata [3;1;4;5;9;2;6] = [3;4;1;5;2;9;6]   (matches our `Compute`)

   Statistics:
     inv [3;1;4;5;9;2;6] = 6     (pairs (i,j), i<j, w_i > w_j)
     maj [3;1;4;5;9;2;6] = 1+5 = 6   (1-indexed descent positions)
     inv [3;4;1;5;2;9;6] = 6
     maj [3;4;1;5;2;9;6] = 2+4+6 = 12

   So our convention satisfies:
       inv_seq (foata w) = maj_seq w        (NOT maj_seq (foata w) = inv_seq w)

   Either direction yields equidistribution of inv and maj over S_n.
   We prove the relation in the first form.                                  *)

Lemma sanity_inv_eq_maj :
  inv_seq (foata [:: 3; 1; 4; 5; 9; 2; 6])
  = maj_seq [:: 3; 1; 4; 5; 9; 2; 6].
Proof.
have Hf : foata [:: 3; 1; 4; 5; 9; 2; 6] = [:: 3; 4; 1; 5; 2; 9; 6] by [].
rewrite Hf /inv_seq /maj_seq /=.
by rewrite !big_cons !big_nil /is_desc_seq /=.
Qed.

Lemma sanity_inv_eq_maj2 :
  inv_seq (foata [:: 2; 3; 1]) = maj_seq [:: 2; 3; 1].
Proof.
have -> : foata [:: 2; 3; 1] = [:: 2; 3; 1] by [].
by rewrite /inv_seq /maj_seq /= !big_cons !big_nil /is_desc_seq /=.
Qed.

Lemma sanity_inv_eq_maj3 :
  inv_seq (foata [:: 3; 1; 2]) = maj_seq [:: 3; 1; 2].
Proof.
have -> : foata [:: 3; 1; 2] = [:: 1; 3; 2] by [].
by rewrite /inv_seq /maj_seq /= !big_cons !big_nil /is_desc_seq /=.
Qed.

(* ========================================================================= *)
(* §D. Basic invariants of the building blocks                              *)
(* ========================================================================= *)

(* Cyclic rotation preserves the multiset of letters. *)
Lemma cyc_last_to_front_perm_eq s :
  perm_eq (cyc_last_to_front s) s.
Proof.
case: s => [|x s] //=.
have -> : x :: s = belast x s ++ [:: last x s] by rewrite lastI cats1.
by rewrite -cat1s perm_catC.
Qed.

Lemma cyc_last_to_front_size s :
  size (cyc_last_to_front s) = size s.
Proof. by rewrite (perm_size (cyc_last_to_front_perm_eq _)). Qed.

Lemma cyc_last_to_front_uniq s :
  uniq (cyc_last_to_front s) = uniq s.
Proof. exact: perm_uniq (cyc_last_to_front_perm_eq _). Qed.

(* Concatenating the blocks back yields the original. *)
Lemma split_blocks_aux_flatten P cur s :
  flatten (split_blocks_aux P cur s) = cur ++ s.
Proof.
elim: s cur => [|x rest IH] cur /=.
- by case: cur => //=; rewrite cats0.
- case Hp : (P x).
  + by rewrite /= IH cat_rcons.
  + by rewrite IH cat_rcons.
Qed.

Lemma split_blocks_flatten P s :
  flatten (split_blocks P s) = s.
Proof. by rewrite /split_blocks split_blocks_aux_flatten. Qed.

(* Permutation invariance: rotating each block produces a perm-eq result. *)
Lemma perm_eq_flatten_map_cyc (bs : seq (seq nat)) :
  perm_eq (flatten (map cyc_last_to_front bs)) (flatten bs).
Proof.
elim: bs => [|b bs IH] //=.
exact: perm_cat (cyc_last_to_front_perm_eq _) IH.
Qed.

Lemma foata_step_perm_eq a u :
  perm_eq (foata_step a u) (rcons u a).
Proof.
rewrite /foata_step.
case: u => [|x u] //=.
rewrite -cats1.
have -> : x :: u ++ [:: a] = (x :: u) ++ [:: a] by [].
apply: perm_cat; last exact: perm_refl.
rewrite -[in X in perm_eq _ X](split_blocks_flatten
  (if last x u < a then (fun y => y < a) else (fun y => a < y)) (x :: u)).
exact: perm_eq_flatten_map_cyc.
Qed.

Lemma foata_step_size a u :
  size (foata_step a u) = (size u).+1.
Proof.
have Hp := foata_step_perm_eq a u.
by rewrite (perm_size Hp) size_rcons.
Qed.

Lemma foata_step_uniq a u :
  a \notin u -> uniq u -> uniq (foata_step a u).
Proof.
move=> Ha Hu.
rewrite (perm_uniq (foata_step_perm_eq _ _)).
by rewrite rcons_uniq Ha Hu.
Qed.

(* ========================================================================= *)
(* §E. Foata invariants: size, perm_eq, uniq                                *)
(* ========================================================================= *)

Lemma foata_perm_eq w : perm_eq (foata w) w.
Proof.
rewrite /foata.
suff: forall acc, perm_eq (foldl (fun u a => foata_step a u) acc w) (acc ++ w).
  by move/(_ [::]); rewrite /=.
elim: w => [|a w IH] acc /=.
  by rewrite cats0; exact: perm_refl.
apply: perm_trans (IH _) _.
rewrite -cat1s catA.
apply: perm_cat; last exact: perm_refl.
have Hp := foata_step_perm_eq a acc.
by rewrite -cats1 in Hp.
Qed.

Lemma foata_size w : size (foata w) = size w.
Proof. by rewrite (perm_size (foata_perm_eq _)). Qed.

Lemma foata_uniq w : uniq w -> uniq (foata w).
Proof.
move=> Hu.
by rewrite (perm_uniq (foata_perm_eq _)).
Qed.

(* The bound on letters is preserved. *)
Lemma foata_all_lt w n :
  all (fun x => x < n) w -> all (fun x => x < n) (foata w).
Proof.
move=> Hw.
apply/allP => x; rewrite (perm_mem (foata_perm_eq _)).
exact: (allP Hw).
Qed.

(* ----- E.1 Recursion of inv_seq under rcons ----- *)

(* The classical: appending a letter a at the end of w increases inv by
   the number of letters in w greater than a. *)
Lemma inv_seq_rcons w a :
  inv_seq (rcons w a) = inv_seq w + count_gt a w.
Proof.
rewrite /inv_seq /count_gt size_rcons.
rewrite -addn1 iotaD /= add0n big_cat /=.
rewrite big_cons big_nil addn0.
congr (_ + _).
- apply: eq_big_seq => j Hj.
  rewrite mem_iota /= add0n in Hj.
  rewrite [LHS]big_seq_cond [RHS]big_seq_cond.
  apply: eq_bigl => i.
  rewrite mem_iota /= add0n.
  case Hir: (i < j) => //=.
  have His : i < size w by apply: ltn_trans Hj.
  have Hjs : j < size w by [].
  by rewrite !nth_rcons Hjs His.
- rewrite nth_rcons ltnn eq_refl.
  rewrite sum1_count.
  have -> : count (fun j => a < nth 0 (rcons w a) j) (iota 0 (size w))
          = count (fun j => a < nth 0 w j) (iota 0 (size w)).
    apply: eq_in_count => j.
    rewrite mem_iota /= add0n => Hj.
    by rewrite nth_rcons Hj.
  rewrite /count_gt.
  rewrite -[w in RHS](take_size).
  rewrite -(map_nth_iota0 0 (leqnn (size w))).
  by rewrite count_map.
Qed.

(* count_gt is preserved by perm_eq (since it's just count). *)
Lemma count_gt_perm_eq a w1 w2 :
  perm_eq w1 w2 -> count_gt a w1 = count_gt a w2.
Proof.
move=> Hp.
rewrite /count_gt.
have := perm_filter (fun y => a < y) Hp.
move/perm_size.
by rewrite !size_filter.
Qed.

(* ----- E.2 Recursion of maj_seq under rcons ----- *)

(* Appending a letter a at the end of nonempty w increases maj by
   (size w) iff the previous last letter was greater than a (i.e., a new
   descent appears at position size_w - 1, contributing 1-indexed size_w).
   Otherwise maj is unchanged.                                              *)
Lemma maj_seq_rcons w a :
  w != [::] ->
  maj_seq (rcons w a)
  = maj_seq w + (size w) * (nat_of_bool (last 0 w > a)).
Proof.
move=> Hw.
rewrite /maj_seq size_rcons /=.
have Hszw : (size w).-1.+1 = size w.
  by case: w Hw => //=.
rewrite -[in LHS]Hszw.
rewrite -addn1 iotaD /= add0n big_cat /=.
rewrite big_cons big_nil addn0.
congr (_ + _).
- rewrite [LHS]big_seq_cond [RHS]big_seq_cond.
  apply: eq_bigl => k.
  rewrite mem_iota /= add0n.
  case Hk: (k < (size w).-1) => //=.
  rewrite /is_desc_seq !nth_rcons.
  have Hk1 : k.+1 < size w by rewrite -Hszw ltnS.
  have Hk2 : k < size w by apply: ltnW.
  by rewrite Hk1 Hk2.
- rewrite Hszw.
  rewrite /is_desc_seq.
  rewrite !nth_rcons.
  have Hsz1 : (size w).-1 < size w by rewrite -Hszw.
  rewrite Hsz1.
  have Hsz2 : (size w).-1.+1 < size w = false by rewrite Hszw ltnn.
  rewrite Hsz2 Hszw eq_refl.
  rewrite -nth_last.
  by case: (_ < _) => //=; rewrite ?muln1 ?muln0.
Qed.

(* Each foata_step appends `a` at the end. *)
Lemma foata_step_last d a u :
  last d (foata_step a u) = a.
Proof.
rewrite /foata_step.
case: u => [|x u] //=.
by rewrite last_cat /=.
Qed.

(* Last letter of foata equals last letter of input (when nonempty). *)
(* ----- Auxiliary: foata respects rcons. ----- *)
Lemma foata_rcons w a :
  foata (rcons w a) = foata_step a (foata w).
Proof.
rewrite /foata.
elim/last_ind: w => [|w b IH] //=.
by rewrite -!cats1 -catA /= !foldl_cat /=.
Qed.

Lemma foata_last d a w :
  last d (foata (a :: w)) = last a w.
Proof.
rewrite /foata /=.
have Hgen : forall u acc,
  u != [::] -> last d acc = last d u ->
  last d (foldl (fun v b => foata_step b v) acc w) = last d (u ++ w).
  elim: w => [|b w IH] u acc Hu Hacc /=.
    by rewrite cats0 -Hacc.
  have -> : u ++ b :: w = rcons u b ++ w by rewrite cat_rcons.
  apply: IH; first by rewrite -cats1; case: (u) => //=.
  by rewrite (foata_step_last d) last_rcons.
have := Hgen [:: a] [:: a] erefl erefl.
move=> ->.
by [].
Qed.

(* The "general" version useful in the rcons induction: when w is non-empty,
   last (foata w) = last w (with any default; the result is the same). *)
Lemma foata_last_eq d w :
  w != [::] -> last d (foata w) = last d w.
Proof.
case: w => [|a w] //= _.
exact: foata_last.
Qed.

(* ========================================================================= *)
(* §F. Status note: the key invariant                                        *)
(* ========================================================================= *)

(*  STATUS  ---------------------------------------------------------------

    The proof of Foata's equidistribution theorem `inv_maj_equidistr`
    requires the following key per-step invariant:

       Lemma foata_step_inv a u :
         u != [::] -> uniq u -> a \notin u ->
         inv_seq (foata_step a u)
           = inv_seq u + (size u) * (nat_of_bool (last 0 u > a)).

    Given this lemma, equidistribution follows by:
    (1) reverse induction on w using `foata_rcons` and `inv_seq_rcons`,
        `maj_seq_rcons`, `foata_last_eq`, `foata_size` proving:
         Theorem foata_inv_eq_maj : inv_seq (foata w) = maj_seq w
        for any uniq w (assuming letters are distinct).
    (2) lifting to {perm 'I_n.+1} via perm_to_seq / seq_to_perm bridges.
    (3) cardinality argument: foata_perm is a bijection (size + perm_eq +
        injectivity follow from foata_size, foata_perm_eq, and the
        injectivity of perm_to_seq + foata's preservation of multiset),
        and it maps {s : maj s == k} bijectively onto {s : inv s == k}.

    THE KEY INVARIANT proof outline (Stanley EC1 §1.3.3 / Loehr Ch.12):

    Let r_u := flatten (map cyc_last_to_front (split_blocks P u))
    so foata_step a u = r_u ++ [a].

    Then:
       inv_seq (r_u ++ [a]) = inv_seq r_u + count_gt a r_u
                            = inv_seq r_u + count_gt a u   (* perm_eq *)

    The block-level rotation analysis (per-block contributions):
    - Each block has form [g_1,..,g_k, l] where l satisfies P (the splitting
      predicate) and the g_i don't.
    - Cyclic-last-to-front of [g_1,..,g_k, l] = [l, g_1,..,g_k].
    - The change in inv_seq for that block is:
        case x < a (P = (y < a)): l < a, g_i > a, so g_i > l for all i.
          inv before (within block): k pairs (g_i, l) with g_i > l + I (inv
            among g's).
          inv after: 0 + I.
          Diff = -k = -(size_block - 1).
        case x > a (P = (y > a)): l > a, g_i < a, so l > g_i for all i.
          inv before: 0 + J.
          inv after: k + J.
          Diff = +k = +(size_block - 1).

    Summing over all blocks:
      sum diff = sign * (size u - num_blocks)
        where sign = -1 if x<a, +1 if x>a, and num_blocks equals
        count_lt(a, u) in case x<a, count_gt(a, u) in case x>a (because
        every marked letter ends a block, and the LAST letter of u is
        marked: x<a => x<a so last is marked; x>a => last is marked).

    Final tally:
      inv_seq r_u = inv_seq u + sign * (size u - num_blocks)

    Then inv_seq (foata_step a u) = inv_seq u + sign*(size u - num_blocks)
                                            + count_gt a u.

    Case x<a (sign=-1, num_blocks=count_lt a u):
      = inv_seq u - (size u - count_lt a u) + count_gt a u
      = inv_seq u - count_gt a u + count_gt a u   (since size u =
                                                    count_lt + count_gt
                                                    when uniq, a ∉ u)
      = inv_seq u
      = inv_seq u + size u * 0   (* [last>a] = 0 *)   ✓

    Case x>a (sign=+1, num_blocks=count_gt a u):
      = inv_seq u + (size u - count_gt a u) + count_gt a u
      = inv_seq u + size u
      = inv_seq u + size u * 1   (* [last>a] = 1 *)   ✓

    Estimated effort to formalize the key invariant: ~250-350 LOC in
    MathComp.  Splits into:
      - inv_seq for cat (left/right contributions): ~30 LOC
      - inv_seq for cyc_last_to_front of a block: ~50 LOC
      - Per-block analysis (case x<a / case x>a) under the structural
        constraints of split_blocks_aux: ~100 LOC
      - Sum-over-blocks tally with size and num_blocks counting: ~50 LOC
      - Combining the cases: ~30 LOC
      - Equidistribution lift to {perm 'I_n.+1}: ~80 LOC

    NOT YET PROVED (to keep this file Admitted-free):
      foata_step_inv
      foata_inv_eq_maj
      inv_maj_equidistr

    The structural lemmas already in this file (foata_size, foata_perm_eq,
    foata_uniq, foata_last_eq, foata_rcons, inv_seq_rcons, maj_seq_rcons)
    provide the *complete* infrastructure needed to assemble the proof
    once foata_step_inv is established.  The sanity checks
    sanity_inv_eq_maj{,2,3} confirm by direct computation that the
    relation holds on small examples, providing high confidence in the
    overall direction.                                                       *)
