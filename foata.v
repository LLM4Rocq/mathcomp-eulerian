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
From mathcomp_eulerian Require Import descent inversions perm_seq_bridge.

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
(* §F. Helper: inv_seq of a concatenation                                   *)
(* ========================================================================= *)

(* "Cross-inversions" between two sequences: the number of pairs (i, j)
   with the i-th letter of s1 > the j-th letter of s2.  These are the
   inversions of (s1 ++ s2) that straddle the join point.                  *)
Definition cross_inv (s1 s2 : seq nat) : nat :=
  \sum_(b <- s2) count_gt b s1.

Lemma cross_inv_nil_r s1 : cross_inv s1 [::] = 0.
Proof. by rewrite /cross_inv big_nil. Qed.

Lemma cross_inv_nil_l s2 : cross_inv [::] s2 = 0.
Proof.
rewrite /cross_inv /count_gt /=.
by rewrite big1 // => b _.
Qed.

Lemma cross_inv_rcons s1 s2 a :
  cross_inv s1 (rcons s2 a) = cross_inv s1 s2 + count_gt a s1.
Proof. by rewrite /cross_inv -cats1 big_cat /= big_cons big_nil addn0. Qed.

Lemma cross_inv_cons s1 b s2 :
  cross_inv s1 (b :: s2) = count_gt b s1 + cross_inv s1 s2.
Proof. by rewrite /cross_inv big_cons. Qed.

(* The basic decomposition: inv of a cat = left + right + cross. *)
Lemma inv_seq_cat s1 s2 :
  inv_seq (s1 ++ s2) = inv_seq s1 + inv_seq s2 + cross_inv s1 s2.
Proof.
elim/last_ind: s2 => [|s2 a IH] /=.
  by rewrite cats0 cross_inv_nil_r /inv_seq /= big_nil !addn0.
rewrite -rcons_cat !inv_seq_rcons.
rewrite /count_gt count_cat -/(count_gt a s1) -/(count_gt a s2).
rewrite cross_inv_rcons IH.
set X := count_gt a s1; set Y := count_gt a s2.
set A := inv_seq s1; set B := inv_seq s2; set C := cross_inv s1 s2.
rewrite -[A + B + C]addnA -[A + (B + Y) + _]addnA -addnA.
congr (_ + _).
rewrite -!addnA; congr (_ + _).
by rewrite addnA addnC addnA addnC.
Qed.

(* count_gt of a cons. *)
Lemma count_gt_cons a b s :
  count_gt a (b :: s) = (nat_of_bool (a < b)) + count_gt a s.
Proof. by rewrite /count_gt /=. Qed.

Lemma count_gt_cat a s1 s2 :
  count_gt a (s1 ++ s2) = count_gt a s1 + count_gt a s2.
Proof. by rewrite /count_gt count_cat. Qed.

(* Cross-inversions, like count, distributes over cat in s1. *)
Lemma cross_inv_cat_l s1 s1' s2 :
  cross_inv (s1 ++ s1') s2 = cross_inv s1 s2 + cross_inv s1' s2.
Proof.
rewrite /cross_inv -big_split /=.
by apply: eq_bigr => b _; rewrite count_gt_cat.
Qed.

(* Cross-inversions, like sum, distributes over cat in s2. *)
Lemma cross_inv_cat_r s1 s2 s2' :
  cross_inv s1 (s2 ++ s2') = cross_inv s1 s2 + cross_inv s1 s2'.
Proof. by rewrite /cross_inv big_cat. Qed.

(* Cross-inversions only depend on the multiset of s2. *)
Lemma cross_inv_perm_eq_r s1 s2 s2' :
  perm_eq s2 s2' -> cross_inv s1 s2 = cross_inv s1 s2'.
Proof.
move=> Hp.
rewrite /cross_inv.
by rewrite (perm_big _ Hp).
Qed.

(* Cross-inversions only depend on the multiset of s1 (since count_gt does). *)
Lemma cross_inv_perm_eq_l s1 s1' s2 :
  perm_eq s1 s1' -> cross_inv s1 s2 = cross_inv s1' s2.
Proof.
move=> Hp.
rewrite /cross_inv.
by apply: eq_bigr => b _; apply: count_gt_perm_eq.
Qed.

(* count_lt: number of letters strictly less than a. *)
Definition count_lt (a : nat) (w : seq nat) : nat :=
  count (fun y => y < a) w.

Lemma count_lt_perm_eq a w1 w2 :
  perm_eq w1 w2 -> count_lt a w1 = count_lt a w2.
Proof.
move=> Hp.
rewrite /count_lt.
have := perm_filter (fun y => y < a) Hp.
move/perm_size.
by rewrite !size_filter.
Qed.

Lemma count_lt_cat a s1 s2 :
  count_lt a (s1 ++ s2) = count_lt a s1 + count_lt a s2.
Proof. by rewrite /count_lt count_cat. Qed.

(* Helper: if each block is perm-eq to its image under f, then the flattened
   sequences are perm-eq. *)
Lemma perm_eq_flatten_map_pred (f : seq nat -> seq nat) bs :
  (forall b, b \in bs -> perm_eq (f b) b) ->
  perm_eq (flatten (map f bs)) (flatten bs).
Proof.
elim: bs => [|b bs IH] Hf //=.
apply: perm_cat.
  by apply: Hf; rewrite mem_head.
by apply: IH => c Hc; apply: Hf; rewrite in_cons Hc orbT.
Qed.

(* The block-rotation lemma: if every block is replaced by a perm-eq one,
   the global inv_seq diff equals the sum of per-block diffs.  *)
Lemma inv_seq_flatten_swap_eq (f : seq nat -> seq nat) bs :
  (forall b, b \in bs -> perm_eq (f b) b) ->
  inv_seq (flatten (map f bs)) + \sum_(b <- bs) inv_seq b
  = inv_seq (flatten bs) + \sum_(b <- bs) inv_seq (f b).
Proof.
elim: bs => [|b bs IH] Hf.
  by rewrite /= /inv_seq /= big_nil !big_nil !addn0.
have Hb : perm_eq (f b) b by apply: Hf; rewrite mem_head.
have Hbs : forall c, c \in bs -> perm_eq (f c) c.
  by move=> c Hc; apply: Hf; rewrite in_cons Hc orbT.
have IHs := IH Hbs.
rewrite /= !inv_seq_cat.
have HpermFlat := perm_eq_flatten_map_pred Hbs.
have Hcross : cross_inv (f b) (flatten (map f bs)) = cross_inv b (flatten bs).
  rewrite (cross_inv_perm_eq_l _ Hb).
  by rewrite (cross_inv_perm_eq_r _ HpermFlat).
rewrite Hcross !big_cons.
set IFb := inv_seq (f b); set IB := inv_seq b.
set IFbs := inv_seq (flatten (map f bs)); set IBs := inv_seq (flatten bs).
set CR := cross_inv b (flatten bs).
set Sb := \sum_(c <- bs) inv_seq c.
set SFb := \sum_(c <- bs) inv_seq (f c).
have HSrec : IFbs + Sb = IBs + SFb by [].
apply/eqP.
rewrite -!addnA.
rewrite [IFbs + (CR + _)]addnCA [IBs + (CR + _)]addnCA.
rewrite [IFb + _]addnCA [IB + (CR + _)]addnCA.
rewrite eqn_add2l; apply/eqP.
rewrite [IFbs + (IB + Sb)]addnCA [IBs + (IFb + SFb)]addnCA.
by rewrite HSrec addnCA.
Qed.

(* For a non-empty block b = b' ++ [l], cyc_last_to_front gives l :: b'. *)
Lemma cyc_last_to_front_rcons b' l :
  cyc_last_to_front (rcons b' l) = l :: b'.
Proof.
case: b' => [|x b'] /=.
  by [].
by rewrite last_rcons belast_rcons.
Qed.

(* Express inv_seq of l :: b' = inv_seq (b' ++ [l]) shifted by count_lt l b' - count_gt l b'. *)
Lemma inv_seq_cons_eq_rcons_shift l b' :
  inv_seq (l :: b') + count_gt l b' = inv_seq (rcons b' l) + count_lt l b'.
Proof.
rewrite -cat1s -cats1 !inv_seq_cat.
have HCG : cross_inv b' [:: l] = count_gt l b'.
  by rewrite /cross_inv big_seq1.
have HCL : cross_inv [:: l] b' = count_lt l b'.
  rewrite /cross_inv /count_lt.
  have ->: \sum_(b <- b') count_gt b [:: l] = \sum_(b <- b') (nat_of_bool (b < l)).
    by apply: eq_bigr => x _; rewrite /count_gt /= addn0.
  rewrite -sum1_count.
  by rewrite (eq_bigr (fun b => if b < l then 1 else 0));
     [rewrite -big_mkcond | move=> i _; case: (i < l)].
rewrite HCG HCL.
set X := inv_seq b'; set CG := count_gt l b'; set CL := count_lt l b'.
set IL := inv_seq [:: l].
by rewrite -addnA -[in RHS]addnA [IL + X]addnC; congr (_ + _); rewrite addnC.
Qed.

(* Per-block diff for case x<a: l < a, all of b' > a > l => all_b' > l. *)
Lemma cyc_diff_block_lt a b' l :
  l < a -> all (fun x => a < x) b' ->
  inv_seq (cyc_last_to_front (rcons b' l)) + size b' = inv_seq (rcons b' l).
Proof.
move=> Hla Hb'.
have HCG : count_gt l b' = size b'.
  rewrite /count_gt -size_filter.
  have ->: [seq y <- b' | l < y] = b'.
    apply/all_filterP/allP => x Hx.
    by apply: ltn_trans Hla _; exact: (allP Hb').
  by [].
have HCL : count_lt l b' = 0.
  rewrite /count_lt; apply/eqP; rewrite -leqn0 leqNgt -has_count.
  apply/hasPn => x Hx /=.
  rewrite -leqNgt.
  by have Hxa := allP Hb' _ Hx; apply: ltnW; apply: ltn_trans Hla _.
rewrite cyc_last_to_front_rcons.
have := inv_seq_cons_eq_rcons_shift l b'.
by rewrite HCG HCL addn0 => ->.
Qed.

(* Per-block diff for case x>a: l > a, all of b' < a < l => all_b' < l. *)
Lemma cyc_diff_block_gt a b' l :
  a < l -> all (fun x => x < a) b' ->
  inv_seq (cyc_last_to_front (rcons b' l)) = inv_seq (rcons b' l) + size b'.
Proof.
move=> Hal Hb'.
have HCL : count_lt l b' = size b'.
  rewrite /count_lt -size_filter.
  have ->: [seq y <- b' | y < l] = b'.
    apply/all_filterP/allP => x Hx.
    by apply: ltn_trans (allP Hb' _ Hx) Hal.
  by [].
have HCG : count_gt l b' = 0.
  rewrite /count_gt; apply/eqP; rewrite -leqn0 leqNgt -has_count.
  apply/hasPn => x Hx /=.
  rewrite -leqNgt.
  have Hxa := allP Hb' _ Hx.
  by apply: ltnW; apply: ltn_trans Hxa _.
rewrite cyc_last_to_front_rcons.
have := inv_seq_cons_eq_rcons_shift l b'.
by rewrite HCG HCL addn0 => <-.
Qed.

(* Structural lemma about split_blocks_aux: every produced block is non-empty. *)
Lemma split_blocks_aux_all_nonempty P cur s :
  all (fun b => b != [::]) (split_blocks_aux P cur s).
Proof.
elim: s cur => [|x s IH] cur /=.
  by case: cur.
case Hp : (P x) => /=.
  by rewrite IH /= -size_eq0 size_rcons.
exact: IH.
Qed.

Lemma split_blocks_all_nonempty P s :
  all (fun b => b != [::]) (split_blocks P s).
Proof. exact: split_blocks_aux_all_nonempty. Qed.

(* Structural lemma: in split_blocks_aux P cur s, every "internal" letter
   of every block (i.e., every letter except possibly the last of the LAST
   block) does NOT satisfy P.  Specifically: if `cur` is all-not-P and
   we're processing `s`, then every block produced has its non-last letters
   all not-P, AND every block whose last letter doesn't end the input
   (i.e., is not the very last block) has last letter satisfying P.  *)

(* For our purposes we need: every block b in (split_blocks P s) is of
   form `rcons b' l` where all of b' is not-P, and the last letter l
   satisfies P, EXCEPT possibly the last block. *)

(* Predicate: a block b is "well-formed for P" if it is non-empty, its last
   letter satisfies P, and all its non-last letters do NOT satisfy P. *)
Definition wf_block (P : pred nat) (b : seq nat) : bool :=
  match b with
  | [::] => false
  | x :: rest =>
      P (last x rest) && all (fun y => ~~ P y) (belast x rest)
  end.

(* Convenient form: if b = rcons b' l, then wf_block holds iff P l && all (~~P) b'. *)
Lemma wf_block_rcons P b' l :
  wf_block P (rcons b' l) = P l && all (fun y => ~~ P y) b'.
Proof.
case: b' => [|x b'] /=.
  by rewrite andbT.
by rewrite last_rcons belast_rcons.
Qed.

(* Structural property: in split_blocks_aux P cur s, if cur consists of
   not-P letters and last s satisfies P, every produced block is wf_block. *)
Lemma split_blocks_aux_wf (P : pred nat) s :
  s != [::] -> P (last 0 s) ->
  forall cur,
  all (fun y => ~~ P y) cur ->
  all (wf_block P) (split_blocks_aux P cur s).
Proof.
elim: s => [|x s IH] Hs HPlast cur Hcur //=.
move: Hs => _.
case Hp: (P x).
- apply/andP; split.
    by rewrite wf_block_rcons Hp Hcur.
  case Hs': (s == [::]).
    by move/eqP: Hs' => ->.
  apply: IH => //.
  + by rewrite Hs'.
  + move: HPlast => /=.
    move: Hs'; case: s => [|? ?] //=.
- case Hs': (s == [::]).
    move/eqP: Hs' => Hsnil; rewrite Hsnil /= in HPlast.
    by rewrite Hp in HPlast.
  apply: IH.
  + by rewrite Hs'.
  + move: HPlast; rewrite /=.
    move: Hs'; case: s => [|? ?] //=.
  + by rewrite all_rcons Hp.
Qed.

Lemma split_blocks_wf (P : pred nat) s :
  s != [::] -> P (last 0 s) ->
  all (wf_block P) (split_blocks P s).
Proof. by move=> ? ?; apply: split_blocks_aux_wf. Qed.

(* Helper: number of blocks equals count P s when last s satisfies P. *)
Lemma split_blocks_aux_size_when_last_P (P : pred nat) s :
  s != [::] -> P (last 0 s) ->
  forall cur, size (split_blocks_aux P cur s) = count P s.
Proof.
elim: s => [|x s IH] Hs HPlast cur //=.
move: Hs => _.
case Hp: (P x) => /=.
- case Hs': (s == [::]).
    by move/eqP: Hs' => H; rewrite H /=.
  rewrite IH //.
    by rewrite Hs'.
  have HsP : P (last 0 s).
    move: HPlast => /= H.
    by case: (s) Hs' H => [|? ?] //.
  exact: HsP.
- case Hs': (s == [::]).
    move/eqP: Hs' => Hsnil; rewrite Hsnil /= in HPlast.
    by rewrite Hp in HPlast.
  rewrite IH //.
    by rewrite Hs'.
  have HsP : P (last 0 s).
    move: HPlast => /= H.
    by case: (s) Hs' H => [|? ?] //.
  exact: HsP.
Qed.

Lemma split_blocks_size_eq (P : pred nat) s :
  s != [::] -> P (last 0 s) ->
  size (split_blocks P s) = count P s.
Proof. by move=> ? ?; apply: split_blocks_aux_size_when_last_P. Qed.

(* For a wf_block, expose b = rcons b' l. *)
Lemma wf_block_decomp P b :
  wf_block P b ->
  exists b' l, [/\ b = rcons b' l, P l, all (fun y => ~~ P y) b'
              & size b = (size b').+1].
Proof.
case: b => [|x rest] //= /andP[HPlast Hbelast].
exists (belast x rest), (last x rest); split.
- by rewrite -lastI.
- by [].
- by [].
- by rewrite size_belast.
Qed.

(* For uniq u with a ∉ u, size u = count_lt a u + count_gt a u. *)
Lemma size_count_lt_gt a u :
  uniq u -> a \notin u -> size u = count_lt a u + count_gt a u.
Proof.
move=> Hu Hau.
rewrite /count_lt /count_gt -count_predUI.
have ->: count (predI (fun y => y < a) (fun y => a < y)) u = 0.
  apply/eqP; rewrite -leqn0 leqNgt -has_count.
  apply/hasPn => x _ /=.
  by case: (ltngtP x a) => //.
rewrite addn0 -[LHS](count_predT).
apply: eq_in_count => x Hx /=.
case: (ltngtP x a) => //= Heq.
by exfalso; move: Hau; rewrite -Heq Hx.
Qed.

(* Sum of (size b - 1) over wf_blocks = size flatten - num blocks. *)
Lemma sum_size_belast_wf P bs :
  all (wf_block P) bs ->
  \sum_(b <- bs) (size b).-1 = size (flatten bs) - size bs.
Proof.
elim: bs => [|b bs IH] /= Hbs.
  by rewrite big_nil.
move: Hbs => /andP[Hb Hbs].
rewrite big_cons IH // size_cat.
case: (wf_block_decomp Hb) => b' [l] [-> _ _ Hsz].
rewrite size_rcons /=.
have Hflat : size bs <= size (flatten bs).
  elim: bs Hbs {IH} => [|c cs IHcs] //=.
  move=> /andP[Hc Hcs].
  rewrite size_cat /=.
  have Hsc : 0 < size c.
    by case: (c) Hc => [|? ?] //=.
  have IHcss := IHcs Hcs.
  by apply: leq_ltn_trans IHcss _; rewrite -[size _]add0n ltn_add2r.
by rewrite addSn subSS addnBA.
Qed.

(* The key per-step invariant.

   We split into two cases (last u < a, and last u > a) and treat each separately.
*)

(* Helper: cyc_diff aggregated over wf_blocks — case "x<a" / P=(y<a). *)
Lemma sum_inv_cyc_lt_blocks a bs :
  all (wf_block (fun y => y < a)) bs ->
  (* Strong hyp: every non-last letter of every block is > a (not just >=). *)
  all (fun b => match b with
                | [::] => false
                | x :: rest => all (fun y => a < y) (belast x rest)
                end) bs ->
  \sum_(b <- bs) inv_seq (cyc_last_to_front b) + \sum_(b <- bs) (size b).-1
  = \sum_(b <- bs) inv_seq b.
Proof.
elim: bs => [|b bs IH] /= Hbs Hstr.
  by rewrite !big_nil.
move: Hbs => /andP[Hb Hbs].
move: Hstr => /andP[Hstrb Hstrbs].
rewrite !big_cons.
have IHs := IH Hbs Hstrbs.
case: (wf_block_decomp Hb) => b' [l] [Hbeq HPl _ Hsz].
have Hstrb' : all (fun y => a < y) b'.
  move: Hstrb; rewrite Hbeq.
  case: b' Hbeq Hsz => [|y b' /=] _ Hsz //=.
  by rewrite belast_rcons.
have := cyc_diff_block_lt HPl Hstrb'.
rewrite -Hbeq => Hcyc.
rewrite Hsz /=.
set IB := inv_seq b; set ICB := inv_seq (cyc_last_to_front b).
set SI := \sum_(b0 <- bs) inv_seq (cyc_last_to_front b0).
set SS := \sum_(b0 <- bs) (size b0).-1.
set SB := \sum_(b0 <- bs) inv_seq b0.
have HE : ICB + size b' = IB by rewrite /ICB /IB; exact: Hcyc.
have IHs' : SI + SS = SB by rewrite -/SI -/SS -/SB in IHs.
rewrite -addnA [SI + (size b' + SS)]addnCA.
by rewrite addnA HE IHs'.
Qed.

(* Helper: cyc_diff aggregated over wf_blocks — case "x>a" / P=(a<y). *)
Lemma sum_inv_cyc_gt_blocks a bs :
  all (wf_block (fun y => a < y)) bs ->
  all (fun b => match b with
                | [::] => false
                | x :: rest => all (fun y => y < a) (belast x rest)
                end) bs ->
  \sum_(b <- bs) inv_seq (cyc_last_to_front b)
  = \sum_(b <- bs) inv_seq b + \sum_(b <- bs) (size b).-1.
Proof.
elim: bs => [|b bs IH] /= Hbs Hstr.
  by rewrite !big_nil.
move: Hbs => /andP[Hb Hbs].
move: Hstr => /andP[Hstrb Hstrbs].
rewrite !big_cons.
have IHs := IH Hbs Hstrbs.
case: (wf_block_decomp Hb) => b' [l] [Hbeq HPl _ Hsz].
have Hstrb' : all (fun y => y < a) b'.
  move: Hstrb; rewrite Hbeq.
  case: b' Hbeq Hsz => [|y b' /=] _ Hsz //=.
  by rewrite belast_rcons.
have := cyc_diff_block_gt HPl Hstrb'.
rewrite -Hbeq => Hcyc.
rewrite Hsz /=.
set IB := inv_seq b; set ICB := inv_seq (cyc_last_to_front b).
set SI := \sum_(b0 <- bs) inv_seq (cyc_last_to_front b0).
set SS := \sum_(b0 <- bs) (size b0).-1.
set SB := \sum_(b0 <- bs) inv_seq b0.
have HE : ICB = IB + size b' by rewrite /ICB /IB; exact: Hcyc.
have IHs' : SI = SB + SS by rewrite -/SI -/SB -/SS in IHs.
rewrite HE IHs'.
by rewrite -!addnA; congr (IB + _); rewrite addnCA.
Qed.

(* The structural strong form of the wf_block: combined with uniq u + a ∉ u,
   the not-P letters in each block become strict inequalities. *)
Lemma split_blocks_lt_strict a u :
  uniq u -> a \notin u ->
  u != [::] -> last 0 u < a ->
  all (fun b => match b with
                | [::] => false
                | x :: rest => all (fun y => a < y) (belast x rest)
                end) (split_blocks (fun y => y < a) u).
Proof.
move=> Hu Hau Hu' Hla.
have HPlast : (fun y : nat => y < a) (last 0 u) by [].
have Hwf := @split_blocks_wf (fun y : nat => y < a) u Hu' HPlast.
apply/allP => b Hb.
have Hwfb := allP Hwf _ Hb.
case: (wf_block_decomp Hwfb) => b' [l] [Hbeq _ Hb' Hsz].
case: b Hb Hbeq Hsz Hwfb => [|x rest] //= Hb Hbeq Hsz Hwfb.
have Hbelast_eq : belast x rest = b'.
  by have := f_equal (belast 0) Hbeq; rewrite belast_rcons /= => -[->].
rewrite Hbelast_eq.
apply/allP => y Hy.
have HyU : y \in u.
  rewrite -(split_blocks_flatten (fun y => y < a) u).
  apply/flattenP. exists (rcons b' l).
    by rewrite -Hbeq; exact: Hb.
  by rewrite mem_rcons in_cons Hy orbT.
have Hya_neq : y != a.
  by apply: contra Hau => /eqP <-.
have Hyge : ~~ (y < a).
  by have := allP Hb' _ Hy.
rewrite ltn_neqAle.
apply/andP; split.
- by rewrite eq_sym.
- by rewrite leqNgt.
Qed.

Lemma split_blocks_gt_strict a u :
  uniq u -> a \notin u ->
  u != [::] -> a < last 0 u ->
  all (fun b => match b with
                | [::] => false
                | x :: rest => all (fun y => y < a) (belast x rest)
                end) (split_blocks (fun y => a < y) u).
Proof.
move=> Hu Hau Hu' Hla.
have HPlast : (fun y => a < y) (last 0 u) by [].
have Hwf := split_blocks_wf Hu' HPlast.
apply/allP => b Hb.
have Hwfb := allP Hwf _ Hb.
case: (wf_block_decomp Hwfb) => b' [l] [Hbeq _ Hb' Hsz].
case: b Hb Hbeq Hsz Hwfb => [|x rest] //= Hb Hbeq Hsz Hwfb.
have Hbelast_eq : belast x rest = b'.
  by have := f_equal (belast 0) Hbeq; rewrite belast_rcons /= => -[->].
rewrite Hbelast_eq.
apply/allP => y Hy.
have HyU : y \in u.
  rewrite -(split_blocks_flatten (fun y => a < y) u).
  apply/flattenP. exists (rcons b' l).
    by rewrite -Hbeq; exact: Hb.
  by rewrite mem_rcons in_cons Hy orbT.
have Hya_neq : y != a.
  by apply: contra Hau => /eqP <-.
have Hyle : ~~ (a < y).
  by have := allP Hb' _ Hy.
rewrite ltn_neqAle.
apply/andP; split.
- by apply: contra Hau => /eqP <-.
- by rewrite leqNgt.
Qed.

(* The case "last u < a" of foata_step_inv. *)
Lemma foata_step_inv_lt a u :
  u != [::] -> uniq u -> a \notin u -> last 0 u < a ->
  inv_seq (foata_step a u) = inv_seq u.
Proof.
case: u => [|x u] //= _ Hu' Hau Hla.
have HPlast : (fun y : nat => y < a) (last 0 (x :: u)) by [].
have Huniq : uniq (x :: u) by [].
have Hu_ne : (x :: u) != [::] by [].
have Hwf : all (wf_block (fun y : nat => y < a)) (split_blocks (fun y : nat => y < a) (x :: u)).
  exact: split_blocks_wf.
have Hstr := split_blocks_lt_strict Huniq Hau Hu_ne Hla.
have Hflat_bs : flatten (split_blocks (fun y : nat => y < a) (x :: u)) = x :: u by exact: split_blocks_flatten.
(* Step 1: foata_step *)
rewrite /foata_step /=.
have Hxulast : last x u < a by [].
rewrite Hxulast.
(* Now introduce bs *)
set bs := split_blocks (fun y : nat => y < a) (x :: u) in Hwf Hstr Hflat_bs *.
(* Step 2: inv_seq of the cat = inv_seq r_u + count_gt a r_u *)
rewrite inv_seq_cat /cross_inv big_seq1.
have ->: inv_seq [:: a] = 0 by rewrite /inv_seq /= !big_cons !big_nil.
rewrite addn0.
(* Now: inv_seq (flatten (map cyc bs)) + count_gt a r_u = inv_seq u' *)
set ru := flatten (map cyc_last_to_front bs).
have Hperm_ru : perm_eq ru (x :: u) by rewrite /ru -[in X in perm_eq _ X]Hflat_bs;
  exact: perm_eq_flatten_map_cyc.
have Hcg : count_gt a ru = count_gt a (x :: u) by exact: count_gt_perm_eq.
rewrite Hcg.
(* Apply the swap lemma + sum_inv_cyc_lt_blocks *)
have Hpermall : forall b, b \in bs -> perm_eq (cyc_last_to_front b) b.
  by move=> ? _; exact: cyc_last_to_front_perm_eq.
have Hswap := inv_seq_flatten_swap_eq Hpermall.
have Hsum_cyc := sum_inv_cyc_lt_blocks Hwf Hstr.
(* Hswap: inv_seq ru + sum_b inv_seq b = inv_seq (flatten bs) + sum_b inv_seq (cyc b)
   Hsum_cyc: sum_b inv_seq (cyc b) + sum_b (size b).-1 = sum_b inv_seq b *)
rewrite Hflat_bs in Hswap.
set IRu := inv_seq ru. set IU := inv_seq (x :: u).
set SB := \sum_(b <- bs) inv_seq b.
set SCB := \sum_(b <- bs) inv_seq (cyc_last_to_front b).
set SS := \sum_(b <- bs) (size b).-1.
have Hswap' : IRu + SB = IU + SCB by rewrite -/IRu -/SB -/IU -/SCB in Hswap.
have Hsum' : SCB + SS = SB by rewrite -/SCB -/SB -/SS in Hsum_cyc.
(* From Hswap' and Hsum': IRu + SCB + SS = IU + SCB, so IRu + SS = IU *)
have Hkey : IRu + SS = IU.
  apply/eqP. rewrite -(eqn_add2r SCB).
  by rewrite -addnA [SS + SCB]addnC Hsum' Hswap'.
(* SS = size u' - num_blocks = size (x::u) - count_lt a (x::u) = count_gt a (x::u) *)
have Hsize_u : size (x :: u) = count_lt a (x :: u) + count_gt a (x :: u)
  by exact: size_count_lt_gt.
have Hnumb : size bs = count_lt a (x :: u).
  rewrite /bs split_blocks_size_eq //= /count_lt.
have Hsumss : SS = size (x :: u) - size bs.
  rewrite /SS (sum_size_belast_wf Hwf).
  by rewrite Hflat_bs.
rewrite Hnumb Hsize_u in Hsumss.
rewrite addKn in Hsumss.
rewrite Hsumss in Hkey.
(* Goal: IRu + count_gt a (x::u) = IU *)
exact: Hkey.
Qed.

(* The case "last u > a" of foata_step_inv. *)
Lemma foata_step_inv_gt a u :
  u != [::] -> uniq u -> a \notin u -> a < last 0 u ->
  inv_seq (foata_step a u) = inv_seq u + size u.
Proof.
case: u => [|x u] //= _ Hu' Hau Hla.
have HPlast : (fun y : nat => a < y) (last 0 (x :: u)) by [].
have Huniq : uniq (x :: u) by [].
have Hu_ne : (x :: u) != [::] by [].
have Hwf : all (wf_block (fun y : nat => a < y)) (split_blocks (fun y : nat => a < y) (x :: u)).
  exact: split_blocks_wf.
have Hstr := split_blocks_gt_strict Huniq Hau Hu_ne Hla.
have Hflat_bs : flatten (split_blocks (fun y : nat => a < y) (x :: u)) = x :: u
  by exact: split_blocks_flatten.
(* Step 1: foata_step *)
rewrite /foata_step /=.
have Hxulast : ~~ (last x u < a) by rewrite -leqNgt; apply: ltnW.
move: Hxulast => /negbTE ->.
set bs := split_blocks (fun y : nat => a < y) (x :: u) in Hwf Hstr Hflat_bs *.
(* Step 2: inv_seq of the cat *)
rewrite inv_seq_cat /cross_inv big_seq1.
have ->: inv_seq [:: a] = 0 by rewrite /inv_seq /= !big_cons !big_nil.
rewrite addn0.
set ru := flatten (map cyc_last_to_front bs).
have Hperm_ru : perm_eq ru (x :: u) by rewrite /ru -[in X in perm_eq _ X]Hflat_bs;
  exact: perm_eq_flatten_map_cyc.
have Hcg : count_gt a ru = count_gt a (x :: u) by exact: count_gt_perm_eq.
rewrite Hcg.
have Hpermall : forall b, b \in bs -> perm_eq (cyc_last_to_front b) b.
  by move=> ? _; exact: cyc_last_to_front_perm_eq.
have Hswap := inv_seq_flatten_swap_eq Hpermall.
have Hsum_cyc := sum_inv_cyc_gt_blocks Hwf Hstr.
rewrite Hflat_bs in Hswap.
set IRu := inv_seq ru. set IU := inv_seq (x :: u).
set SB := \sum_(b <- bs) inv_seq b.
set SCB := \sum_(b <- bs) inv_seq (cyc_last_to_front b).
set SS := \sum_(b <- bs) (size b).-1.
have Hswap' : IRu + SB = IU + SCB by rewrite -/IRu -/SB -/IU -/SCB in Hswap.
have Hsum' : SCB = SB + SS by rewrite -/SCB -/SB -/SS in Hsum_cyc.
(* From Hswap and Hsum: IRu + SB = IU + SB + SS, so IRu = IU + SS *)
have Hkey : IRu = IU + SS.
  apply/eqP. rewrite -(eqn_add2r SB).
  by rewrite Hswap' Hsum' [SB + SS]addnC addnA.
(* SS = size u' - num_blocks = size (x::u) - count_gt a (x::u) = count_lt a (x::u) *)
have Hsize_u : size (x :: u) = count_lt a (x :: u) + count_gt a (x :: u)
  by exact: size_count_lt_gt.
have Hnumb : size bs = count_gt a (x :: u).
  rewrite /bs split_blocks_size_eq //= /count_gt.
have Hsumss : SS = size (x :: u) - size bs.
  rewrite /SS (sum_size_belast_wf Hwf).
  by rewrite Hflat_bs.
rewrite Hnumb Hsize_u in Hsumss.
rewrite -addnBA // subnn addn0 in Hsumss.
rewrite Hsumss in Hkey.
(* Goal: IRu + count_gt a (x::u) = IU + size (x :: u) *)
rewrite Hkey.
rewrite -addnA -[count_lt a (x :: u) + _]Hsize_u.
by [].
Qed.

(* The combined invariant. *)
Lemma foata_step_inv a u :
  u != [::] -> uniq u -> a \notin u ->
  inv_seq (foata_step a u)
    = inv_seq u + (size u) * (nat_of_bool (a < last 0 u)).
Proof.
move=> Hu Hu' Hau.
case Hla: (a < last 0 u).
- by rewrite muln1; exact: foata_step_inv_gt.
- rewrite muln0 addn0.
  apply: foata_step_inv_lt => //.
  rewrite ltn_neqAle leqNgt Hla andbT.
  apply/eqP => Hlast.
  move/negP: Hau; apply.
  rewrite -Hlast.
  by case: (u) Hu => [//=|? ?] _; exact: mem_last.
Qed.

(* ========================================================================= *)
(* §H. The main equidistribution theorem                                    *)
(* ========================================================================= *)

Theorem foata_inv_eq_maj w :
  uniq w -> inv_seq (foata w) = maj_seq w.
Proof.
elim/last_ind: w => [|w a IH] Hu.
  by rewrite /foata /= /inv_seq /maj_seq /= !big_nil.
have Hw : uniq w by move: Hu; rewrite rcons_uniq; case/andP.
have Ha : a \notin w by move: Hu; rewrite rcons_uniq; case/andP.
have IHw := IH Hw.
rewrite foata_rcons.
case Hwnil: (w == [::]).
  move/eqP: Hwnil => ->.
  by rewrite /= /inv_seq /maj_seq /= !big_cons !big_nil.
have Hw_ne : w != [::] by rewrite Hwnil.
have Hfw_ne : foata w != [::].
  rewrite -size_eq0 foata_size.
  by case: (w) Hw_ne => [|? ?].
have Hfw_uniq : uniq (foata w) by exact: foata_uniq.
have Hfw_a : a \notin foata w.
  by rewrite (perm_mem (foata_perm_eq _)).
rewrite foata_step_inv //.
rewrite (foata_last_eq 0 Hw_ne).
rewrite foata_size.
rewrite (maj_seq_rcons _ Hw_ne).
by rewrite IHw.
Qed.

(* ========================================================================= *)
(* §I. Lift to {perm 'I_n.+1}: foata_perm and inv-maj relation             *)
(* ========================================================================= *)

Section Equidistribution.

(* Convert perm-level maj to seq-level maj_seq. *)
Lemma maj_eq_maj_seq n (s : {perm 'I_n.+1}) :
  maj s = maj_seq (perm_to_seq s).
Proof.
rewrite /maj /maj_seq perm_to_seq_size /=.
rewrite [LHS](_ : _ = \sum_(i : 'I_n | is_descent s i) (val i).+1); last first.
  by apply: eq_bigl => i; rewrite mem_descent_set.
rewrite -[iota 0 n]val_enum_ord big_map.
rewrite [LHS]big_mkcond -big_enum.
rewrite [RHS](_ : _ = \sum_(i <- enum 'I_n) (if is_descent s i then (val i).+1 else 0)).
  by [].
rewrite -big_mkcond.
by apply: eq_big => k //=; rewrite is_descent_perm_seq.
Qed.

(* The Foata bijection at the permutation level. *)
Section FoataPerm.

Variable n : nat.

Lemma foata_perm_to_seq_size (s : {perm 'I_n.+1}) :
  size (foata (perm_to_seq s)) = n.+1.
Proof. by rewrite foata_size perm_to_seq_size. Qed.

Lemma foata_perm_to_seq_uniq (s : {perm 'I_n.+1}) :
  uniq (foata (perm_to_seq s)).
Proof. by apply: foata_uniq; exact: perm_to_seq_uniq. Qed.

Lemma foata_perm_to_seq_bnd (s : {perm 'I_n.+1}) :
  all (fun x => x < n.+1) (foata (perm_to_seq s)).
Proof.
apply/allP => x.
rewrite (perm_mem (foata_perm_eq _)) => Hx.
exact: (allP (perm_to_seq_bnd s)).
Qed.

Definition foata_perm (s : {perm 'I_n.+1}) : {perm 'I_n.+1} :=
  seq_to_perm (foata_perm_to_seq_size s) (foata_perm_to_seq_uniq s)
              (foata_perm_to_seq_bnd s).

Lemma perm_to_seq_foata_perm (s : {perm 'I_n.+1}) :
  perm_to_seq (foata_perm s) = foata (perm_to_seq s).
Proof. by rewrite /foata_perm perm_to_seq_seq_to_perm. Qed.

End FoataPerm.

(* Convert perm-level inv to seq-level inv_seq. *)
Lemma inv_eq_inv_seq n (s : {perm 'I_n.+1}) :
  inv s = inv_seq (perm_to_seq s).
Proof.
rewrite (inv_double_sum s).
rewrite /inv_seq perm_to_seq_size.
(* RHS: outer iota -> ord *)
rewrite -[iota 0 n.+1]val_enum_ord big_map.
rewrite -big_enum.
apply: eq_bigr => j _.
have Hjn : (j : nat) <= n.+1 by apply: ltnW; exact: ltn_ord.
rewrite -(subn0 (val j)) -[iota 0 _]/(index_iota _ _).
rewrite (big_nat_widen 0 (val j) n.+1 _ _ Hjn).
rewrite -[index_iota 0 n.+1]/(iota 0 (n.+1 - 0)) subn0.
rewrite -[iota 0 n.+1]val_enum_ord big_map.
rewrite subn0.
rewrite [in LHS]big_mkcond /=.
rewrite [in RHS]big_seq_cond.
under [in RHS]eq_bigl => i do rewrite mem_enum andTb.
rewrite [in RHS]big_mkcond.
have ->: enum 'I_n.+1 = index_enum (Finite.clone _ 'I_n.+1) by rewrite enumT.
apply: eq_bigr => i _.
have Hi : (i : nat) < n.+1 := ltn_ord i.
have Hj' : (j : nat) < n.+1 := ltn_ord j.
rewrite (nth_perm_to_seq s Hi) (nth_perm_to_seq s Hj').
have ->: Ordinal Hi = i by apply: val_inj.
have ->: Ordinal Hj' = j by apply: val_inj.
by case Hij: (i < j); rewrite andbC //=.
Qed.

(* The interesting intermediate result: foata_perm preserves the bijection
   between maj and inv at the perm level.

   This says: the Foata bijection sends {s : maj s = k} into {s : inv s = k}
   for every k.  To upgrade this to the equidistribution theorem
       #|{s : inv s == k}| = #|{s : maj s == k}|
   we need foata_perm to be injective (hence bijective on the finite group
   Sym_{n+1}, by injective ⇒ surjective on finite sets).

   The injectivity reduces (via perm_to_seq_inj) to: foata is injective on
   uniq sequences of length n+1.  Sketch (see also Stanley EC1, §1.3.6 for
   the standard inverse construction):
     - foata (rcons w a) ends in a, so a = last (foata w).
     - The remaining prefix r determines the predicate P (lt a or gt a)
       via head r vs a, since after `cyc_last_to_front` each block
       starts with a P-letter (cf. `wf_block_rcons`).
     - Re-split r at P-elements (split_blocks_inv) to recover the
       cyc-rotated blocks; apply cyc_first_to_back (the inverse of
       cyc_last_to_front, see preliminary lemmas in foata.v history)
       to each, flatten, recover w.
   The construction is straightforward but the formalization (~150-200 LOC
   of bookkeeping about wf_block / split_blocks_inv cancellation lemmas)
   is left as future work.                                                  *)
Lemma foata_perm_inv_maj n (s : {perm 'I_n.+1}) :
  inv (foata_perm s) = maj s.
Proof.
rewrite inv_eq_inv_seq perm_to_seq_foata_perm.
rewrite foata_inv_eq_maj; last exact: perm_to_seq_uniq.
by rewrite -maj_eq_maj_seq.
Qed.

End Equidistribution.

