(* Inversions and the major index.
   Stanley EC1 §1.3.3.

   Sister file to descent.v: where descent.v counts adjacent pairs that
   "go down", inv counts all pairs that go down (not just adjacent).
   The major index maj(s) is the sum of (1-indexed) descent positions;
   together inv and maj are the two classical "Mahonian" statistics
   that are equidistributed over S_n (proved in foata.v).
*)
From mathcomp Require Import all_ssreflect fingroup perm binomial.
From mathcomp_eulerian Require Import ordinal_reindex perm_compress descent.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* ========================================================================= *)
(* §A. The inversion statistic                                               *)
(* ========================================================================= *)

Section Inversions.
Variable n : nat.
Implicit Types (s : {perm 'I_n.+1}).

(** [is_inv s i j] holds when the pair [(i, j)] is an inversion of [s],
    i.e. [i < j] but [s i > s j].  Stanley EC1 §1.3.3. *)
Definition is_inv s (i j : 'I_n.+1) : bool :=
  (i < j) && (s j < s i).

(** [inv_set s] is the set of inversions of [s]: pairs [(i, j)] with
    [i < j] but [s i > s j]. *)
Definition inv_set s : {set 'I_n.+1 * 'I_n.+1} :=
  [set ij | is_inv s ij.1 ij.2].

(** [inv s] is the inversion count of [s], i.e. [#|inv_set s|].
    Stanley's [inv(w)]. *)
Definition inv s : nat := #|inv_set s|.

(** Membership in [inv_set s] reduces to [is_inv s i j]. *)
Lemma mem_inv_set s i j :
  ((i, j) \in inv_set s) = is_inv s i j.
Proof. by rewrite inE. Qed.

(** The identity permutation has no inversions: [inv 1 = 0]. *)
Lemma inv_id : inv (1 : {perm 'I_n.+1}) = 0.
Proof.
apply/eqP; rewrite /inv cards_eq0; apply/eqP/setP=> [[i j]].
by rewrite !inE /is_inv !perm1 ltnNge leq_eqVlt orbC; case: ltngtP.
Qed.

(** Bridge lemma: [inv s] expressed as the nested double-sum
    [\sum_j \sum_(i < j) (s j < s i)].  Bridges the [inv_set]
    cardinality form to the seq-level double-sum form of [inv_seq],
    used in [foata.v] to prove [inv_eq_inv_seq]. *)
Lemma inv_double_sum s :
  inv s = \sum_(j : 'I_n.+1) \sum_(i : 'I_n.+1 | i < j) (s j < s i).
Proof.
rewrite /inv /inv_set.
rewrite -sum1dep_card.
rewrite (partition_big snd predT) //=.
apply: eq_bigr => j _.
rewrite (reindex (fun i : 'I_n.+1 => (i, j))) /=; last first.
  exists (@fst _ _) => x; first by [].
  rewrite inE => /andP[_ /eqP Hx2].
  by case: x Hx2 => a b /= ->.
under [in LHS]eq_bigl => i do rewrite eqxx andbT /is_inv.
rewrite [in RHS]big_mkcond [in LHS]big_mkcond /=.
apply: eq_bigr => i _.
by case Hij: (i < j); rewrite //=; case: (s j < s i).
Qed.

End Inversions.

(* ========================================================================= *)
(* §B. The major index                                                       *)
(* ========================================================================= *)

Section MajorIndex.
Variable n : nat.
Implicit Types (s : {perm 'I_n.+1}).

(** [maj s] is the major index: the sum of the (1-indexed) descent
    positions of [s].  Stanley EC1 §1.3.3.  Our [descent_set s] is
    0-indexed in ['I_n]; we shift by 1 to recover Stanley's
    1-indexed positions in [{1, ..., n}]. *)
Definition maj s : nat := \sum_(i in descent_set s) (val i).+1.

(** The identity permutation has zero major index: [maj 1 = 0]. *)
Lemma maj_id : maj (1 : {perm 'I_n.+1}) = 0.
Proof.
rewrite /maj big_pred0 // => i.
rewrite mem_descent_set /is_descent !perm1.
by apply/negbTE; rewrite -leqNgt /= /bump leq0n add1n.
Qed.

End MajorIndex.

(* ========================================================================= *)
(* §C. Cardinality lemma: pairs (i,j) with i < j in 'I_m * 'I_m number      *)
(* 'C(m, 2)                                                                  *)
(* ========================================================================= *)

(** The number of strictly-ordered pairs in ['I_m * 'I_m] is the binomial
    coefficient ['C(m, 2)].  Used to bound [inv] and [maj]. *)
Lemma card_ord_pair m :
  #|[set ij : 'I_m * 'I_m | ij.1 < ij.2]| = 'C(m, 2).
Proof.
rewrite -sum1dep_card.
rewrite (eq_bigl (fun p : 'I_m * 'I_m => xpredT p.1 && (p.1 < p.2))) //.
rewrite -(pair_big_dep xpredT (fun i j : 'I_m => i < j) (fun _ _ => 1)) /=.
rewrite (eq_bigr (fun i : 'I_m => m - i.+1)); last first.
{ move=> i _.
  rewrite -(big_mkord (fun j => i < j) (fun _ => 1)).
  have Hi1m : i.+1 <= m := ltn_ord i.
  rewrite (big_cat_nat (n := i.+1) (leq0n _) Hi1m) /=.
  rewrite [X in X + _]big1_seq; last first.
    move=> j /andP[Hij].
    rewrite mem_index_iota => /andP[_ Hji1].
    by move: Hji1 Hij; rewrite ltnNge => /negbTE ->.
  rewrite add0n.
  rewrite big_nat_cond.
  rewrite (eq_bigl (fun k => (i.+1 <= k < m) && true)); last first.
    by move=> k; case: (boolP (i.+1 <= k < m)) => //= /andP[Hk1 _]; rewrite Hk1.
  rewrite -big_nat_cond.
  by rewrite big_const_nat iter_addn_0 mul1n.
}
rewrite -bin2_sum big_mkord.
rewrite (reindex_inj rev_ord_inj) /=.
apply: eq_bigr => i _.
rewrite subnSK; last by exact: ltn_ord.
by rewrite subKn // ltnW.
Qed.

(* ========================================================================= *)
(* §D. Bounds and reversal-symmetry for inv and maj                          *)
(* ========================================================================= *)

Section InvMajBoundsRev.
Variable n : nat.
Implicit Types (s : {perm 'I_n.+1}).

(* ----- D.1 The bound inv s <= 'C(n+1, 2) ----- *)

(** Bound: [inv s <= 'C(n+1, 2)] for [s : {perm 'I_n.+1}], since
    inversions are a subset of all strictly-ordered pairs. *)
Lemma inv_le s : inv s <= 'C(n.+1, 2).
Proof.
rewrite /inv -(card_ord_pair n.+1).
apply: subset_leq_card.
apply/subsetP => [[i j]]; rewrite !inE /is_inv.
by case/andP=> ->.
Qed.

(* ----- D.2 Helper: full sum of (val i + 1) over 'I_n equals 'C(n+1, 2) ----- *)

(** Helper: [\sum_(i : 'I_n) (val i).+1 = 'C(n+1, 2)].  Used to bound
    [maj]. *)
Lemma sum_succ_ord_eq_bin2 :
  \sum_(i : 'I_n) (val i).+1 = 'C(n.+1, 2).
Proof.
rewrite -bin2_sum big_mkord.
rewrite [in RHS](_ : n.+1 = 1 + n); last by rewrite addnC addn1.
rewrite big_split_ord /=.
rewrite big_ord_recl big_ord0 addn0 add0n.
by apply: eq_bigr => i _.
Qed.

(* ----- D.3 The bound maj s <= 'C(n+1, 2) ----- *)

(** Bound: [maj s <= 'C(n+1, 2)] for [s : {perm 'I_n.+1}], by comparing
    descent-position sum to the full sum of [(val i).+1] over ['I_n]. *)
Lemma maj_le s : maj s <= 'C(n.+1, 2).
Proof.
rewrite /maj -sum_succ_ord_eq_bin2.
rewrite [X in _ <= X](bigID (mem (descent_set s))) /=.
exact: leq_addr.
Qed.

(* ----- D.4 Co-inversion set: pairs (i,j) with i<j and s i < s j ----- *)

(** [coinv_set s] is the co-inversion set of [s]: pairs [(i, j)] with
    [i < j] and [s i < s j].  Since [s] is a permutation, every
    strictly-ordered pair is either an inversion or a co-inversion. *)
Definition coinv_set s : {set 'I_n.+1 * 'I_n.+1} :=
  [set ij : 'I_n.+1 * 'I_n.+1 | (ij.1 < ij.2) && (s ij.1 < s ij.2)].

(** Order-reversal property of [rev_ord]: [rev_ord a < rev_ord b] iff
    [b < a].  Used in the [inv] reversal identity. *)
Lemma rev_ord_lt (a b : 'I_n.+1) : (rev_ord a < rev_ord b) = (b < a).
Proof.
have Ha : a < n.+1 := ltn_ord a.
rewrite /=.
by rewrite ltn_sub2lE.
Qed.

(** Split: every strictly-ordered pair is either an inversion or a
    co-inversion, so [inv s + #|coinv_set s| = 'C(n+1, 2)]. *)
Lemma card_split_ord_pair s :
  inv s + #|coinv_set s| = 'C(n.+1, 2).
Proof.
rewrite /inv -card_ord_pair.
rewrite -(cardsID (inv_set s) [set ij : 'I_n.+1 * 'I_n.+1 | ij.1 < ij.2]).
congr (_ + _).
- apply: eq_card => [[i j]]; rewrite !inE /is_inv /=.
  by case Hij: (i < j) => //=; rewrite andbF.
- rewrite /coinv_set; apply: eq_card => [[i j]]; rewrite !inE /is_inv /=.
  case Hij: (i < j); last by rewrite andbF /=.
  rewrite /= !andbT.
  case: (ltngtP (s i) (s j)) => H //.
  have /perm_inj Eij : s i = s j by apply: val_inj.
  by move: Hij; rewrite Eij ltnn.
Qed.

(* ----- D.5 inv (rev_perm s) bijects with coinv_set s ----- *)

(** The inversions of [rev_perm s] are in bijection with the
    co-inversions of [s] via [(i, j) |-> (rev_ord j, rev_ord i)]. *)
Lemma inv_rev_perm_eq_coinv s :
  inv (rev_perm s) = #|coinv_set s|.
Proof.
rewrite /inv /coinv_set /inv_set.
pose phi := fun ij : 'I_n.+1 * 'I_n.+1 => (rev_ord ij.2, rev_ord ij.1).
have phi_invol : involutive phi.
  by move=> [a b]; rewrite /phi /= !rev_ordK.
have phi_inj : injective phi := can_inj phi_invol.
rewrite -[in RHS](card_imset _ phi_inj).
apply: eq_card => [[i j]]; rewrite !inE /is_inv /=.
apply/idP/imsetP.
- case/andP=> Hij Hsji.
  exists (rev_ord j, rev_ord i); last by rewrite /phi /= !rev_ordK.
  rewrite inE /= rev_ord_lt Hij /=.
  by rewrite !rev_permE in Hsji.
- case=> [[a b]]; rewrite inE /= => /andP[Hab Hsab] [-> ->].
  rewrite rev_ord_lt Hab /=.
  by rewrite !rev_permE !rev_ordK.
Qed.

(* ----- D.6 The reversal identity for inv ----- *)

(** Reversal identity for [inv]: [inv (rev_perm s) = 'C(n+1, 2) - inv s].
    Stanley EC1 §1.3.3. *)
Lemma inv_rev_perm s :
  inv (rev_perm s) = 'C(n.+1, 2) - inv s.
Proof.
rewrite inv_rev_perm_eq_coinv.
have H := card_split_ord_pair s.
by rewrite -H addKn.
Qed.

(* ----- D.7 Reversal identity for maj.

   Note: the naive identity `maj (rev_perm s) = 'C(n+1, 2) - maj s` is
   FALSE in general (counterexample: s = [0;2;1] in S_3 has maj 2, and
   rev_perm s = [1;2;0] also has maj 2, but 'C(3,2) - 2 = 1).

   The correct classical identity (Stanley EC1, derivation: descent_set
   of rev_perm sits at the rev_ord-image of the *complement*, so the
   "1-indexed position" sum picks up an offset of n+1 per descent of s):
                                                                          *)
(** Reversal identity for [maj]:
    [maj (rev_perm s) + (n+1) * des s = 'C(n+1, 2) + maj s].
    The naive [maj (rev_perm s) = 'C(n+1, 2) - maj s] is FALSE; the
    correct identity carries a [(n+1) * des s] offset (Stanley EC1). *)
Lemma maj_rev_perm s :
  maj (rev_perm s) + (n.+1) * des s = 'C(n.+1, 2) + maj s.
Proof.
have descent_set_rev_perm :
  descent_set (rev_perm s) = [set rev_ord i | i in ~: descent_set s].
  apply/setP => j; rewrite !inE.
  apply/idP/imsetP.
  - rewrite is_descent_rev => Hnd.
    exists (rev_ord j); last by rewrite rev_ordK.
    by rewrite !inE.
  - case=> x; rewrite !inE => Hnd ->.
    by rewrite is_descent_rev rev_ordK.
rewrite /maj /des descent_set_rev_perm.
rewrite big_imset; last by move=> x y _ _; apply: (can_inj (@rev_ordK _)).
rewrite (eq_bigr (fun i : 'I_n => n - val i)); last first.
  by move=> i _ /=; rewrite subnSK //; exact: ltn_ord.
have Hsum_complete : \sum_(i in ~: descent_set s) (n - val i)
                   + \sum_(i in descent_set s) (n - val i)
                   = \sum_(i : 'I_n) (n - val i).
  rewrite [in RHS](bigID (mem (descent_set s))) /=.
  by rewrite addnC; congr (_ + _); apply: eq_bigl => i; rewrite !inE.
have HD : \sum_(i in descent_set s) (n - val i)
        + \sum_(i in descent_set s) (val i).+1
        = (n.+1) * #|descent_set s|.
  rewrite -big_split /=.
  rewrite (eq_bigr (fun _ => n.+1)); last first.
    move=> i _.
    have Him : i < n := ltn_ord i.
    by rewrite addnS subnK // ltnW.
  by rewrite sum_nat_const mulnC.
have HsumNat : \sum_(i : 'I_n) (n - val i) = 'C(n.+1, 2).
  rewrite -sum_succ_ord_eq_bin2.
  rewrite (reindex_inj rev_ord_inj) /=.
  apply: eq_bigr => i _.
  by rewrite /= subKn // ltnW // ltn_ord.
rewrite -HsumNat -Hsum_complete.
rewrite -addnA.
congr (_ + _).
by rewrite -HD.
Qed.

End InvMajBoundsRev.
