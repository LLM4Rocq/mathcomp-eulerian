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

(* Position pair (i, j) is an inversion of s when i < j but s i > s j. *)
Definition is_inv s (i j : 'I_n.+1) : bool :=
  (i < j) && (s j < s i).

(* The inversion set: pairs (i, j) such that s makes them out-of-order. *)
Definition inv_set s : {set 'I_n.+1 * 'I_n.+1} :=
  [set ij | is_inv s ij.1 ij.2].

(* The inversion count.  Stanley writes inv(w). *)
Definition inv s : nat := #|inv_set s|.

Lemma mem_inv_set s i j :
  ((i, j) \in inv_set s) = is_inv s i j.
Proof. by rewrite inE. Qed.

(* The identity permutation has no inversions. *)
Lemma inv_id : inv (1 : {perm 'I_n.+1}) = 0.
Proof.
apply/eqP; rewrite /inv cards_eq0; apply/eqP/setP=> [[i j]].
by rewrite !inE /is_inv !perm1 ltnNge leq_eqVlt orbC; case: ltngtP.
Qed.

End Inversions.

(* ========================================================================= *)
(* §B. The major index                                                       *)
(* ========================================================================= *)

Section MajorIndex.
Variable n : nat.
Implicit Types (s : {perm 'I_n.+1}).

(* maj(s) = sum of (1-indexed) descent positions.  Stanley §1.3.3.
   Our descent_set s : {set 'I_n} is 0-indexed; (val i).+1 maps to
   Stanley's 1-indexed positions in {1, ..., n}.                           *)
Definition maj s : nat := \sum_(i in descent_set s) (val i).+1.

Lemma maj_id : maj (1 : {perm 'I_n.+1}) = 0.
Proof.
rewrite /maj big_pred0 // => i.
rewrite mem_descent_set /is_descent !perm1.
by apply/negbTE; rewrite -leqNgt /= /bump leq0n add1n.
Qed.

End MajorIndex.
