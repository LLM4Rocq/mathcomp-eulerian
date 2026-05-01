(* Cycles and Stirling cycle numbers.
   Stanley EC1 §1.3.1 (cycle representation) and §1.3.2 (Stirling numbers
   of the first kind, also called signless Stirling cycle numbers c(n,k)).

   Builds on mathcomp's [porbit] / [porbits] machinery in
   mathcomp/algebra/perm.v.  Sister file to [eulerian.v]: where eulerian.v
   refines permutations by descent count, this file refines them by cycle
   count.
*)
From mathcomp Require Import all_ssreflect fingroup perm.
From mathcomp_eulerian Require Import ordinal_reindex perm_compress descent.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* ========================================================================= *)
(* §A. Cycle count                                                           *)
(* ========================================================================= *)

(* cycle_count s = number of cycles in the disjoint-cycle decomposition
   of [s].  In mathcomp this is the cardinality of [porbits s], the set
   of orbits of [s] acting on [T] by iteration.                            *)
Definition cycle_count {T : finType} (s : {perm T}) : nat := #|porbits s|.

(* ========================================================================= *)
(* §B. Stirling cycle numbers                                                *)
(* ========================================================================= *)

(* stirling_c n k = number of permutations of [0, ..., n-1] with exactly
   k cycles in their disjoint-cycle decomposition.  Stanley writes
   [c(n, k)] (signless Stirling numbers of the first kind).               *)
Definition stirling_c (n k : nat) : nat :=
  #|[set s : {perm 'I_n} | cycle_count s == k]|.

(* ========================================================================= *)
(* §C. Basic identities                                                      *)
(* ========================================================================= *)

Section CycleBasic.

(* Each cycle is non-empty, so [cycle_count s <= |T|].  This is the cycle
   analogue of [des_le] for descents.                                      *)
Lemma cycle_count_le {T : finType} (s : {perm T}) :
  cycle_count s <= #|T|.
Proof.
rewrite /cycle_count /porbits.
exact: leq_imset_card.
Qed.

(* The identity permutation has exactly [|T|] cycles — one singleton per
   element.  Stanley §1.3.1 (a fixed point is a 1-cycle).                 *)
(* For the identity, every porbit is a singleton {x}.  We prove this
   pointwise and then count.                                              *)
Lemma porbit_id_singleton (T : finType) (x : T) :
  porbit (1 : {perm T}) x = [set x].
Proof.
apply/setP=> y; rewrite !inE.
apply/porbitP/eqP.
- by case=> i ->; rewrite expg1n perm1.
- by move=> ->; exists 0; rewrite expg1n perm1.
Qed.

Lemma cycle_count_id (T : finType) :
  cycle_count (1 : {perm T}) = #|T|.
Proof.
rewrite /cycle_count /porbits.
rewrite -[in RHS](card_imset [pred x : T | true] set1_inj).
apply: eq_card => P; apply/imsetP/imsetP.
- case=> x _ ->.
  by exists x; rewrite ?inE //; rewrite porbit_id_singleton.
- case=> x _ ->.
  by exists x => //; rewrite porbit_id_singleton.
Qed.

End CycleBasic.

(* ========================================================================= *)
(* §D. Row sum: sum over cycle counts recovers n!                            *)
(* ========================================================================= *)

(* The cycle-count statistic partitions {perm 'I_n} just as the descent
   count does, so summing stirling_c over all cycle counts recovers the
   total permutation count.  Mirrors [eulerian_row_sum] in eulerian.v.   *)

Lemma stirling_c_row_sum n :
  \sum_(k < n.+1) stirling_c n k = #|{perm 'I_n}|.
Proof.
rewrite /stirling_c -sum1_card.
rewrite (partition_big (fun s : {perm 'I_n} => inord (cycle_count s) : 'I_n.+1)
                       xpredT) //=.
apply: eq_bigr => k _; rewrite -sum1_card; apply: eq_bigl => s; rewrite inE.
rewrite -val_eqE /= inordK //.
have := cycle_count_le s.
by rewrite card_ord.
Qed.

Lemma stirling_c_row_sum_fact n :
  \sum_(k < n.+1) stirling_c n k = n`!.
Proof. by rewrite stirling_c_row_sum card_Sn. Qed.
