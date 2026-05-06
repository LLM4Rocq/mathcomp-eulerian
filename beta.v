(* Layer 4: set-refined descent counts (beta-numbers).                       *)
(*                                                                           *)
(* beta n D counts permutations of 'I_n.+1 whose descent_set equals D.       *)
(* Summing beta D over all D of a given cardinality k recovers the classical *)
(* Eulerian number. This file provides basic lemmas used by beta_swap.v and   *)
(* (ultimately) Putnam 2025 A5.                                              *)

From mathcomp Require Import all_ssreflect fingroup perm.
From mathcomp_eulerian Require Import ordinal_reindex perm_compress descent eulerian.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* ========================================================================= *)
(* Set-refined descent count                                                 *)
(* ========================================================================= *)

(** [beta n D] is the set-refined descent count: the number of permutations of
    ['I_n.+1] whose descent set equals exactly [D]. Stanley's [beta_n(D)]
    (Stanley EC1, S1.4); summing [beta D] over [|D| = k] recovers [eulerian n k]. *)
Definition beta (n : nat) (D : {set 'I_n}) : nat :=
  #|[set sigma : {perm 'I_n.+1} | descent_set sigma == D]|.

(* ========================================================================= *)
(* Auxiliary: descent_set of rev_perm                                        *)
(* ========================================================================= *)

(** Descent set of the reversal: [D(rev_perm s)] is the [rev_ord]-image of the
    complement of [D(s)]. Set-level refinement of [is_descent_rev]. *)
Lemma descent_set_rev_perm n (s : {perm 'I_n.+1}) :
  descent_set (rev_perm s) = [set rev_ord i | i in ~: descent_set s].
Proof.
apply/setP => j; rewrite !inE.
apply/idP/imsetP.
- rewrite is_descent_rev => Hnd.
  exists (rev_ord j); last by rewrite rev_ordK.
  by rewrite !inE.
- case=> x; rewrite !inE => Hnd ->.
  by rewrite is_descent_rev rev_ordK.
Qed.

(** The reversal permutation [n,n-1,...,0] has descent set equal to all positions. *)
Lemma descent_set_rev_perm_ord n :
  descent_set (rev_perm_ord n) = [set: 'I_n].
Proof.
apply/setP => i; rewrite !inE.
rewrite /is_descent !rev_perm_ordE /= /bump /= add1n.
by rewrite !subSS ltn_sub2l // ltnS ltn_ord.
Qed.

(* ========================================================================= *)
(* Image under rev_ord: involutivity and complement                          *)
(* ========================================================================= *)

(** [rev_ord] is involutive on subsets: applying [imset rev_ord] twice is the identity. *)
Lemma imset_rev_ord_inv n (D : {set 'I_n}) :
  [set rev_ord i | i in [set rev_ord i | i in D]] = D.
Proof.
apply/setP => x; apply/imsetP/idP.
- by case=> y /imsetP[z Hz ->] ->; rewrite rev_ordK.
- by move=> Hx; exists (rev_ord x); rewrite ?rev_ordK //; apply/imsetP; exists x.
Qed.

(** [rev_ord]-image commutes with set complement. *)
Lemma imset_rev_ord_compl n (D : {set 'I_n}) :
  [set rev_ord i | i in ~: D] = ~: [set rev_ord i | i in D].
Proof.
apply/setP => x; rewrite inE; apply/imsetP/idP.
- case=> y; rewrite inE => HyND ->.
  apply/negP => /imsetP[z Hz Hrev].
  have Eyz : y = z by apply: (can_inj (@rev_ordK _)); apply/val_inj/(congr1 val Hrev).
  by rewrite Eyz Hz in HyND.
- move=> HnD; exists (rev_ord x); rewrite ?rev_ordK //.
  by rewrite inE; apply: contra HnD => Hx; apply/imsetP; exists (rev_ord x); rewrite ?rev_ordK.
Qed.

(* ========================================================================= *)
(* beta0 and beta_full                                                       *)
(* ========================================================================= *)

(** [beta_n(emptyset) = 1]: only the identity permutation has empty descent set. *)
Lemma beta0 n : beta (set0 : {set 'I_n}) = 1.
Proof.
rewrite /beta -(cards1 (1%g : {perm 'I_n.+1})); apply: eq_card => s.
rewrite !inE; apply/idP/idP.
- by move/eqP => Hds; apply/eqP/des0_id; rewrite /des Hds cards0.
- move/eqP => ->; apply/eqP/setP => i; rewrite !inE.
  by rewrite /is_descent !perm1 ltnNge /= leqW.
Qed.

(** Only the strictly-decreasing permutation [rev_perm_ord] has descent set
    equal to all positions. *)
Lemma descent_set_full_rev n (s : {perm 'I_n.+1}) :
  descent_set s = [set: 'I_n] -> s = rev_perm_ord n.
Proof.
move=> HD.
have Hrev : descent_set (rev_perm s) = set0.
  rewrite descent_set_rev_perm HD setCT.
  by apply/setP => j; rewrite !inE; apply/negP => /imsetP[x]; rewrite inE.
have /des0_id : des (rev_perm s) = 0 by rewrite /des Hrev cards0.
rewrite /rev_perm => Hrp.
apply/permP => i.
have Hi := congr1 (fun g : {perm 'I_n.+1} => g (rev_ord i)) Hrp.
rewrite perm1 permM !rev_perm_ordE rev_ordK in Hi.
by rewrite rev_perm_ordE -Hi.
Qed.

(** [beta_n(top) = 1]: only the reversal permutation has full descent set. *)
Lemma beta_full n : beta ([set: 'I_n] : {set 'I_n}) = 1.
Proof.
rewrite /beta -(cards1 (rev_perm_ord n)); apply: eq_card => s.
rewrite !inE; apply/idP/idP.
- by move/eqP/descent_set_full_rev => ->.
- by move/eqP => ->; rewrite descent_set_rev_perm_ord.
Qed.

(* ========================================================================= *)
(* Sum over all descent sets = (n+1)!                                        *)
(* ========================================================================= *)

(** [sum_D beta_n(D) = (n+1)!]: the [beta] partition of [{perm 'I_n.+1}] by
    descent set covers all permutations. *)
Lemma sum_beta_eq_fact n :
  \sum_(D : {set 'I_n}) beta D = n.+1`!.
Proof.
rewrite /beta -(card_Sn n.+1) -sum1_card.
rewrite (partition_big (@descent_set n) xpredT) //=.
by apply: eq_bigr => D _; rewrite -sum1dep_card.
Qed.

(* ========================================================================= *)
(* Connection to classical Eulerian numbers                                  *)
(* ========================================================================= *)

(** Connection to Eulerian numbers: summing [beta D] over all [D] of cardinality [k]
    recovers the Eulerian number [A(n+1, k)] (Stanley EC1, S1.4). *)
Lemma beta_eulerian n k :
  \sum_(D : {set 'I_n} | #|D| == k) beta D = eulerian n k.
Proof.
rewrite /beta /eulerian -sum1_card.
rewrite (partition_big (@descent_set n) (fun D => #|D| == k)) /=;
  last by move=> sigma; rewrite inE => /eqP <-.
apply: eq_bigr => D /eqP HD.
rewrite -sum1_card; apply: eq_bigl => sigma; rewrite !inE /=.
case E : (descent_set sigma == D); last by rewrite andbF.
by rewrite /des (eqP E) HD eqxx.
Qed.

(* ========================================================================= *)
(* Reversal-complement symmetry                                              *)
(* ========================================================================= *)

(** Reversal-complement symmetry: [beta_n(D) = beta_n(rev_ord(complement D))].
    Set-level refinement of [eulerian_symm], proved via the [rev_perm] involution. *)
Lemma beta_rev n (D : {set 'I_n}) :
  beta D = beta ([set rev_ord i | i in ~: D]).
Proof.
rewrite /beta -(card_imset _ (@rev_perm_inj n)).
congr #|pred_of_set _|; apply/setP => s; rewrite !inE; apply/imsetP/idP.
- by case=> t; rewrite inE => /eqP Ht ->; rewrite descent_set_rev_perm Ht.
- move/eqP => Hs; exists (rev_perm s); last by rewrite rev_perm_involutive.
  by rewrite inE descent_set_rev_perm Hs -imset_rev_ord_compl setCK imset_rev_ord_inv.
Qed.
