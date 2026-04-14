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

Definition beta (n : nat) (D : {set 'I_n}) : nat :=
  #|[set sigma : {perm 'I_n.+1} | descent_set sigma == D]|.

(* ========================================================================= *)
(* Auxiliary: descent_set of rev_perm                                        *)
(* ========================================================================= *)

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

Lemma imset_rev_ord_inv n (D : {set 'I_n}) :
  [set rev_ord i | i in [set rev_ord i | i in D]] = D.
Proof.
apply/setP => x.
apply/imsetP/idP.
- by case=> y /imsetP[z Hz ->] ->; rewrite rev_ordK.
- move=> Hx; exists (rev_ord x); last by rewrite rev_ordK.
  by apply/imsetP; exists x.
Qed.

Lemma imset_rev_ord_compl n (D : {set 'I_n}) :
  [set rev_ord i | i in ~: D] = ~: [set rev_ord i | i in D].
Proof.
apply/setP => x; rewrite inE.
apply/imsetP/idP.
- case=> y; rewrite inE => HyND ->.
  apply/negP => /imsetP[z Hz Hrev].
  have Eyz : y = z.
    apply: (can_inj (@rev_ordK _)).
    by apply/val_inj/(congr1 val Hrev).
  by rewrite Eyz Hz in HyND.
- move=> HnD; exists (rev_ord x); last by rewrite rev_ordK.
  rewrite inE; apply/negP => Hx.
  move: HnD => /negP; apply.
  by apply/imsetP; exists (rev_ord x); rewrite // rev_ordK.
Qed.

(* ========================================================================= *)
(* beta0 and beta_full                                                       *)
(* ========================================================================= *)

(* Only the identity has no descents. *)
Lemma beta0 n : beta (set0 : {set 'I_n}) = 1.
Proof.
rewrite /beta -(cards1 (1%g : {perm 'I_n.+1})); apply: eq_card => s.
rewrite !inE; apply/idP/idP.
- move/eqP => Hds; apply/eqP.
  have : des s = 0 by rewrite /des Hds cards0.
  exact: des0_id.
- move/eqP => ->.
  apply/eqP/setP => i; rewrite !inE.
  by rewrite /is_descent !perm1 ltnNge /= leqW.
Qed.

(* Only the strictly-decreasing permutation has all descents. *)
Lemma descent_set_full_rev n (s : {perm 'I_n.+1}) :
  descent_set s = [set: 'I_n] -> s = rev_perm_ord n.
Proof.
move=> HD.
have Hrev : descent_set (rev_perm s) = set0.
  rewrite descent_set_rev_perm HD setCT.
  apply/setP => j; rewrite !inE.
  by apply/negP => /imsetP[x]; rewrite inE.
have : des (rev_perm s) = 0 by rewrite /des Hrev cards0.
move/des0_id; rewrite /rev_perm => Hrp.
apply/permP => i.
have Hi := congr1 (fun g : {perm 'I_n.+1} => g (rev_ord i)) Hrp.
rewrite perm1 permM !rev_perm_ordE rev_ordK in Hi.
by rewrite rev_perm_ordE -Hi.
Qed.

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

Lemma sum_beta_eq_fact n :
  \sum_(D : {set 'I_n}) beta D = n.+1`!.
Proof.
rewrite /beta.
transitivity (\sum_(D : {set 'I_n})
  \sum_(sigma : {perm 'I_n.+1} | descent_set sigma == D) 1).
  by apply: eq_bigr => D _;
     rewrite sum1_card; apply: eq_card => s; rewrite !inE.
rewrite (exchange_big_dep predT) //=.
rewrite -(card_Sn n.+1) -sum1_card.
apply: eq_bigr => sigma _.
rewrite (bigD1 (descent_set sigma)) //= big1 ?addn0 //.
by move=> D /andP[/eqP -> /eqP].
Qed.

(* ========================================================================= *)
(* Connection to classical Eulerian numbers                                  *)
(* ========================================================================= *)

Lemma beta_eulerian n k :
  \sum_(D : {set 'I_n} | #|D| == k) beta D = eulerian n k.
Proof.
rewrite /beta /eulerian -sum1_card.
rewrite (partition_big (@descent_set n) (fun D => #|D| == k)) /=;
  last by move=> sigma; rewrite inE => /eqP <-.
apply: eq_bigr => D /eqP HD.
rewrite -sum1_card; apply: eq_bigl => sigma.
rewrite !inE /=.
case E : (descent_set sigma == D); last by rewrite andbF.
by move/eqP: E => EE; rewrite /des EE HD eqxx.
Qed.

(* ========================================================================= *)
(* Reversal-complement symmetry                                              *)
(* ========================================================================= *)

Lemma beta_rev n (D : {set 'I_n}) :
  beta D = beta ([set rev_ord i | i in ~: D]).
Proof.
rewrite /beta.
rewrite -(card_imset _ (@rev_perm_inj n)).
congr #|pred_of_set _|; apply/setP => s; rewrite !inE.
apply/imsetP/idP.
- case=> t; rewrite inE => /eqP Ht Hst; subst s.
  by rewrite descent_set_rev_perm Ht.
- move/eqP => Hs.
  exists (rev_perm s); last by rewrite rev_perm_involutive.
  rewrite inE descent_set_rev_perm Hs.
  rewrite -imset_rev_ord_compl setCK.
  by rewrite imset_rev_ord_inv.
Qed.
