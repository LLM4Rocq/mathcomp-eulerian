(* Layer 6 (Phase C): André's reflection method for Euler numbers.            *)
(*                                                                            *)
(* Stanley EC1 §1.6.4.                                                        *)
(*                                                                            *)
(* This file lands the definitions of Euler numbers via the alternating       *)
(* descent set and the trivial base cases.  The substantive recurrence        *)
(*                                                                            *)
(*    2 * eulerA n.+2 = \sum_(k < n.+2) 'C(n.+1, k) * eulerA k * eulerA (n.+1 - k) *)
(*                                                                            *)
(* is left for sessions C-2 through C-5.                                      *)

From mathcomp Require Import all_ssreflect fingroup perm.
From mathcomp_eulerian Require Import ordinal_reindex perm_compress
                                       descent eulerian beta beta_omega
                                       beta_swap.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* ========================================================================= *)
(* §A. Definitions                                                           *)
(* ========================================================================= *)

(* euler n = number of permutations of 'I_n.+1 with descent set equal to     *)
(* alt_desc_set n = {0, 2, 4, ...}.  In Stanley's notation this is A_{n+1}: *)
(* the count of down-up alternating permutations of length n+1.              *)
Definition euler (n : nat) : nat := beta (alt_desc_set n).

(* eulerA n = A_n in Stanley's notation, with the convention                  *)
(* A_0 := 1 (empty alternating permutation).                                  *)
Definition eulerA (n : nat) : nat :=
  if n is k.+1 then euler k else 1.

(* ========================================================================= *)
(* §B. Trivial base cases                                                    *)
(* ========================================================================= *)

Lemma eulerA_0 : eulerA 0 = 1.
Proof. by []. Qed.

(* alt_desc_set 0 = set0 since 'I_0 is empty.                                *)
Lemma alt_desc_set_0 : alt_desc_set 0 = set0.
Proof. by apply/setP; case; case. Qed.

(* euler 0 counts perms of 'I_1 with descent_set = set0; only id qualifies. *)
Lemma euler_0 : euler 0 = 1.
Proof. by rewrite /euler alt_desc_set_0 beta0. Qed.

Lemma eulerA_1 : eulerA 1 = 1.
Proof. by rewrite /eulerA euler_0. Qed.

(* alt_desc_set 1 = [set: 'I_1] since the unique element of 'I_1 has         *)
(* val 0 and ~~ odd 0 is true.                                               *)
Lemma alt_desc_set_1 : alt_desc_set 1 = [set: 'I_1].
Proof.
apply/setP => i; rewrite mem_alt_desc_set inE.
by have /eqP -> : val i == 0%N by rewrite -leqn0 -ltnS ltn_ord.
Qed.

(* euler 1 = beta (alt_desc_set 1) = beta setT = 1 (only [1;0] in S_2).      *)
Lemma euler_1 : euler 1 = 1.
Proof. by rewrite /euler alt_desc_set_1 beta_full. Qed.

Lemma eulerA_2 : eulerA 2 = 1.
Proof. by rewrite /eulerA euler_1. Qed.

(* ========================================================================= *)
(* §C. descent_set under insert_max_perm                                     *)
(* ========================================================================= *)

(* These lemmas refine the existing [des_insert_max_*] (which give descent   *)
(* COUNT changes) into descent SET characterizations.  They are proved by    *)
(* the same case analysis as the count versions in eulerian.v.               *)

(* Inserting ord_max at position 0: a forced descent appears at slot 0,     *)
(* and old descents shift up by one (slot k of t becomes slot k+1).         *)
Lemma descent_set_insert_max_ord0 n (t : {perm 'I_n.+1}) :
  descent_set (insert_max_perm t (ord0 : 'I_n.+2))
  = (ord0 : 'I_n.+1) |: [set lift ord0 j | j in descent_set t].
Proof.
rewrite /descent_set; apply/setP => i; rewrite !inE.
case: (unliftP ord0 i) => [j ->|->].
- rewrite eq_sym (negbTE (neq_lift _ _)) /=.
  have E1 : widen_ord (leqnSn n.+1) (lift ord0 j)
          = lift ord0 (widen_ord (leqnSn n) j) :> 'I_n.+2.
    by apply/val_inj; rewrite /= /bump leq0n /= add1n.
  rewrite /is_descent E1 !insert_max_perm_lift.
  apply/idP/imsetP.
  + by move=> H; exists j; first by rewrite inE /is_descent.
  + by case=> j' /[!inE] Hj' /lift_inj ->; rewrite /is_descent.
- rewrite eqxx orTb /is_descent.
  have -> : widen_ord (leqnSn n.+1) (ord0 : 'I_n.+1) = ord0 :> 'I_n.+2.
    by apply/val_inj.
  by rewrite insert_max_perm_at_p insert_max_perm_lift /=; apply: ltn_ord.
Qed.

(* Inserting ord_max at position ord_max (= n.+1): no new descent created;  *)
(* old descents at slot k stay at slot k (no shift, since we use lift       *)
(* ord_max to embed 'I_n.+1 into 'I_n.+2 by widening).                     *)
Lemma descent_set_insert_max_ord_max n (t : {perm 'I_n.+1}) :
  descent_set (insert_max_perm t (ord_max : 'I_n.+2))
  = [set (lift ord_max j : 'I_n.+1) | j in descent_set t].
Proof.
rewrite /descent_set; apply/setP => i; rewrite !inE.
case: (unliftP ord_max i) => [j ->|->].
- have E1 : widen_ord (leqnSn n.+1) (lift ord_max j)
          = lift ord_max (widen_ord (leqnSn n) j) :> 'I_n.+2.
    apply/val_inj; rewrite /= /bump /=.
    rewrite leqNgt (ltn_ord j) /=.
    by rewrite leqNgt (leq_trans (ltn_ord j) (leqnSn n)).
  have E2 : lift ord0 (lift ord_max j : 'I_n.+1)
          = lift ord_max (lift ord0 j) :> 'I_n.+2.
    apply/val_inj => /=.
    rewrite /bump /=.
    have H2 : (n <= j) = false by apply/negbTE; rewrite -ltnNge; apply: ltn_ord.
    have H3 : (n.+1 <= j.+1) = false by apply/negbTE; rewrite -ltnNge; apply: ltn_ord.
    by rewrite H2 H3.
  rewrite /is_descent E1 E2 !insert_max_perm_lift.
  apply/idP/imsetP.
  + by move=> H; exists j; first by rewrite inE /is_descent.
  + by case=> j' /[!inE] Hj' /lift_inj ->; rewrite /is_descent.
- rewrite /is_descent.
  have E1 : widen_ord (leqnSn n.+1) (ord_max : 'I_n.+1)
          = lift ord_max (ord_max : 'I_n.+1) :> 'I_n.+2.
    by apply/val_inj; rewrite /= /bump /= leqNgt ltnSn.
  have -> : lift ord0 (ord_max : 'I_n.+1) = ord_max :> 'I_n.+2.
    by apply/val_inj.
  rewrite E1 insert_max_perm_lift insert_max_perm_at_p.
  apply/idP/imsetP.
  + by move=> H; move: (ltn_ord (t (ord_max : 'I_n.+1)));
       rewrite ltnNge /= in H; case/negP: H; apply: ltnW.
  + case=> j' _ /eqP; rewrite -val_eqE /= /bump /= leqNgt ltn_ord /= => /eqP eqn.
    rewrite add0n in eqn.
    by move: (ltn_ord j'); rewrite -eqn ltnn.
Qed.

(* Interior insertion at position p = lift ord0 (widen_ord _ j) where        *)
(* j : 'I_n.  In one-line notation, this places ord_max at slot p (which    *)
(* equals j.+1).  The descent set is the [lift h]-image of                  *)
(*    descent_set t  ∪  {j}                                                  *)
(* where h = widen_ord (leqnSn n) j.  Intuition:                             *)
(*  - slots strictly below j: inherited from t (no shift).                   *)
(*  - slot j: forced ASCENT (going INTO ord_max), so slot val j of the new  *)
(*    perm — here represented as lift h applied to the [ord0..j-1]-part —   *)
(*    is NOT a descent.                                                      *)
(*  - slot j.+1 = val p: forced DESCENT (going OUT OF ord_max).             *)
(*  - slots strictly above j.+1: inherited from t at slots > j (shifted     *)
(*    up by one).                                                            *)
(* The clean statement uses lift h to package both shifts uniformly.        *)
Lemma descent_set_insert_max_interior n (t : {perm 'I_n.+1}) (j : 'I_n) :
  let h := widen_ord (leqnSn n) j in
  descent_set (insert_max_perm t (lift ord0 h))
  = [set lift h x | x in descent_set t :|: [set j]].
Proof.
move=> h; set p := lift ord0 h; set sigma := insert_max_perm t p.
rewrite /descent_set; apply/setP => i; rewrite !inE.
case: (unliftP h i) => [x ->|->].
- have sigma_lift0 : forall y : 'I_n,
    sigma (lift ord0 (lift h y)) = widen_ord (leqnSn n.+1) (t (lift ord0 y)).
    move=> y.
    have E : lift ord0 (lift h y) = lift p (lift ord0 y) :> 'I_n.+2.
      by apply/val_inj => /=; rewrite /p /=; rewrite /bump /= addnCA.
    by rewrite /sigma E insert_max_perm_lift.
  have -> : (lift h x \in [set lift h x0 | x0 in descent_set t :|: [set j]])
          = (is_descent t x) || (x == j).
    apply/imsetP/idP => [[y]|].
    + by rewrite !inE => /orP[Hy|/eqP ->] /lift_inj ->;
         [rewrite Hy|rewrite eqxx orbT].
    + case/orP => [H|/eqP ->].
      - by exists x; rewrite // !inE H.
      - by exists j; rewrite // !inE eqxx orbT.
  rewrite /is_descent sigma_lift0 /=.
  case: (eqVneq x j) => [->|xnj].
  + have -> : sigma (widen_ord (leqnSn n.+1) (lift h j)) = ord_max.
      have E : widen_ord (leqnSn n.+1) (lift h j) = p :> 'I_n.+2.
        by apply/val_inj; rewrite /= /p /= /bump /= leqnn.
      by rewrite /sigma E insert_max_perm_at_p.
    by rewrite orbT; apply: ltn_ord.
  + rewrite orbF.
    have E : widen_ord (leqnSn n.+1) (lift h x) = lift p (widen_ord (leqnSn n) x) :> 'I_n.+2.
      apply/val_inj; rewrite /= /p /= /bump /=.
      case: (ltngtP x j) => [Hxj|Hxj|Hxj].
      - by [].
      - by [].
      - by rewrite -val_eqE /= Hxj eqxx in xnj.
    by rewrite /sigma E insert_max_perm_lift.
- have Rfalse : (h \in [set lift h x | x in descent_set t :|: [set j]]) = false.
    by apply/negbTE/imsetP => -[y _ Hy]; have := neq_lift h y; rewrite -Hy eqxx.
  rewrite Rfalse /is_descent.
  have E1 : widen_ord (leqnSn n.+1) h = lift p h :> 'I_n.+2.
    apply/val_inj; rewrite /= /p /= /bump /=.
    by rewrite add1n ltnn.
  have E2 : lift ord0 h = p :> 'I_n.+2 by [].
  rewrite E1 E2 insert_max_perm_lift insert_max_perm_at_p.
  apply/negbTE; rewrite -leqNgt.
  by apply: ltnW; rewrite /=; exact: ltn_ord.
Qed.
