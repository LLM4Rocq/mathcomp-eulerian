(* Stanley EC1 §1.4: the ordinary generating function of the powers          *)
(* (m+1)^(n+1) is the Eulerian polynomial over (1-x)^(n+2):                   *)
(*                                                                            *)
(*    \sum_(m >= 0) (m+1)^(n+1) x^m  =  A_n(x) / (1-x)^(n+2)                  *)
(*                                                                            *)
(* as formal power series over int, where A_n = eul_pol n (qeul.v) is the     *)
(* Eulerian polynomial of permutations of n+1 letters.  The combinatorial     *)
(* content is Worpitzky's identity (worpitzky.v, axiom-free); this file is    *)
(* the generating-function packaging on top of mathcomp_fps.                  *)
(*                                                                            *)
(* Note the coefficient ring: int is NOT a field — the proof uses the         *)
(* mathcomp_fps units theory over an arbitrary comUnitRingType (1 - x is      *)
(* invertible because its constant coefficient 1 is).                         *)

From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra fingroup perm.
From mathcomp Require Import boolp.
From mathcomp_fps Require Import fps fps_ogf.
From mathcomp_eulerian Require Import eulerian qfact qeul worpitzky.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.

(** The OGF of the (n+1)-st powers: coefficient m is (m+1)^(n+1). *)
Definition pow_ogf (n : nat) : {fps int} :=
  \fps (((m.+1) ^ n.+1)%N %:R) .x^m.

(* ========================================================================= *)
(* Stanley EC1 §1.4: the Eulerian-polynomial generating function             *)
(* ========================================================================= *)

(** Division form: A_n(x) * (1/(1-x))^(n+2) = sum_m (m+1)^(n+1) x^m.          *)
(* Coefficientwise this is exactly Worpitzky's identity, with the negative    *)
(* binomial expansion of the geometric-series power (coef_fps_geomXn).        *)
Theorem stanley_1_4_div n :
  poly_fps (eul_pol n) * fps_geom int ^+ n.+2 = pow_ogf n.
Proof.
apply/fpsP => m; rewrite coef_fpsM.
under eq_bigr => j _ do
  rewrite coef_poly_fps coef_eul_pol coef_fps_geomXn -natrM.
rewrite -natr_sum [(pow_ogf n)``_m]/= worpitzky.
congr (_%:R).
under eq_bigr => i _ do rewrite (addnBAC _ (ltn_ord i : (i <= m)%N)).
pose G j := (eulerian n j * 'C(m + n.+1 - j, n.+1))%N.
have sumF (q : nat) (H : nat -> nat) : (q < (m + n).+2)%N ->
    (forall j, (q < j)%N -> H j = 0%N) ->
    (\sum_(j < q.+1) H j = \sum_(j < (m + n).+2) H j)%N.
  move=> le_q Hz; rewrite (big_ord_widen _ H le_q) big_mkcond /=.
  apply: eq_bigr => j _; case: ltnP => // lt_qj.
  by rewrite Hz.
rewrite (sumF m G); first last.
- move=> j lt_mj; rewrite /G bin_small ?muln0 //.
  rewrite ltnS (leq_trans (leq_sub2l (m + n.+1) lt_mj)) //.
  by rewrite addnS subSS addnC addnK.
- by rewrite ltnS (leq_trans (leq_addr n m)) ?leqnSn.
rewrite (sumF n G) //; first last.
- by move=> j lt_nj; rewrite /G eulerian_out_of_range // mul0n.
by rewrite !ltnS (leq_trans (leq_addl m n)) ?leqnSn.
Qed.

(** Multiplied-out form (no division): the OGF times (1-x)^(n+2) is the       *)
(* Eulerian polynomial.                                                       *)
Theorem stanley_1_4 n :
  pow_ogf n * ((1 - 'Xf) ^+ n.+2) = poly_fps (eul_pol n).
Proof.
rewrite -stanley_1_4_div -mulrA -exprMn [fps_geom int * _]mulrC.
by rewrite onesubX_mul_geom expr1n mulr1.
Qed.

(** Display form with the explicit inverse of 1 - x. *)
Corollary stanley_1_4_inv n :
  pow_ogf n = poly_fps (eul_pol n) * (((1 - 'Xf)^-1) ^+ n.+2).
Proof. by rewrite fps_inv_onesubX stanley_1_4_div. Qed.
