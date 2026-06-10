(* mathcomp_fps: exponential and logarithm of formal power series.           *)
(*                                                                            *)
(* Copyright 2026 the mathcomp-eulerian contributors.                         *)
(* SPDX-License-Identifier: Apache-2.0                                        *)
(*                                                                            *)
(* Over a comUnitRingType R in which every positive natural is invertible     *)
(* (hypothesis natU — e.g. a char-0 field, or {poly K} over one):            *)
(*      fps_e == the exponential series sum x^n/n!                            *)
(*      fps_l == the logarithm series log(1+x) = sum (-1)^(n-1) x^n/n         *)
(*  fps_exp f == fps_e \o f   (for f with zero constant coefficient)          *)
(*  fps_log u == fps_l \o (u - 1)   (for u with constant coefficient 1)       *)
(*                                                                            *)
(* Main results:                                                              *)
(*   fps_exp_deriv : (exp f)' = f' * exp f                                    *)
(*   fps_expD      : exp (f + g) = exp f * exp g                              *)
(*   fps_log_deriv : (log u)' = u^-1 * u'                                     *)
(*   fps_expK      : log (exp f) = f                                          *)
(*   fps_logK      : exp (log u) = u                                          *)
(*   fps_lin_ode_uniq : solutions of y' = a*y are determined by y(0)          *)
(*   fps_deriv_inj0U  : equal derivatives + equal constants => equal          *)
(* and the sanity demo: exp (log (1-x)^-1) = (1-x)^-1.                        *)

From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import boolp.
From mathcomp_fps Require Import fps fps_deriv fps_comp.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.

Section FpsExpLog.
Variable R : comUnitRingType.
Hypothesis natU : forall n : nat, (n.+1)%:R \is a @GRing.unit R.
Implicit Types f g : {fps R}.

Lemma factU n : n`!%:R \is a @GRing.unit R.
Proof.
elim: n => [|n IHn]; first by rewrite fact0 unitr1.
by rewrite factS natrM unitrM natU.
Qed.

(* ----------------------------------------------------------------------- *)
(* The two basic series                                                      *)
(* ----------------------------------------------------------------------- *)

Definition fps_e : {fps R} := \fps ((n`!%:R)^-1) .x^n.

Definition fps_l : {fps R} :=
  \fps (if n is m.+1 then (-1) ^+ m / (m.+1)%:R else 0) .x^n.

Lemma fps_e0 : fps_e``_0 = 1.
Proof. by rewrite /= fact0 invr1. Qed.

Lemma fps_l0 : fps_l``_0 = 0.
Proof. by []. Qed.

Lemma fps_e_deriv : fps_deriv fps_e = fps_e.
Proof.
apply/fpsP => n; rewrite coef_fps_deriv /= factS natrM.
by rewrite invrM ?natU ?factU // mulrCA divrr ?natU // mulr1.
Qed.

(* ----------------------------------------------------------------------- *)
(* The inverse of 1 + x                                                      *)
(* ----------------------------------------------------------------------- *)

Lemma onepX_unit : (1 + 'Xf : {fps R}) \is a GRing.unit.
Proof.
by rewrite fps_unitE coef_fpsD coef_fps1 coef_poly_fps coefX addr0 unitr1.
Qed.

Lemma onepX_mul_altgeom :
  (1 + 'Xf) * (\fps ((-1) ^+ n) .x^n) = 1 :> {fps R}.
Proof.
apply/fpsP => n; rewrite coef_fpsM coef_fps1.
case: n => [|n].
  by rewrite big_ord1 /= coefX /= addr0 mul1r.
rewrite big_ord_recl big_ord_recl /= !coefX /= !addr0 add0r.
rewrite mul1r mul1r subn0 subSS subn0 big1 ?addr0.
  by rewrite exprS mulN1r addNr.
move=> k _; rewrite coefX /=.
by rewrite add0r mul0r.
Qed.

Lemma fps_l_deriv : fps_deriv fps_l = (1 + 'Xf)^-1.
Proof.
have <- : (\fps ((-1) ^+ n) .x^n : {fps R}) = (1 + 'Xf)^-1.
  apply: (mulrI onepX_unit).
  by rewrite mulrV ?onepX_unit // onepX_mul_altgeom.
apply/fpsP => n; rewrite coef_fps_deriv /=.
by rewrite mulrCA divrr ?natU // mulr1.
Qed.

(* ----------------------------------------------------------------------- *)
(* The exponential and logarithm operators                                   *)
(* ----------------------------------------------------------------------- *)

Definition fps_exp f : {fps R} := fps_comp fps_e f.
Definition fps_log f : {fps R} := fps_comp fps_l (f - 1).

Lemma coef0_fps_exp f : (fps_exp f)``_0 = 1.
Proof. by rewrite coef0_fps_comp fps_e0. Qed.

Lemma fps_exp_unit f : fps_exp f \is a GRing.unit.
Proof. by rewrite fps_unitE coef0_fps_exp unitr1. Qed.

Lemma coef0_fps_log f : (fps_log f)``_0 = 0.
Proof. by rewrite coef0_fps_comp. Qed.

Lemma fps_unit1 f : f``_0 = 1 -> f \is a GRing.unit.
Proof. by move=> f1; rewrite fps_unitE f1 unitr1. Qed.

Lemma fps_exp_deriv f : f``_0 = 0 ->
  fps_deriv (fps_exp f) = fps_deriv f * fps_exp f.
Proof.
move=> f0; rewrite /fps_exp fps_comp_deriv // fps_e_deriv.
by rewrite mulrC.
Qed.

Lemma fps_log_deriv f : f``_0 = 1 ->
  fps_deriv (fps_log f) = f^-1 * fps_deriv f.
Proof.
move=> f1.
have v0 : (f - 1)``_0 = 0 by rewrite coef_fpsB f1 coef_fps1 subrr.
rewrite /fps_log fps_comp_deriv // fps_l_deriv.
rewrite fps_derivB fps_deriv1 subr0.
rewrite fps_compV ?onepX_unit //; congr (_^-1 * _).
rewrite fps_compD fps_comp1 fps_compX //.
by rewrite addrC subrK.
Qed.

(* ----------------------------------------------------------------------- *)
(* Uniqueness principles                                                     *)
(* ----------------------------------------------------------------------- *)

(** Solutions of the linear equation y' = a y are determined by y(0). *)
Lemma fps_lin_ode_uniq (a y z : {fps R}) :
  fps_deriv y = a * y -> fps_deriv z = a * z -> y``_0 = z``_0 -> y = z.
Proof.
move=> Hy Hz H0; apply/fpsP => n.
elim/ltn_ind: n => -[|n] IH //.
have IHle k : (k <= n)%N -> y``_k = z``_k.
  by move=> le_kn; apply: IH; rewrite ltnS.
have Hyn := congr1 (fun h : {fps R} => h``_n) Hy.
have Hzn := congr1 (fun h : {fps R} => h``_n) Hz.
rewrite coef_fps_deriv in Hyn.
rewrite coef_fps_deriv in Hzn.
apply: (mulrI (natU n)).
rewrite Hyn Hzn !coef_fpsM; apply: eq_bigr => k _; congr (_ * _).
by rewrite IHle // leq_subr.
Qed.

(** Equal derivatives and equal constant coefficients force equality. *)
Lemma fps_deriv_inj0U f g :
  fps_deriv f = fps_deriv g -> f``_0 = g``_0 -> f = g.
Proof.
move=> Hd H0; apply/fpsP => n.
case: n => [|n] //.
have := congr1 (fun h : {fps R} => h``_n) Hd.
rewrite !coef_fps_deriv.
exact: (mulrI (natU n)).
Qed.

(* ----------------------------------------------------------------------- *)
(* The group laws                                                            *)
(* ----------------------------------------------------------------------- *)

Lemma fps_expD f g : f``_0 = 0 -> g``_0 = 0 ->
  fps_exp (f + g) = fps_exp f * fps_exp g.
Proof.
move=> f0 g0.
apply: (@fps_lin_ode_uniq (fps_deriv f + fps_deriv g)).
- rewrite fps_exp_deriv ?coef_fpsD ?f0 ?g0 ?addr0 //.
  by rewrite fps_derivD.
- rewrite fps_derivM !fps_exp_deriv //.
  by rewrite mulrDl -mulrA [fps_exp f * (_ * _)]mulrCA.
- by rewrite coef0_fps_exp coef0_fpsM !coef0_fps_exp mulr1.
Qed.

(** exp (log u) = u. *)
Lemma fps_logK f : f``_0 = 1 -> fps_exp (fps_log f) = f.
Proof.
move=> f1.
apply: (@fps_lin_ode_uniq (f^-1 * fps_deriv f)).
- rewrite fps_exp_deriv ?coef0_fps_log //.
  by rewrite fps_log_deriv.
- by rewrite mulrAC mulVr ?fps_unit1 // mul1r.
- by rewrite coef0_fps_exp f1.
Qed.

(** log (exp f) = f. *)
Lemma fps_expK f : f``_0 = 0 -> fps_log (fps_exp f) = f.
Proof.
move=> f0.
apply: fps_deriv_inj0U; last by rewrite coef0_fps_log f0.
rewrite fps_log_deriv ?coef0_fps_exp //.
rewrite fps_exp_deriv // [_^-1 * _]mulrCA mulrC.
by rewrite mulVr ?fps_exp_unit // mul1r.
Qed.

(* ----------------------------------------------------------------------- *)
(* Sanity demo: exp and log of the geometric series                          *)
(* ----------------------------------------------------------------------- *)

Lemma fps_exp_log_geom :
  fps_exp (fps_log ((1 - 'Xf)^-1)) = ((1 - 'Xf)^-1 : {fps R}).
Proof. by apply: fps_logK; rewrite fps_inv_onesubX. Qed.

End FpsExpLog.
