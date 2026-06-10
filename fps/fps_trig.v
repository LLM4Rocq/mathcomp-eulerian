(* mathcomp_fps: the standard series exp, sin, cos, sec, tan.                *)
(*                                                                            *)
(* Copyright 2026 the mathcomp-eulerian contributors.                         *)
(* SPDX-License-Identifier: Apache-2.0                                        *)
(*                                                                            *)
(* Over a field F of characteristic 0:                                        *)
(*    expf == egf of the constant sequence 1                                  *)
(*    sinf == egf of 0, 1, 0, -1, 0, 1, ...                                   *)
(*    cosf == egf of 1, 0, -1, 0, 1, ...                                      *)
(*    secf == cosf^-1   (cosf has unit constant coefficient)                  *)
(*    tanf == sinf * secf                                                     *)
(*                                                                            *)
(* Main results: the derivative rules, the Pythagorean identity               *)
(* sin2cos2 (sin^2 + cos^2 = 1, by the derivative trick), sec2f               *)
(* (sec^2 = 1 + tan^2) and the quadratic ODE for sec + tan:                   *)
(*    sectan_ode : 2 *: (sec + tan)' = 1 + (sec + tan)^2,  (sec+tan)(0) = 1.  *)

From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import boolp.
From mathcomp_fps Require Import fps fps_deriv fps_egf.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.

Section Trig.
Variable F : fieldType.
Hypothesis charF0 : has_pchar0 F.

Definition expf : {fps F} := egf (fun _ => 1).
Definition sinf : {fps F} :=
  egf (fun n => if odd n then (-1) ^+ n./2 else 0).
Definition cosf : {fps F} :=
  egf (fun n => if odd n then 0 else (-1) ^+ n./2).
Definition secf : {fps F} := cosf ^-1.
Definition tanf : {fps F} := sinf * secf.

(* ----------------------------------------------------------------------- *)
(* Constant coefficients                                                     *)
(* ----------------------------------------------------------------------- *)

Lemma expf0 : expf``_0 = 1.
Proof. by rewrite coef_egf fact0 divr1. Qed.

Lemma sinf0 : sinf``_0 = 0.
Proof. by rewrite coef_egf mul0r. Qed.

Lemma cosf0 : cosf``_0 = 1.
Proof. by rewrite coef_egf fact0 divr1. Qed.

Lemma cosf_unit : cosf \is a GRing.unit.
Proof. by rewrite fps_unitE cosf0 unitr1. Qed.

Lemma cos_mul_sec : cosf * secf = 1.
Proof. by rewrite /secf divrr // cosf_unit. Qed.

Lemma secf0 : secf``_0 = 1.
Proof.
have := congr1 (fun f : {fps F} => f``_0) cos_mul_sec.
by rewrite coef0_fpsM cosf0 mul1r coef_fps1.
Qed.

Lemma tanf0 : tanf``_0 = 0.
Proof. by rewrite /tanf coef0_fpsM sinf0 mul0r. Qed.

(* ----------------------------------------------------------------------- *)
(* Derivative rules                                                          *)
(* ----------------------------------------------------------------------- *)

Lemma expf_deriv : fps_deriv expf = expf.
Proof. by rewrite /expf (egf_deriv charF0). Qed.

Lemma sinf_deriv : fps_deriv sinf = cosf.
Proof.
rewrite /sinf (egf_deriv charF0); apply/fpsP => n; rewrite !coef_egf.
congr (_ / _); rewrite oddS.
case Hodd: (odd n) => //=.
by rewrite uphalf_half Hodd.
Qed.

Lemma cosf_deriv : fps_deriv cosf = - sinf.
Proof.
rewrite /cosf (egf_deriv charF0); apply/fpsP => n.
rewrite coef_fpsN !coef_egf -mulNr; congr (_ / _); rewrite oddS.
case Hodd: (odd n) => /=; last by rewrite oppr0.
by rewrite uphalf_half Hodd add1n exprS mulN1r.
Qed.

(* ----------------------------------------------------------------------- *)
(* The Pythagorean identity, by the derivative trick                         *)
(* ----------------------------------------------------------------------- *)

Lemma sin2cos2 : sinf ^+ 2 + cosf ^+ 2 = 1.
Proof.
have D0 : fps_deriv (sinf ^+ 2 + cosf ^+ 2) = 0.
  rewrite fps_derivD !expr2 !fps_derivM sinf_deriv cosf_deriv.
  by rewrite mulNr mulrN [sinf * cosf]mulrC -opprD subrr.
have := fps_deriv_eq0 charF0 D0.
rewrite coef_fpsD !expr2 !coef0_fpsM sinf0 cosf0 mulr0 mulr1 add0r.
by move=> ->; rewrite scale1r.
Qed.

(** sec^2 = 1 + tan^2. *)
Lemma sec2f : secf ^+ 2 = 1 + tanf ^+ 2.
Proof.
have := congr1 (fun f : {fps F} => f * secf ^+ 2) sin2cos2.
move=> H; rewrite mul1r mulrDl !expr2 in H.
rewrite [sinf * sinf * _]mulrACA [cosf * cosf * _]mulrACA in H.
rewrite cos_mul_sec mulr1 in H.
by rewrite !expr2 /tanf -H addrC.
Qed.

(* ----------------------------------------------------------------------- *)
(* Derivatives of sec and tan                                                *)
(* ----------------------------------------------------------------------- *)

Lemma secf_deriv : fps_deriv secf = tanf * secf.
Proof.
have Hd := congr1 (@fps_deriv F) cos_mul_sec.
rewrite fps_derivM fps_deriv1 cosf_deriv mulNr in Hd.
have HcD : cosf * fps_deriv secf = sinf * secf.
  by move: Hd; rewrite addrC => /eqP; rewrite subr_eq0 => /eqP.
have := congr1 (fun f : {fps F} => secf * f) HcD.
rewrite mulrA [secf * cosf]mulrC cos_mul_sec mul1r => ->.
by rewrite /tanf mulrCA -mulrA.
Qed.

Lemma tanf_deriv : fps_deriv tanf = 1 + tanf ^+ 2.
Proof.
rewrite {1}/tanf fps_derivM sinf_deriv secf_deriv.
by rewrite cos_mul_sec expr2 mulrCA -/tanf.
Qed.

(* ----------------------------------------------------------------------- *)
(* The quadratic ODE for sec + tan                                           *)
(* ----------------------------------------------------------------------- *)

Lemma sectan0 : (secf + tanf)``_0 = 1.
Proof. by rewrite coef_fpsD secf0 tanf0 addr0. Qed.

Theorem sectan_ode :
  2%:R *: fps_deriv (secf + tanf) = 1 + (secf + tanf) ^+ 2.
Proof.
rewrite fps_derivD secf_deriv tanf_deriv scaler_nat sqrrD sec2f.
rewrite !mulr2n [secf * tanf]mulrC !addrA.
rewrite [tanf * secf + 1]addrC.
rewrite [_ + tanf * secf + 1]addrAC.
rewrite [1 + tanf * secf + tanf ^+ 2 + 1]addrAC.
rewrite [1 + tanf * secf + 1]addrAC.
by rewrite [1 + 1 + tanf * secf + tanf ^+ 2]addrAC.
Qed.

End Trig.

Arguments expf {F}.
Arguments sinf {F}.
Arguments cosf {F}.
Arguments secf {F}.
Arguments tanf {F}.
