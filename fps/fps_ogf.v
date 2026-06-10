(* mathcomp_fps: ordinary generating function toolkit.                       *)
(*                                                                            *)
(* Copyright 2026 the mathcomp-eulerian contributors.                         *)
(* SPDX-License-Identifier: Apache-2.0                                        *)
(*                                                                            *)
(* Powers of the geometric series and their coefficients (the "negative      *)
(* binomial" expansion):                                                       *)
(*    coef_fps_geomXn : (fps_geom ^+ k.+1)``_m = 'C(m + k, k)%:R              *)
(*    onesubXn_mul_geomn : (1 - 'Xf) ^+ N * fps_geom ^+ N = 1                 *)
(* These are the OGF counterparts of the EGF calculus in fps_egf.v, used      *)
(* for Stanley §1.4 (Worpitzky / Eulerian polynomial) identities.             *)

From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import boolp.
From mathcomp_fps Require Import fps.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.

(* ========================================================================= *)
(* A binomial summation (Pascal staircase)                                    *)
(* ========================================================================= *)

(** \sum_(j <= m) 'C(m - j + k, k) = 'C(m + k + 1, k + 1).                    *)
Lemma sum_bin_stair (k m : nat) :
  (\sum_(j < m.+1) 'C(m - j + k, k) = 'C((m + k).+1, k.+1))%N.
Proof.
elim: m => [|m IHm].
  by rewrite big_ord1 subn0 !add0n !binn.
rewrite big_ord_recl /= subn0.
under eq_bigr => j _ do rewrite /bump /= add1n subSS.
by rewrite IHm binS addnC addSn.
Qed.

(* ========================================================================= *)
(* Coefficients of powers of the geometric series                             *)
(* ========================================================================= *)

Section GeomPowers.
Variable R : comUnitRingType.

(** The negative binomial expansion: 1/(1-x)^(k+1) = sum_m C(m+k,k) x^m. *)
Lemma coef_fps_geomXn (k m : nat) :
  ((fps_geom R ^+ k.+1)``_m) = 'C(m + k, k)%:R.
Proof.
elim: k m => [|k IHk] m.
  by rewrite expr1 /fps_geom /= addn0 bin0.
rewrite exprS coef_fpsM.
under eq_bigr => j _ do rewrite [(fps_geom R)``_j]/= mul1r IHk.
by rewrite -natr_sum sum_bin_stair addnS.
Qed.

(** Powers of 1 - x and of the geometric series are mutually inverse. *)
Lemma onesubXn_mul_geomn (N : nat) :
  ((1 - 'Xf) ^+ N) * (fps_geom R ^+ N) = 1.
Proof. by rewrite -exprMn onesubX_mul_geom expr1n. Qed.

End GeomPowers.
