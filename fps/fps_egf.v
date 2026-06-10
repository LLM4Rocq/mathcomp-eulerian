(* mathcomp_fps: exponential generating functions.                           *)
(*                                                                            *)
(* Copyright 2026 the mathcomp-eulerian contributors.                         *)
(* SPDX-License-Identifier: Apache-2.0                                        *)
(*                                                                            *)
(*        egf a == the exponential generating function of the sequence a,    *)
(*                 the series with n-th coefficient a n / n!                  *)
(*                 (over a field of characteristic 0)                         *)
(*                                                                            *)
(* Main results:                                                              *)
(*   egf_mul : egf a * egf b is the egf of the BINOMIAL CONVOLUTION           *)
(*             n |-> sum_k 'C(n,k) * a k * b (n-k) — the workhorse that       *)
(*             makes EGF combinatorics go through.                            *)
(*   egf_deriv : fps_deriv (egf a) = egf (a o succ) — differentiation is     *)
(*             the shift.                                                     *)
(*   egf_eq  : egf is injective (coefficientwise).                            *)

From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import boolp.
From mathcomp_fps Require Import fps fps_deriv.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.

Section Egf.
Variable F : fieldType.
Hypothesis charF0 : has_pchar0 F.
Implicit Types a b : nat -> F.

Definition egf (a : nat -> F) : {fps F} := \fps (a n / n`!%:R) .x^n.

Lemma coef_egf a n : (egf a)``_n = a n / n`!%:R.
Proof. by []. Qed.

Lemma factf_neq0 n : n`!%:R != 0 :> F.
Proof. by rewrite (natf_neq0_char0 charF0) -lt0n fact_gt0. Qed.

Lemma binf_neq0 n k : (k <= n)%N -> 'C(n, k)%:R != 0 :> F.
Proof. by move=> ?; rewrite (natf_neq0_char0 charF0) -lt0n bin_gt0. Qed.

(** egf is injective, coefficientwise. *)
Lemma egf_eq a b : egf a = egf b -> a =1 b.
Proof.
move/fpsP => H n; have := H n; rewrite !coef_egf.
by move/(mulIf (invr_neq0 (factf_neq0 n))).
Qed.

Lemma egfD a b : egf a + egf b = egf (fun n => a n + b n).
Proof. by apply/fpsP => n /=; rewrite mulrDl. Qed.

Lemma egfZ (c : F) a : c *: egf a = egf (fun n => c * a n).
Proof. by apply/fpsP => n /=; rewrite mulrA. Qed.

(** The egf of the Kronecker delta is 1. *)
Lemma egf_dirac : egf (fun n => ((n == 0%N)%:R : F)) = 1.
Proof.
apply/fpsP => n; rewrite coef_egf coef_fps1.
by case: n => [|n] /=; rewrite ?fact0 ?divr1 // mul0r.
Qed.

(** THE workhorse: products of egfs are egfs of binomial convolutions. *)
Lemma egf_mul a b :
  egf a * egf b
  = egf (fun n => \sum_(k < n.+1) 'C(n, k)%:R * (a k * b (n - k)%N)).
Proof.
apply/fpsP => n; rewrite coef_fpsM coef_egf mulr_suml.
apply: eq_bigr => k _; rewrite !coef_egf.
have le_kn : (k <= n)%N by rewrite -ltnS ltn_ord.
have fact_split : n`!%:R = 'C(n, k)%:R * (k`! * (n - k)`!)%:R :> F.
  by rewrite -natrM bin_fact.
rewrite mulrACA -invfM -natrM fact_split invfM mulrA mulrAC.
rewrite mulrACA.
rewrite (mulrC ('C(n, k)%:R) (a k)) mulfK ?(binf_neq0 le_kn) //.
by rewrite mulrAC -mulrA.
Qed.

(** Differentiation of an egf is the index shift. *)
Lemma egf_deriv a : fps_deriv (egf a) = egf (fun n => a n.+1).
Proof.
apply/fpsP => n; rewrite coef_fps_deriv !coef_egf factS natrM invfM.
by rewrite mulrCA [n.+1%:R * (_ / _)]mulrA divff ?(natSf_neq0 charF0) //
   mul1r.
Qed.

End Egf.
