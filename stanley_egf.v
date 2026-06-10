(* Stanley Proposition 1.6.1: the exponential generating function of the     *)
(* Euler numbers is sec x + tan x.                                            *)
(*                                                                            *)
(*    \sum_n E_n x^n / n!  =  sec x + tan x                                   *)
(*                                                                            *)
(* as an identity of FORMAL power series over rat (no analysis), where        *)
(* E_n = eulerA n is the number of alternating permutations (reflection.v).   *)
(*                                                                            *)
(* Proof: the André recurrence euler_rec (reflection.v) says exactly that    *)
(* A := egf eulerA satisfies the formal quadratic ODE 2A' = 1 + A^2 with     *)
(* A(0) = 1 (euler_egf_ode, via the binomial-convolution workhorse egf_mul); *)
(* sec + tan satisfies the same ODE (sectan_ode, fps_trig.v); and solutions  *)
(* of that ODE are determined by their constant coefficient                   *)
(* (fps_quad_ode_uniq, fps_ode.v).                                            *)
(*                                                                            *)
(* This file is the bridge between the axiom-free combinatorial core          *)
(* (mathcomp_eulerian) and the classical generating-function layer            *)
(* (mathcomp_fps); its theorems carry the classical axioms of                  *)
(* mathcomp-classical and nothing else.                                       *)

From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra fingroup perm.
From mathcomp Require Import boolp.
From mathcomp_fps Require Import fps fps_deriv fps_egf fps_trig fps_ode.
From mathcomp_eulerian Require Import reflection.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.

(** rat has characteristic 0. *)
Lemma rat_char0 : has_pchar0 rat.
Proof. exact: Num.Theory.pchar_num. Qed.

(** The exponential generating function of the Euler numbers, over rat. *)
Definition euler_egf : {fps rat} := egf (fun n => (eulerA n)%:R).

Lemma euler_egf0 : euler_egf``_0 = 1.
Proof. by rewrite coef_egf fact0 divr1. Qed.

(** The André recurrence, as a formal differential equation:                 *)
(*      2 A' = 1 + A^2,   A(0) = 1.                                           *)
Lemma euler_egf_ode :
  2%:R *: fps_deriv euler_egf = 1 + euler_egf ^+ 2.
Proof.
rewrite /euler_egf (egf_deriv rat_char0) egfZ.
rewrite expr2 (egf_mul rat_char0) -[X in X + _]egf_dirac egfD.
apply: eq_egf => n.
case: n => [|m].
  by rewrite big_ord1 bin0 eulerA_0 eulerA_1 /= !mul1r mulr1 mulr2n.
rewrite /= add0r.
have := euler_rec m.
move/(congr1 (fun k : nat => k%:R : rat)).
rewrite natrM => ->.
rewrite natr_sum; apply: eq_bigr => k _.
by rewrite !natrM mulrA.
Qed.

(* ========================================================================= *)
(* Stanley EC1, Proposition 1.6.1                                            *)
(* ========================================================================= *)

Theorem stanley_1_6_1 : euler_egf = secf + tanf :> {fps rat}.
Proof.
apply: (fps_quad_ode_uniq rat_char0 euler_egf_ode (sectan_ode rat_char0)).
by rewrite coef_egf fact0 divr1 sectan0.
Qed.

(** Coefficient form: E_n = n! * [x^n] (sec x + tan x). *)
Corollary stanley_1_6_1_coef n :
  (eulerA n)%:R = n`!%:R * ((secf + tanf : {fps rat})``_n).
Proof.
have := congr1 (fun f : {fps rat} => f``_n) stanley_1_6_1.
rewrite coef_egf => <-.
by rewrite mulrC divfK ?(factf_neq0 rat_char0).
Qed.
