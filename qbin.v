(* Gaussian (q-)binomial coefficients, as integer polynomials in q.          *)
(*                                                                            *)
(*    qbin n k == the Gaussian binomial [n choose k]_q : {poly int},          *)
(*                defined by the q-Pascal recurrence                          *)
(*                   [n+1, k+1] = [n, k] + q^(k+1) [n, k+1]                   *)
(*                with [n, 0] = 1 and [0, k+1] = 0.                           *)
(*                                                                            *)
(* Basic theory: boundary values, vanishing out of range, and the             *)
(* specialization q = 1 recovering the ordinary binomial coefficients.        *)
(* This file is AXIOM-FREE (combinatorial core); the generating-function      *)
(* identity (the q-staircase, denominator of Carlitz's identity) lives in     *)
(* carlitz.v on top of mathcomp_fps.                                          *)

From mathcomp Require Import all_ssreflect all_algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.

(* ========================================================================= *)
(* Definition                                                                 *)
(* ========================================================================= *)

Fixpoint qbin (n k : nat) : {poly int} :=
  match n, k with
  | _, 0%N => 1
  | 0%N, _.+1 => 0
  | n'.+1, k'.+1 => qbin n' k' + 'X^(k'.+1) * qbin n' k'.+1
  end.

Lemma qbin_n0 n : qbin n 0 = 1.
Proof. by case: n. Qed.

Lemma qbin_0S k : qbin 0 k.+1 = 0.
Proof. by []. Qed.

(** The defining q-Pascal recurrence. *)
Lemma qbinS n k :
  qbin n.+1 k.+1 = qbin n k + 'X^(k.+1) * qbin n k.+1.
Proof. by []. Qed.

(* ========================================================================= *)
(* Boundary behaviour                                                         *)
(* ========================================================================= *)

Lemma qbin_small n k : (n < k)%N -> qbin n k = 0.
Proof.
elim: n k => [|n IHn] [|k] // lt_nk.
by rewrite qbinS !IHn // ?mulr0 ?addr0 // ltnW.
Qed.

Lemma qbin_nn n : qbin n n = 1.
Proof.
elim: n => [|n IHn] //.
by rewrite qbinS IHn qbin_small // mulr0 addr0.
Qed.

(* ========================================================================= *)
(* Specialization q = 1: ordinary binomials                                   *)
(* ========================================================================= *)

Lemma qbin_horner1 n k : (qbin n k).[1] = ('C(n, k))%:R.
Proof.
elim: n k => [|n IHn] [|k]; rewrite ?qbin_n0 ?hornerC ?bin0 //.
rewrite qbinS hornerD hornerM hornerXn expr1n mul1r !IHn.
by rewrite binS natrD addrC.
Qed.
