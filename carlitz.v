(* Toward Carlitz's q-analogue of Stanley §1.4 (phase 4 of                    *)
(* docs/plans/FPS_PLAN.md):                                                    *)
(*                                                                            *)
(*    \sum_m ([m+1]_q)^(n+1) x^m                                              *)
(*       = (\sum_w q^(maj w) x^(des w)) / \prod_(i <= n+1) (1 - q^i x).       *)
(*                                                                            *)
(* This file provides the DENOMINATOR half: the generating function of the    *)
(* Gaussian binomials (the "q-staircase"), over {fps {poly int}} — series in *)
(* x with coefficients in the q-ring Z[q]:                                    *)
(*                                                                            *)
(*    q_staircase : \prod_(i < N.+1) (1 - q^i *: x) * \sum_m [m+N, N]_q x^m   *)
(*                  = 1.                                                      *)
(*                                                                            *)
(* The numerator half needs the q-Eulerian (maj, des) insertion recurrence    *)
(* for q_eul_pol (qeul.v), which is future work — see the plan.  Note Z[q]   *)
(* is not a field: the inverses exist by the mathcomp_fps unit theory         *)
(* (constant coefficient 1).                                                  *)

From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra fingroup perm.
From mathcomp Require Import boolp.
From mathcomp_fps Require Import fps fps_ogf.
From mathcomp_eulerian Require Import qbin.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.

(* ========================================================================= *)
(* The q-staircase series                                                     *)
(* ========================================================================= *)

(** The product prod_(i <= N) (1 - q^i x), the Carlitz denominator. *)
Definition q_onesub_prod (N : nat) : {fps {poly int}} :=
  \prod_(i < N.+1) (1 - ('X^i : {poly int}) *: 'Xf).

(** The generating function of the Gaussian binomials [m+N, N]_q. *)
Definition q_stair (N : nat) : {fps {poly int}} :=
  \fps (qbin (m + N) N) .x^m.

Lemma q_stair0 : q_stair 0 = fps_geom {poly int}.
Proof. by apply/fpsP => m; rewrite /= addn0 qbin_n0. Qed.

(** Coefficient shift under multiplication by x (local copy). *)
Lemma coef_fpsXfM' (R : comNzRingType) (f : {fps R}) n :
  ('Xf * f)``_n = if n is m.+1 then f``_m else 0.
Proof.
rewrite coef_fpsM; case: n => [|m].
  by rewrite big_ord1 /= coefX /= mul0r.
rewrite big_ord_recl big_ord_recl /= !coefX /= mul0r add0r mul1r subSS subn0.
by rewrite big1 ?addr0 // => k _; rewrite coefX /= mul0r.
Qed.

(** Peeling one factor: (1 - q^(N+1) x) [m+N+1, N+1]-series = [m+N, N]-series.*)
Lemma q_stair_step N :
  (1 - ('X^(N.+1) : {poly int}) *: 'Xf) * q_stair N.+1 = q_stair N.
Proof.
rewrite mulrBl mul1r -scalerAl.
apply/fpsP => m; rewrite coef_fpsB coef_fpsZ coef_fpsXfM'.
case: m => [|m].
  rewrite mulr0 subr0 /=.
  by rewrite add0n (qbin_small (ltnSn N)) mulr0 addr0.
rewrite [(q_stair N.+1)``_m.+1]/= [(q_stair N.+1)``_m]/=
        [(q_stair N)``_m.+1]/=.
by rewrite addrK addnS.
Qed.

(* ========================================================================= *)
(* The q-staircase identity                                                   *)
(* ========================================================================= *)

Theorem q_staircase N : q_onesub_prod N * q_stair N = 1.
Proof.
elim: N => [|N IHN].
  rewrite /q_onesub_prod big_ord1 expr0 scale1r q_stair0.
  exact: onesubX_mul_geom.
rewrite /q_onesub_prod big_ord_recr /= -mulrA q_stair_step.
exact: IHN.
Qed.

(** Corollary in division form: the inverse of the Carlitz denominator. *)
Lemma q_onesub_prod_unit N : q_onesub_prod N \is a GRing.unit.
Proof.
apply/unitrP; exists (q_stair N).
by rewrite q_staircase mulrC q_staircase.
Qed.

Corollary q_stairE N : q_stair N = (q_onesub_prod N)^-1.
Proof.
apply: (mulrI (q_onesub_prod_unit N)).
by rewrite q_staircase divrr // q_onesub_prod_unit.
Qed.
