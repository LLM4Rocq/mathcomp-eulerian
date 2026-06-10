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
(* and the FULL identity [carlitz], combining the q-staircase with the        *)
(* q-Worpitzky identity (qworpitzky.v, itself powered by the q-Eulerian       *)
(* insertion recurrence of qeul_rec.v):                                       *)
(*                                                                            *)
(*    carlitz : (\sum_m ([m+1]_q)^(n+1) x^m) * \prod_(i < n+2) (1 - q^i x)   *)
(*              = q_eul_pol n.                                                *)
(*                                                                            *)
(* Note Z[q] is not a field: the inverses exist by the mathcomp_fps unit      *)
(* theory (constant coefficient 1).                                           *)

From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra fingroup perm.
From mathcomp Require Import boolp.
From mathcomp_fps Require Import fps fps_ogf.
From mathcomp_eulerian Require Import ordinal_reindex perm_compress descent.
From mathcomp_eulerian Require Import eulerian reflection inversions.
From mathcomp_eulerian Require Import qfact qeul qbin qeul_rec qworpitzky.

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

(* ========================================================================= *)
(* Carlitz's q-analogue of Stanley §1.4                                       *)
(* ========================================================================= *)

(** The OGF of the (n+1)-st powers of the q-integers: coefficient m is        *)
(* ([m+1]_q)^(n+1), a polynomial in q.                                        *)
Definition q_pow_ogf (n : nat) : {fps {poly int}} :=
  \fps (q_int m.+1 ^+ n.+1) .x^m.

(** Division form: q_eul_pol n times the q-staircase series.  Coefficient-    *)
(* wise this is exactly the q-Worpitzky identity, padded on both sides.       *)
Theorem carlitz_div n :
  poly_fps (q_eul_pol n) * q_stair n.+1 = q_pow_ogf n.
Proof.
apply/fpsP => m; rewrite coef_fpsM.
under eq_bigr => j _ do rewrite coef_poly_fps coef_q_eul_pol /=.
rewrite [(q_pow_ogf n)``_m]/= q_worpitzky.
pose G j := q_eulerian n j * qbin (m + n.+1 - j)%N n.+1.
have sumF (q : nat) (H : nat -> {poly int}) : (q < (m + n).+2)%N ->
    (forall j, (q < j)%N -> H j = 0) ->
    \sum_(j < q.+1) H j = \sum_(j < (m + n).+2) H j.
  move=> le_q Hz; rewrite (big_ord_widen _ H le_q) big_mkcond /=.
  apply: eq_bigr => j _; case: ltnP => // lt_qj.
  by rewrite Hz.
under eq_bigr => i _ do
  rewrite (addnBAC _ (ltn_ord i : (i <= m)%N)).
rewrite (sumF m G); first last.
- move=> j lt_mj; rewrite /G qbin_small ?mulr0 //.
  rewrite ltnS (leq_trans (leq_sub2l (m + n.+1) lt_mj)) //.
  by rewrite addnS subSS addnC addnK.
- by rewrite ltnS (leq_trans (leq_addr n m)) ?leqnSn.
rewrite (sumF n G) //; first last.
- by move=> j lt_nj; rewrite /G q_eulerian_out_of_range // mul0r.
by rewrite !ltnS (leq_trans (leq_addl m n)) ?leqnSn.
Qed.

(** Multiplied-out form (no division): Carlitz's q-analogue of Stanley §1.4.  *)
Theorem carlitz n :
  q_pow_ogf n * q_onesub_prod n.+1 = poly_fps (q_eul_pol n).
Proof.
by rewrite -carlitz_div -mulrA [q_stair _ * _]mulrC q_staircase mulr1.
Qed.

(** Display form with the explicit inverse of the Carlitz denominator. *)
Corollary carlitz_inv n :
  q_pow_ogf n = poly_fps (q_eul_pol n) / q_onesub_prod n.+1.
Proof. by rewrite -q_stairE carlitz_div. Qed.
