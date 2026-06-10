(* mathcomp_fps: formal derivative of formal power series.                   *)
(*                                                                            *)
(* Copyright 2026 the mathcomp-eulerian contributors.                         *)
(* SPDX-License-Identifier: Apache-2.0                                        *)
(*                                                                            *)
(*    fps_deriv f == the formal derivative, coefficient n is                  *)
(*                   (n+1)%:R * f``_(n+1)                                     *)
(*     fps_prim f == the formal primitive with zero constant coefficient      *)
(*                   (over a char-0 field)                                    *)
(*                                                                            *)
(* Main results:                                                              *)
(*   fps_derivM (Leibniz), fps_deriv_poly (compatibility with {poly R}),      *)
(*   fps_derivK (primitive then derivative), fps_deriv_eq0 (a series with     *)
(*   zero derivative is constant, char 0), fps_deriv_inj0 (two series with    *)
(*   the same derivative and the same constant coefficient are equal).        *)

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
(* The derivative over a commutative ring                                    *)
(* ========================================================================= *)

Section FpsDeriv.
Variable R : comNzRingType.
Implicit Types f g : {fps R}.

Definition fps_deriv f : {fps R} := \fps ((n.+1)%:R * f``_n.+1) .x^n.

Lemma coef_fps_deriv f n : (fps_deriv f)``_n = (n.+1)%:R * f``_n.+1.
Proof. by []. Qed.

Lemma fps_derivD f g : fps_deriv (f + g) = fps_deriv f + fps_deriv g.
Proof. by apply/fpsP => n /=; rewrite mulrDr. Qed.

Lemma fps_derivN f : fps_deriv (- f) = - fps_deriv f.
Proof. by apply/fpsP => n /=; rewrite mulrN. Qed.

Lemma fps_derivB f g : fps_deriv (f - g) = fps_deriv f - fps_deriv g.
Proof. by rewrite fps_derivD fps_derivN. Qed.

Lemma fps_derivZ (a : R) f : fps_deriv (a *: f) = a *: fps_deriv f.
Proof. by apply/fpsP => n /=; rewrite mulrCA. Qed.

Lemma fps_deriv0 : fps_deriv 0 = 0.
Proof. by apply/fpsP => n /=; rewrite mulr0. Qed.

Lemma fps_deriv1 : fps_deriv 1 = 0.
Proof. by apply/fpsP => n /=; rewrite mulr0. Qed.

Lemma fps_derivC (c : R) : fps_deriv (c *: 1) = 0.
Proof. by apply/fpsP => n /=; rewrite mulr0 mulr0. Qed.

Lemma fps_deriv_sum (I : Type) (r : seq I) (P : pred I)
    (F : I -> {fps R}) :
  fps_deriv (\sum_(i <- r | P i) F i) = \sum_(i <- r | P i) fps_deriv (F i).
Proof.
by elim/big_rec2: _ => [|i x f _ <-]; rewrite ?fps_deriv0 ?fps_derivD.
Qed.

(** The Leibniz rule. *)
Lemma fps_derivM f g :
  fps_deriv (f * g) = fps_deriv f * g + f * fps_deriv g.
Proof.
apply/fpsP => n.
rewrite coef_fps_deriv coef_fpsD !coef_fpsM big_distrr /=.
(* split the weight n+1 = k + (n+1-k) on each summand *)
rewrite (eq_bigr (fun k : 'I_n.+2 =>
    k%:R * (f``_k * g``_(n.+1 - k)%N)
    + (n.+1 - k)%:R * (f``_k * g``_(n.+1 - k)%N))); last first.
  move=> k _; rewrite -mulrDl -natrD.
  by rewrite subnKC // -ltnS ltn_ord.
rewrite big_split /=; congr (_ + _).
- (* first piece: reindex k -> k+1, the k = 0 term vanishes *)
  rewrite big_ord_recl /= mul0r add0r.
  apply: eq_bigr => k _.
  by rewrite /bump /= add1n subSS mulrA.
- (* second piece: the k = n+1 term vanishes *)
  rewrite big_ord_recr /= subnn mul0r addr0.
  apply: eq_bigr => k _.
  rewrite mulrCA; congr (_ * _).
  by rewrite subSn // -ltnS ltn_ord.
Qed.

(** Compatibility with the polynomial derivative. *)
Lemma fps_deriv_poly (p : {poly R}) :
  fps_deriv (poly_fps p) = poly_fps p^`().
Proof.
by apply/fpsP => n /=; rewrite coef_deriv mulr_natl.
Qed.

Lemma fps_derivX : fps_deriv 'Xf = 1 :> {fps R}.
Proof. by rewrite fps_deriv_poly derivX rmorph1. Qed.

End FpsDeriv.

(* ========================================================================= *)
(* Primitive and derivative-cancellation over a char-0 field                 *)
(* ========================================================================= *)

Section FpsDerivChar0.
Variable F : fieldType.
Hypothesis charF0 : has_pchar0 F.
Implicit Types f g : {fps F}.

Lemma natf_neq0_char0 m : (m%:R != 0 :> F) = (m != 0%N).
Proof. by have /GRing.pcharf0P -> := charF0. Qed.

Lemma natSf_neq0 m : (m.+1)%:R != 0 :> F.
Proof. by rewrite natf_neq0_char0. Qed.

Definition fps_prim f : {fps F} :=
  \fps (if n is m.+1 then f``_m / (m.+1)%:R else 0) .x^n.

Lemma coef_fps_prim0 f : (fps_prim f)``_0 = 0.
Proof. by []. Qed.

Lemma coef_fps_primS f m : (fps_prim f)``_m.+1 = f``_m / (m.+1)%:R.
Proof. by []. Qed.

(** Differentiating a primitive recovers the series. *)
Lemma fps_derivK f : fps_deriv (fps_prim f) = f.
Proof.
apply/fpsP => n; rewrite coef_fps_deriv coef_fps_primS.
by rewrite mulrC divfK // natSf_neq0.
Qed.

(** A series with zero derivative is its constant coefficient. *)
Lemma fps_deriv_eq0 f : fps_deriv f = 0 -> f = f``_0 *: 1.
Proof.
move=> /fpsP Hd; apply/fpsP => n.
case: n => [|n]; first by rewrite coef_fpsZ coef_fps1 mulr1.
have := Hd n; rewrite coef_fps_deriv coef_fps0 => /eqP.
rewrite mulf_eq0 (negbTE (natSf_neq0 n)) /= => /eqP ->.
by rewrite mulr0.
Qed.

(** Two series with the same derivative and the same constant coefficient    *)
(* are equal — the uniqueness half of the fundamental exercise.              *)
Lemma fps_deriv_inj0 f g :
  fps_deriv f = fps_deriv g -> f``_0 = g``_0 -> f = g.
Proof.
move=> Hd H0; apply/eqP; rewrite -subr_eq0; apply/eqP.
have /fps_deriv_eq0 : fps_deriv (f - g) = 0.
  by rewrite fps_derivB Hd subrr.
by rewrite coef_fpsB H0 subrr => ->; rewrite scale0r.
Qed.

End FpsDerivChar0.
