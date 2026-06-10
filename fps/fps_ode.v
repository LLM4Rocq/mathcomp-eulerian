(* mathcomp_fps: uniqueness of solutions of formal quadratic ODEs.           *)
(*                                                                            *)
(* Copyright 2026 the mathcomp-eulerian contributors.                         *)
(* SPDX-License-Identifier: Apache-2.0                                        *)
(*                                                                            *)
(* Over a char-0 field, a formal power series solution of the quadratic       *)
(* differential equation                                                       *)
(*       2 y' = c + y^2                                                       *)
(* is determined by its constant coefficient (fps_quad_ode_uniq):             *)
(* coefficient n+1 of a solution is computed from coefficients <= n, since    *)
(* 2(n+1) is invertible.  This is the "holonomic" uniqueness argument used    *)
(* for sec + tan (and, classically, for Catalan-style equations).             *)

From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import boolp.
From mathcomp_fps Require Import fps fps_deriv.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.

Section FpsOde.
Variable F : fieldType.
Hypothesis charF0 : has_pchar0 F.
Implicit Types c f g : {fps F}.

(** Solutions of 2 y' = c + y^2 are determined by their constant term. *)
Lemma fps_quad_ode_uniq c f g :
  2%:R *: fps_deriv f = c + f ^+ 2 ->
  2%:R *: fps_deriv g = c + g ^+ 2 ->
  f``_0 = g``_0 -> f = g.
Proof.
move=> Hf Hg H0; apply/fpsP => n.
elim/ltn_ind: n => -[|n] IH //.
have IHle k : (k <= n)%N -> f``_k = g``_k.
  by move=> le_kn; apply: IH; rewrite ltnS.
have Hfn := congr1 (fun h : {fps F} => h``_n) Hf.
have Hgn := congr1 (fun h : {fps F} => h``_n) Hg.
rewrite coef_fpsZ coef_fps_deriv mulrA in Hfn.
rewrite coef_fpsZ coef_fps_deriv mulrA in Hgn.
have Hsum : (f ^+ 2)``_n = (g ^+ 2)``_n.
  rewrite !expr2 !coef_fpsM; apply: eq_bigr => k _.
  by rewrite !IHle // ?leq_subr // -ltnS ltn_ord.
have Hne : 2%:R * (n.+1)%:R != 0 :> F.
  by rewrite mulf_neq0 // (natf_neq0_char0 charF0).
apply: (mulfI Hne).
by rewrite Hfn Hgn !coef_fpsD Hsum.
Qed.

End FpsOde.
