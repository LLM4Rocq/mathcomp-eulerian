(* mathcomp_fps: composition of formal power series.                         *)
(*                                                                            *)
(* Copyright 2026 the mathcomp-eulerian contributors.                         *)
(* SPDX-License-Identifier: Apache-2.0                                        *)
(*                                                                            *)
(*    fps_comp f g == the substitution f(g(x)), defined coefficientwise by    *)
(*                    (f \o g)``_n = \sum_(k <= n) f``_k * (g^k)``_n.         *)
(*                    The formula is meaningful when g``_0 = 0 (the sum       *)
(*                    truncates by the valuation lemma coef_fpsXn_small);     *)
(*                    all structural lemmas carry that hypothesis.            *)
(*                                                                            *)
(* Main results (g``_0 = 0 throughout):                                       *)
(*   fps_compD/Z/N/0/1/C : additivity and constants (hypothesis-free)        *)
(*   fps_compX  : 'Xf \o g = g                                                *)
(*   fps_compM  : (f1 * f2) \o g = (f1 \o g) * (f2 \o g)                      *)
(*   fps_compV  : f^-1 \o g = (f \o g)^-1 for f a unit                        *)
(*   fps_comp_deriv (chain rule) :                                            *)
(*       (f \o g)' = (f' \o g) * g'                                           *)
(*                                                                            *)
(* Proof method: the same polynomial bootstrap as fps.v — coefficient n of   *)
(* f \o g factors through the degree-n truncations and {poly R}'s \Po         *)
(* (coef_fps_comp_trunc), so multiplicativity is inherited from comp_polyM    *)
(* and the chain rule reduces by poly_ind to the Leibniz rule.                *)

From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import boolp.
From mathcomp_fps Require Import fps fps_deriv.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.

Section FpsComp.
Variable R : comNzRingType.
Implicit Types f g h : {fps R}.

Definition fps_comp f g : {fps R} :=
  \fps (\sum_(k < n.+1) f``_k * (g ^+ k)``_n) .x^n.

Lemma coef_fps_comp f g n :
  (fps_comp f g)``_n = \sum_(k < n.+1) f``_k * (g ^+ k)``_n.
Proof. by []. Qed.

(* ----------------------------------------------------------------------- *)
(* Valuation: powers of a series with zero constant term                     *)
(* ----------------------------------------------------------------------- *)

Lemma coef_fpsXn_small f k n :
  f``_0 = 0 -> (n < k)%N -> (f ^+ k)``_n = 0.
Proof.
move=> f0; elim: k n => [|k IHk] n // lt_nk.
rewrite exprS coef_fpsM big1 // => j _.
case: (posnP (val j)) => [-> | jpos]; first by rewrite f0 mul0r.
rewrite IHk ?mulr0 //.
have npos : (0 < n)%N := leq_trans jpos (ltnSE (ltn_ord j)).
by rewrite (leq_trans _ (ltnSE lt_nk)) // ltn_subrL npos jpos.
Qed.

(* ----------------------------------------------------------------------- *)
(* Power bootstrap: coefficients of powers through truncations               *)
(* ----------------------------------------------------------------------- *)

Lemma coef_fpsXn_trunc m f k n : (n <= m)%N ->
  (f ^+ k)``_n = ((fps_trunc m f) ^+ k)`_n.
Proof.
elim: k n => [|k IHk] n le_nm; first by rewrite !expr0 coef_fps1 coef1.
rewrite !exprS.
have -> : (f * f ^+ k)``_n = (fps_trunc m f * fps_trunc m (f ^+ k))`_n.
  exact: coef_fpsM_trunc.
apply: coefM_eqr => i le_in.
rewrite coef_fps_trunc (leq_trans le_in le_nm) IHk //.
exact: leq_trans le_in le_nm.
Qed.

(* Poly-level valuation, transferred through poly_fps. *)
Lemma coef_polyXn_small (q : {poly R}) k n :
  q`_0 = 0 -> (n < k)%N -> (q ^+ k)`_n = 0.
Proof.
move=> q0 lt_nk.
have := coef_fpsXn_small (f := poly_fps q) (k := k) (n := n).
by rewrite coef_poly_fps -rmorphXn coef_poly_fps => ->.
Qed.

(* \Po coefficient over a padded index range. *)
Lemma coef_comp_poly_wide (p q : {poly R}) (M n : nat) :
  (size p <= M)%N ->
  (p \Po q)`_n = \sum_(i < M) p`_i * (q ^+ i)`_n.
Proof.
move=> le_pM; rewrite coef_comp_poly.
rewrite (big_ord_widen M (fun i => p`_i * (q ^+ i)`_n) le_pM).
rewrite big_mkcond /=; apply: eq_bigr => i _.
case: ltnP => // le_szp.
by rewrite nth_default ?mul0r.
Qed.

(* Coefficient n of p \Po q only depends on p's coefficients <= n,           *)
(* provided q has zero constant term.                                        *)
Lemma coef_comp_poly_eqp (p p' q : {poly R}) n : q`_0 = 0 ->
  (forall i, (i <= n)%N -> p`_i = p'`_i) ->
  (p \Po q)`_n = (p' \Po q)`_n.
Proof.
move=> q0 eq_pp'; pose M := maxn (size p) (size p').
rewrite (@coef_comp_poly_wide p q M n (leq_maxl _ _)).
rewrite (@coef_comp_poly_wide p' q M n (leq_maxr _ _)).
apply: eq_bigr => i _.
case: (leqP i n) => [le_in | lt_ni]; first by rewrite eq_pp'.
by rewrite coef_polyXn_small // !mulr0.
Qed.

(* ----------------------------------------------------------------------- *)
(* THE bridge: composition through truncations                               *)
(* ----------------------------------------------------------------------- *)

Lemma coef_fps_comp_trunc m f g n : g``_0 = 0 -> (n <= m)%N ->
  (fps_comp f g)``_n = ((fps_trunc m f) \Po (fps_trunc m g))`_n.
Proof.
move=> g0 le_nm.
have q0 : (fps_trunc m g)`_0 = 0 by rewrite coef_fps_trunc leq0n g0.
pose M := maxn (size (fps_trunc m f)) n.+1.
rewrite (@coef_comp_poly_wide (fps_trunc m f) (fps_trunc m g) M n
           (leq_maxl _ _)).
rewrite coef_fps_comp.
rewrite (big_ord_widen M (fun k => f``_k * (g ^+ k)``_n) (leq_maxr _ _)).
rewrite big_mkcond /=; apply: eq_bigr => i _.
case: ltnP => [lt_in1 | lt_ni].
  rewrite coef_fps_trunc (leq_trans _ le_nm) -1?ltnS //.
  by rewrite (coef_fpsXn_trunc _ _ le_nm).
rewrite coef_polyXn_small // mulr0 //.
Qed.

(* ----------------------------------------------------------------------- *)
(* Additive and constant laws (no hypothesis needed)                         *)
(* ----------------------------------------------------------------------- *)

Lemma fps_compD f1 f2 g :
  fps_comp (f1 + f2) g = fps_comp f1 g + fps_comp f2 g.
Proof.
apply/fpsP => n; rewrite coef_fpsD !coef_fps_comp -big_split /=.
by apply: eq_bigr => k _; rewrite mulrDl.
Qed.

Lemma fps_compZ (c : R) f g :
  fps_comp (c *: f) g = c *: fps_comp f g.
Proof.
apply/fpsP => n; rewrite coef_fpsZ !coef_fps_comp big_distrr /=.
by apply: eq_bigr => k _; rewrite mulrA.
Qed.

Lemma fps_compN f g : fps_comp (- f) g = - fps_comp f g.
Proof.
apply/fpsP => n; rewrite coef_fpsN !coef_fps_comp -sumrN /=.
by apply: eq_bigr => k _; rewrite mulNr.
Qed.

Lemma fps_comp0 g : fps_comp 0 g = 0.
Proof.
by apply/fpsP => n; rewrite coef_fps_comp big1 // => k _; rewrite mul0r.
Qed.

Lemma fps_comp1 g : fps_comp 1 g = 1.
Proof.
apply/fpsP => n; rewrite coef_fps_comp big_ord_recl /=.
by rewrite mul1r big1 ?addr0 // => k _; rewrite mul0r.
Qed.

Lemma fps_compC (c : R) g : fps_comp (c *: 1) g = c *: 1.
Proof. by rewrite fps_compZ fps_comp1. Qed.

Lemma coef0_fps_comp f g : (fps_comp f g)``_0 = f``_0.
Proof.
by rewrite coef_fps_comp big_ord1 expr0 coef_fps1 mulr1.
Qed.

(* ----------------------------------------------------------------------- *)
(* Identity, multiplicativity, inverses                                      *)
(* ----------------------------------------------------------------------- *)

Lemma fps_compX g : g``_0 = 0 -> fps_comp 'Xf g = g.
Proof.
move=> g0; apply/fpsP => n; rewrite coef_fps_comp.
case: n => [|n].
  by rewrite big_ord1 /= coefX /= mul0r g0.
rewrite big_ord_recl big_ord_recl /= !coefX /=.
rewrite mul0r add0r expr1 mul1r big1 ?addr0 // => k _.
by rewrite coefX /= mul0r.
Qed.

Lemma fps_compM f1 f2 g : g``_0 = 0 ->
  fps_comp (f1 * f2) g = fps_comp f1 g * fps_comp f2 g.
Proof.
move=> g0; apply/fpsP => n.
rewrite (coef_fps_comp_trunc _ g0 (leqnn n)).
have q0 : (fps_trunc n g)`_0 = 0 by rewrite coef_fps_trunc leq0n g0.
transitivity (((fps_trunc n f1 * fps_trunc n f2) \Po fps_trunc n g)`_n).
  apply: coef_comp_poly_eqp => // i le_in.
  by rewrite coef_fps_trunc le_in (coef_fpsM_trunc _ _ le_in).
rewrite comp_polyM (coef_fpsM_trunc _ _ (leqnn n)) !coefM.
apply: eq_bigr => i _; congr (_ * _).
  rewrite coef_fps_trunc -ltnS ltn_ord.
  by rewrite (coef_fps_comp_trunc _ g0 (ltnSE (ltn_ord i))).
rewrite coef_fps_trunc leq_subr.
by rewrite (coef_fps_comp_trunc _ g0 (leq_subr i n)).
Qed.

(* ----------------------------------------------------------------------- *)
(* The chain rule                                                            *)
(* ----------------------------------------------------------------------- *)

(** Coefficient n of f \o g only sees f's coefficients <= n. *)
Lemma fps_comp_coef_eqf f f' g n :
  (forall i, (i <= n)%N -> f``_i = f'``_i) ->
  (fps_comp f g)``_n = (fps_comp f' g)``_n.
Proof.
move=> eq_ff'; rewrite !coef_fps_comp; apply: eq_bigr => k _.
by rewrite eq_ff' // -ltnS ltn_ord.
Qed.

(** The chain rule for polynomial heads, by induction on the polynomial. *)
Lemma fps_comp_deriv_poly (p : {poly R}) g : g``_0 = 0 ->
  fps_deriv (fps_comp (poly_fps p) g)
  = fps_comp (fps_deriv (poly_fps p)) g * fps_deriv g.
Proof.
move=> g0; elim/poly_ind: p => [|p c IHp].
  by rewrite rmorph0 fps_comp0 !fps_deriv0 fps_comp0 mul0r.
rewrite rmorphD rmorphM /= poly_fpsC.
rewrite fps_compD fps_compM // fps_compX // fps_compC.
rewrite fps_derivD fps_derivC addr0 fps_derivM IHp.
rewrite [in RHS]fps_derivD fps_derivC addr0 [in RHS]fps_derivM.
rewrite fps_derivX mulr1 fps_compD fps_compM // fps_compX // mulrDl.
by rewrite mulrAC.
Qed.

(** The chain rule, by reduction to polynomial heads: coefficient n of      *)
(* either side only sees f's coefficients up to n+1.                         *)
Theorem fps_comp_deriv f g : g``_0 = 0 ->
  fps_deriv (fps_comp f g)
  = fps_comp (fps_deriv f) g * fps_deriv g.
Proof.
move=> g0; apply/fpsP => n.
pose P : {fps R} := poly_fps (fps_trunc n.+1 f).
have eqf i : (i <= n.+1)%N -> f``_i = P``_i.
  by move=> le_i; rewrite /P coef_poly_fps coef_fps_trunc le_i.
transitivity ((fps_deriv (fps_comp P g))``_n).
  rewrite !coef_fps_deriv; congr (_ * _).
  exact: fps_comp_coef_eqf eqf.
rewrite /P fps_comp_deriv_poly //.
rewrite !coef_fpsM; apply: eq_bigr => a _; congr (_ * _).
apply: fps_comp_coef_eqf => i le_ia.
rewrite !coef_fps_deriv; congr (_ * _).
apply/esym/eqf.
by rewrite ltnS (leq_trans le_ia) // -ltnS ltn_ord.
Qed.

End FpsComp.

(* ========================================================================= *)
(* Units and inverses under composition                                      *)
(* ========================================================================= *)

Section FpsCompUnit.
Variable R : comUnitRingType.
Implicit Types f g : {fps R}.

Lemma fps_comp_unit f g :
  (fps_comp f g \is a GRing.unit) = (f \is a GRing.unit).
Proof. by rewrite !fps_unitE coef0_fps_comp. Qed.

Lemma fps_compV f g : g``_0 = 0 -> f \is a GRing.unit ->
  fps_comp (f^-1) g = (fps_comp f g)^-1.
Proof.
move=> g0 fU.
have cU : fps_comp f g \is a GRing.unit by rewrite fps_comp_unit.
apply: (mulrI cU).
by rewrite -fps_compM // !divrr // fps_comp1.
Qed.

End FpsCompUnit.
