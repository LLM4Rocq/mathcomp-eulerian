(* mathcomp_fps: formal power series for combinatorics.                      *)
(*                                                                            *)
(* Copyright 2026 the mathcomp-eulerian contributors.                         *)
(* SPDX-License-Identifier: Apache-2.0                                        *)
(*                                                                            *)
(* This file defines the type {fps R} of formal power series over a ring R    *)
(* as coefficient sequences nat -> R, and equips it with mathcomp algebraic   *)
(* structures:                                                                 *)
(*       {fps R} == formal power series with coefficients in R               *)
(*        f``_n == the n-th coefficient of f                                  *)
(*      \fps E_n == the series with n-th coefficient E (n bound in E)         *)
(*   fps_trunc m f == the polynomial truncation \poly_(i < m.+1) f``_i        *)
(*    poly_fps p == a polynomial viewed as a formal power series              *)
(*           'Xf == poly_fps 'X                                               *)
(*       fps_one == 1, fps_mul == Cauchy product, fps_inv == inverse          *)
(*                                                                            *)
(* Structures: Zmodule, ComNzRing, Lmodule, Algebra (R a comNzRingType),      *)
(* ComUnitRing/ComUnitAlgebra (R a comUnitRingType) with                      *)
(*       f \is a GRing.unit <-> f``_0 \is a GRing.unit.                       *)
(*                                                                            *)
(* Design notes.                                                              *)
(* - Equality of series is genuine (Leibniz) equality, via the classical      *)
(*   axioms of mathcomp-classical (boolp): functional extensionality turns    *)
(*   coefficientwise equality (lemma [fpsP]) into equality, and gen_eqMixin / *)
(*   gen_choiceMixin provide the eqType/choiceType structures that GRing      *)
(*   requires.  This is the same axiom set used by mathcomp-analysis.         *)
(* - Ring axioms are proved by a "polynomial bootstrap": coefficient n of a   *)
(*   product only depends on coefficients <= n (lemma [coef_fpsM_trunc]), so  *)
(*   associativity and commutativity reduce to {poly R}.                      *)
(* - Inverses exist over any comUnitRingType as soon as the constant          *)
(*   coefficient is a unit (no field assumption): the coefficients of the     *)
(*   inverse are computed by the prefix recursion [fps_inv_coef].             *)
(*                                                                            *)
(* This library is self-contained over mathcomp + mathcomp-classical and      *)
(* must not import anything from the mathcomp_eulerian namespace.             *)
(*                                                                            *)
(* Design inspired by (but sharing no code with) hivert/FormalPowerSeries     *)
(* (GPL-3.0), which builds full series as inverse limits of truncations.      *)

From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import boolp.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.

Reserved Notation "{ 'fps' R }"
  (R at level 2, format "{ 'fps'  R }").
Reserved Notation "f ``_ n"
  (at level 3, n at level 2, left associativity, format "f ``_ n").
Reserved Notation "\fps E .x^ n"
  (n name, E at level 36, at level 36, format "\fps  E  .x^ n").
Reserved Notation "''Xf'" (at level 0).

(* ========================================================================= *)
(* The carrier                                                               *)
(* ========================================================================= *)

Record fps (R : Type) : Type := FPS { fpscoef : nat -> R }.

Notation "{ 'fps' R }" := (fps R) : type_scope.
Notation "f ``_ n" := (fpscoef f n) : ring_scope.
Notation "\fps E .x^ n" := (FPS (fun n => E)) : ring_scope.

HB.instance Definition _ (R : Type) := gen_eqMixin (fps R).
HB.instance Definition _ (R : Type) := gen_choiceMixin (fps R).

Section FpsExt.
Variable R : Type.

(** Coefficientwise equality is equality (uses functional extensionality). *)
Lemma fpsP (f g : {fps R}) : (forall n, f``_n = g``_n) <-> f = g.
Proof.
split=> [|-> //]; case: f => cf; case: g => cg /= H.
by congr FPS; exact/funext.
Qed.

End FpsExt.

(* ========================================================================= *)
(* Additive structure                                                        *)
(* ========================================================================= *)

Section FpsZmod.
Variable R : zmodType.
Implicit Types f g h : {fps R}.

Definition fps_zero : {fps R} := \fps 0 .x^n.
Definition fps_add f g : {fps R} := \fps (f``_n + g``_n) .x^n.
Definition fps_opp f : {fps R} := \fps (- f``_n) .x^n.

Fact fps_addA : associative fps_add.
Proof. by move=> f g h; apply/fpsP => n /=; rewrite addrA. Qed.

Fact fps_addC : commutative fps_add.
Proof. by move=> f g; apply/fpsP => n /=; rewrite addrC. Qed.

Fact fps_add0f : left_id fps_zero fps_add.
Proof. by move=> f; apply/fpsP => n /=; rewrite add0r. Qed.

Fact fps_addNf : left_inverse fps_zero fps_opp fps_add.
Proof. by move=> f; apply/fpsP => n /=; rewrite addNr. Qed.

HB.instance Definition _ :=
  GRing.isZmodule.Build {fps R} fps_addA fps_addC fps_add0f fps_addNf.

Lemma coef_fps0 n : (0 : {fps R})``_n = 0.
Proof. by []. Qed.

Lemma coef_fpsD f g n : (f + g)``_n = f``_n + g``_n.
Proof. by []. Qed.

Lemma coef_fpsN f n : (- f)``_n = - f``_n.
Proof. by []. Qed.

Lemma coef_fpsB f g n : (f - g)``_n = f``_n - g``_n.
Proof. by []. Qed.

Lemma coef_fps_sum (I : Type) (r : seq I) (P : pred I)
    (F : I -> {fps R}) (n : nat) :
  (\sum_(i <- r | P i) F i)``_n = \sum_(i <- r | P i) (F i)``_n.
Proof. by elim/big_rec2: _ => // i x f _ <-. Qed.

End FpsZmod.

(* ========================================================================= *)
(* Multiplicative structure (Cauchy product), via polynomial bootstrap       *)
(* ========================================================================= *)

Section FpsRing.
Variable R : comNzRingType.
Implicit Types f g h : {fps R}.

Definition fps_one : {fps R} := \fps ((n == 0%N)%:R) .x^n.

Definition fps_mul f g : {fps R} :=
  \fps (\sum_(k < n.+1) f``_k * g``_(n - k)%N) .x^n.

(** Polynomial truncation: the first m+1 coefficients. *)
Definition fps_trunc m f : {poly R} := \poly_(i < m.+1) f``_i.

Lemma coef_fps_trunc m f i :
  (fps_trunc m f)`_i = if (i <= m)%N then f``_i else 0.
Proof. by rewrite coef_poly ltnS. Qed.

(** The bootstrap lemma: coefficient n of a product only involves            *)
(* coefficients <= n, hence factors through any truncation of order >= n.   *)
Lemma coef_fpsM_trunc m f g n :
  (n <= m)%N -> (fps_mul f g)``_n = (fps_trunc m f * fps_trunc m g)`_n.
Proof.
move=> le_nm; rewrite coefM /=; apply: eq_bigr => k _.
rewrite !coef_fps_trunc.
have -> : (k <= m)%N by rewrite (leq_trans _ le_nm) // -ltnS ltn_ord.
by have -> : (n - k <= m)%N by rewrite (leq_trans _ le_nm) // leq_subr.
Qed.

(** Coefficient n of a polynomial product only depends on the coefficients   *)
(* <= n of each factor.                                                      *)
Lemma coefM_eqr (p q q' : {poly R}) n :
  (forall i, (i <= n)%N -> q`_i = q'`_i) -> (p * q)`_n = (p * q')`_n.
Proof.
by move=> Hq; rewrite !coefM; apply: eq_bigr => k _; rewrite Hq // leq_subr.
Qed.

Lemma coefM_eql (p p' q : {poly R}) n :
  (forall i, (i <= n)%N -> p`_i = p'`_i) -> (p * q)`_n = (p' * q)`_n.
Proof.
by move=> Hp; rewrite ![_ * q]mulrC; apply: coefM_eqr.
Qed.

Fact fps_mulA : associative fps_mul.
Proof.
move=> f g h; apply/fpsP => n.
rewrite !(coef_fpsM_trunc _ _ (leqnn n)).
transitivity ((fps_trunc n f * (fps_trunc n g * fps_trunc n h))`_n).
  apply: coefM_eqr => i le_in.
  by rewrite coef_fps_trunc le_in (coef_fpsM_trunc _ _ le_in).
rewrite mulrA; apply/esym.
apply: coefM_eql => i le_in.
by rewrite coef_fps_trunc le_in (coef_fpsM_trunc _ _ le_in).
Qed.

Fact fps_mulC : commutative fps_mul.
Proof.
move=> f g; apply/fpsP => n.
by rewrite !(coef_fpsM_trunc _ _ (leqnn n)) mulrC.
Qed.

Lemma fps_trunc_one m : fps_trunc m fps_one = 1.
Proof.
apply/polyP => i; rewrite coef_fps_trunc coef1 /=.
case: leqP => // lt_mi.
by rewrite (gtn_eqF (leq_ltn_trans (leq0n m) lt_mi)).
Qed.

Fact fps_mul1f : left_id fps_one fps_mul.
Proof.
move=> f; apply/fpsP => n.
rewrite (coef_fpsM_trunc _ _ (leqnn n)) fps_trunc_one mul1r.
by rewrite coef_fps_trunc leqnn.
Qed.

Fact fps_mulDl : left_distributive fps_mul +%R.
Proof.
move=> f g h; apply/fpsP => n /=; rewrite -big_split /=.
by apply: eq_bigr => k _; rewrite mulrDl.
Qed.

Fact fps_oner_neq0 : fps_one != 0 :> {fps R}.
Proof.
apply/eqP => /fpsP/(_ 0%N)/eqP /=.
by rewrite oner_eq0.
Qed.

HB.instance Definition _ :=
  GRing.Zmodule_isComNzRing.Build {fps R}
    fps_mulA fps_mulC fps_mul1f fps_mulDl fps_oner_neq0.

Lemma coef_fps1 n : (1 : {fps R})``_n = (n == 0%N)%:R.
Proof. by []. Qed.

Lemma coef_fpsM f g n : (f * g)``_n = \sum_(k < n.+1) f``_k * g``_(n - k)%N.
Proof. by []. Qed.

(** Coefficient 0 is a ring morphism. *)
Lemma coef0_fpsM f g : (f * g)``_0 = f``_0 * g``_0.
Proof. by rewrite coef_fpsM big_ord1. Qed.

(* ----------------------------------------------------------------------- *)
(* Module and algebra structure over R                                       *)
(* ----------------------------------------------------------------------- *)

Definition fps_scale (a : R) f : {fps R} := \fps (a * f``_n) .x^n.

Fact fps_scaleA a b f : fps_scale a (fps_scale b f) = fps_scale (a * b) f.
Proof. by apply/fpsP => n /=; rewrite mulrA. Qed.

Fact fps_scale1f : left_id 1 fps_scale.
Proof. by move=> f; apply/fpsP => n /=; rewrite mul1r. Qed.

Fact fps_scaleDr a : {morph fps_scale a : f g / f + g}.
Proof. by move=> f g; apply/fpsP => n /=; rewrite mulrDr. Qed.

Fact fps_scaleDl f : {morph fps_scale^~ f : a b / a + b}.
Proof. by move=> a b; apply/fpsP => n /=; rewrite mulrDl. Qed.

HB.instance Definition _ :=
  GRing.Zmodule_isLmodule.Build R {fps R}
    fps_scaleA fps_scale1f fps_scaleDr fps_scaleDl.

Lemma coef_fpsZ a f n : (a *: f)``_n = a * f``_n.
Proof. by []. Qed.

Fact fps_scaleAl a f g : a *: (f * g) = (a *: f) * g.
Proof.
apply/fpsP => n; rewrite coef_fpsZ !coef_fpsM big_distrr /=.
by apply: eq_bigr => k _; rewrite mulrA.
Qed.

HB.instance Definition _ :=
  GRing.Lmodule_isLalgebra.Build R {fps R} fps_scaleAl.

Fact fps_scaleAr a f g : a *: (f * g) = f * (a *: g).
Proof.
apply/fpsP => n; rewrite coef_fpsZ !coef_fpsM big_distrr /=.
by apply: eq_bigr => k _; rewrite mulrCA.
Qed.

HB.instance Definition _ :=
  GRing.Lalgebra_isAlgebra.Build R {fps R} fps_scaleAr.

End FpsRing.

(* ========================================================================= *)
(* The polynomial embedding                                                  *)
(* ========================================================================= *)

Section PolyFps.
Variable R : comNzRingType.
Implicit Types p q : {poly R}.

Definition poly_fps p : {fps R} := \fps (p`_n) .x^n.

Lemma coef_poly_fps p n : (poly_fps p)``_n = p`_n.
Proof. by []. Qed.

Lemma poly_fps_inj : injective poly_fps.
Proof. by move=> p q /fpsP H; apply/polyP => i; have := H i. Qed.

Fact poly_fps_is_zmod_morphism : zmod_morphism poly_fps.
Proof. by move=> p q; apply/fpsP => n /=; rewrite coefB. Qed.

Fact poly_fps_is_monoid_morphism : monoid_morphism poly_fps.
Proof.
split=> [|p q]; apply/fpsP => n /=; first by rewrite coef1.
by rewrite coefM.
Qed.

HB.instance Definition _ :=
  GRing.isZmodMorphism.Build {poly R} {fps R} poly_fps
    poly_fps_is_zmod_morphism.
HB.instance Definition _ :=
  GRing.isMonoidMorphism.Build {poly R} {fps R} poly_fps
    poly_fps_is_monoid_morphism.

Lemma poly_fpsC (c : R) : poly_fps c%:P = c *: 1.
Proof.
apply/fpsP => n; rewrite coef_poly_fps coefC coef_fpsZ coef_fps1.
by case: n => [|n]; rewrite ?mulr1 ?mulr0.
Qed.

End PolyFps.

Notation "''Xf'" := (poly_fps 'X) : ring_scope.

(* ========================================================================= *)
(* Units: f is invertible iff its constant coefficient is                    *)
(* ========================================================================= *)

Section FpsUnitRing.
Variable R : comUnitRingType.
Implicit Types f g : {fps R}.

(** Prefix of the inverse-coefficient sequence: [inv_pref c n] computes      *)
(* [:: i_0; ...; i_n] where i_0 = c_0^-1 and                                  *)
(* i_{m+1} = - c_0^-1 * \sum_(k <= m) c_{m+1-k} * i_k.                        *)
Fixpoint inv_pref (c : nat -> R) (n : nat) : seq R :=
  if n is m.+1 then
    let s := inv_pref c m in
    rcons s (- (c 0%N)^-1 * \sum_(k < m.+1) c (m.+1 - k)%N * s`_k)
  else [:: (c 0%N)^-1].

Lemma size_inv_pref c n : size (inv_pref c n) = n.+1.
Proof. by elim: n => //= n IHn; rewrite size_rcons IHn. Qed.

Definition fps_inv_coef (c : nat -> R) (n : nat) : R := (inv_pref c n)`_n.

Lemma inv_prefE c n m :
  (m <= n)%N -> (inv_pref c n)`_m = fps_inv_coef c m.
Proof.
elim: n => [|n IHn]; first by rewrite leqn0 => /eqP ->.
rewrite leq_eqVlt => /predU1P[-> //|lt_mn].
by rewrite /= nth_rcons size_inv_pref lt_mn IHn // -ltnS.
Qed.

Lemma fps_inv_coef0 c : fps_inv_coef c 0 = (c 0%N)^-1.
Proof. by []. Qed.

Lemma fps_inv_coefS c m :
  fps_inv_coef c m.+1
  = - (c 0%N)^-1 * \sum_(k < m.+1) c (m.+1 - k)%N * fps_inv_coef c k.
Proof.
rewrite /fps_inv_coef /= nth_rcons size_inv_pref ltnn eqxx; congr (_ * _).
by apply: eq_bigr => k _; rewrite inv_prefE // -ltnS ltn_ord.
Qed.

Definition fps_unit : pred {fps R} := fun f => f``_0 \is a GRing.unit.

Definition fps_inv f : {fps R} :=
  if f``_0 \is a GRing.unit then \fps (fps_inv_coef (fpscoef f) n) .x^n
  else f.

Fact fps_mulVf : {in fps_unit, left_inverse 1 fps_inv *%R}.
Proof.
move=> f u0; apply/fpsP => n.
have u0' : f``_0 \is a GRing.unit by exact: u0.
rewrite coef_fpsM coef_fps1 /fps_inv u0' /=.
case: n => [|m] /=.
  by rewrite big_ord1 subnn fps_inv_coef0 mulVr.
rewrite big_ord_recr /= subnn fps_inv_coefS.
have -> : (- (f``_0)^-1 * \sum_(k < m.+1) f``_(m.+1 - k)%N
             * fps_inv_coef (fpscoef f) k) * f``_0
          = - \sum_(k < m.+1) f``_(m.+1 - k)%N * fps_inv_coef (fpscoef f) k.
  by rewrite mulrC mulrA mulrN mulrV // mulN1r.
apply/eqP; rewrite subr_eq0; apply/eqP.
by apply: eq_bigr => k _; rewrite mulrC.
Qed.

Fact fps_unitP f g : g * f = 1 -> fps_unit f.
Proof.
move/fpsP/(_ 0%N); rewrite coef0_fpsM coef_fps1 /= => Hgf.
by apply/unitrP; exists g``_0; rewrite Hgf mulrC Hgf.
Qed.

Fact fps_inv_out : {in [predC fps_unit], fps_inv =1 id}.
Proof.
move=> f; rewrite inE /= => nu.
have nu' : (f``_0 \is a GRing.unit) = false by apply/negbTE; exact: nu.
by rewrite /fps_inv nu'.
Qed.

HB.instance Definition _ :=
  GRing.ComNzRing_hasMulInverse.Build {fps R}
    fps_mulVf fps_unitP fps_inv_out.

(** The headline characterization of units. *)
Lemma fps_unitE f : (f \is a GRing.unit) = (f``_0 \is a GRing.unit).
Proof. by []. Qed.

End FpsUnitRing.

(* ========================================================================= *)
(* Sanity: the geometric series                                              *)
(* ========================================================================= *)

Section Geometric.
Variable R : comUnitRingType.

(** The all-ones series 1 + x + x^2 + ... *)
Definition fps_geom : {fps R} := \fps 1 .x^n.

Lemma coef_fps_onesubX n :
  (1 - 'Xf : {fps R})``_n = (n == 0%N)%:R - (n == 1%N)%:R.
Proof. by rewrite coef_fpsB coef_fps1 coef_poly_fps coefX. Qed.

(** Kronecker-delta summation helper. *)
Let sum_delta m j : (j < m)%N ->
  \sum_(k < m) (((k : nat) == j)%:R : R) = 1.
Proof.
move=> lt_jm; rewrite (bigD1 (Ordinal lt_jm)) //= eqxx big1 ?addr0 //.
by move=> k; rewrite -val_eqE /= => /negbTE ->.
Qed.

Lemma onesubX_mul_geom : (1 - 'Xf) * fps_geom = 1 :> {fps R}.
Proof.
apply/fpsP => n; rewrite coef_fpsM coef_fps1.
rewrite (eq_bigr (fun k : 'I_n.+1 =>
    ((k : nat) == 0%N)%:R - ((k : nat) == 1%N)%:R)); last first.
  by move=> k _; rewrite coef_fps_onesubX mulr1.
rewrite sumrB sum_delta //.
case: n => [|m] /=.
  by rewrite big_ord1 /= subr0.
by rewrite sum_delta // subrr.
Qed.

Lemma fps_onesubX_unit : (1 - 'Xf : {fps R}) \is a GRing.unit.
Proof.
by rewrite fps_unitE coef_fps_onesubX /= subr0 unitr1.
Qed.

(** The acceptance test: the inverse of 1 - x is the geometric series. *)
Lemma fps_inv_onesubX : (1 - 'Xf : {fps R})^-1 = fps_geom.
Proof.
apply: (mulrI fps_onesubX_unit).
by rewrite mulrV ?fps_onesubX_unit // onesubX_mul_geom.
Qed.

End Geometric.
