(* The Stirling-cycle exponential generating function (Stanley EC1 §1.3):    *)
(*                                                                            *)
(*    \sum_n (\sum_k c(n,k) t^k) x^n / n!  =  (1-x)^(-t)                      *)
(*                                                                            *)
(* formalized over {fps {poly rat}} (series in x with coefficients in the     *)
(* polynomial ring rat[t]), where (1-x)^(-t) is by definition                 *)
(*    fps_exp (t *: fps_log ((1-x)^-1)).                                      *)
(* Here c(n,k) = stirling_c n k counts permutations of 'I_n with k cycles.    *)
(*                                                                            *)
(* The combinatorial input is the recurrence stirling_c_rec                   *)
(* (stirling_fiber.v): c(n+1,k+1) = n c(n,k+1) + c(n,k), which says exactly   *)
(* that the row polynomials satisfy s_{n+1} = (n + t) s_n, i.e. that the      *)
(* egf satisfies the formal ODE (1-x) y' = t y with y(0) = 1 — the same      *)
(* equation satisfied by (1-x)^(-t).  This is demo #2 of                      *)
(* docs/plans/FPS_PLAN.md, exercising composition, exp/log and the OGF        *)
(* toolkit over a NON-FIELD coefficient ring.                                 *)

From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra fingroup perm.
From mathcomp Require Import boolp.
From mathcomp_fps Require Import fps fps_deriv fps_ogf fps_comp fps_explog.
From mathcomp_eulerian Require Import ordinal_reindex perm_compress descent.
From mathcomp_eulerian Require Import cycles cycles_rec stirling_fiber.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.

(* ========================================================================= *)
(* Positive naturals are invertible in rat[t]                                 *)
(* ========================================================================= *)

Lemma natU_polyrat n : (n.+1)%:R \is a @GRing.unit {poly rat}.
Proof.
rewrite -polyC_natr poly_unitE size_polyC coefC /=.
by rewrite Num.Theory.pnatr_eq0 /= unitfE Num.Theory.pnatr_eq0.
Qed.

Lemma factU_polyrat m : m`!%:R \is a @GRing.unit {poly rat}.
Proof. exact: factU natU_polyrat m. Qed.

(* ========================================================================= *)
(* Boundary values of the Stirling cycle numbers                              *)
(* ========================================================================= *)

Lemma stirling_c00 : stirling_c 0 0 = 1%N.
Proof.
rewrite /stirling_c.
have -> : [set s : {perm 'I_0} | cycle_count s == 0%N]
          = [set: {perm 'I_0}].
  apply/setP => s; rewrite !inE /cycle_count /porbits.
  suff -> : [set porbit s x | x : 'I_0] = set0 by rewrite cards0.
  by apply/setP => A; rewrite !inE; apply/negbTE/imsetP => -[[]].
by rewrite cardsT card_Sn fact0.
Qed.

(** Every permutation of a nonempty type has at least one cycle. *)
Lemma stirling_cS0 n : stirling_c n.+1 0 = 0%N.
Proof.
rewrite /stirling_c; apply/eqP; rewrite cards_eq0; apply/eqP.
apply/setP => s; rewrite !inE /cycle_count.
apply/negbTE; rewrite cards_eq0; apply/set0Pn.
by exists (porbit s ord0); apply: imset_f.
Qed.

(** A permutation of 'I_n has at most n cycles. *)
Lemma stirling_c_out n k : (n < k)%N -> stirling_c n k = 0%N.
Proof.
move=> lt_nk; rewrite /stirling_c; apply/eqP; rewrite cards_eq0; apply/eqP.
apply/setP => s; rewrite !inE; apply/negbTE/eqP => Hk.
have := cycle_count_le s; rewrite Hk card_ord.
by rewrite leqNgt lt_nk.
Qed.

(* ========================================================================= *)
(* The row polynomials s_n(t) = sum_k c(n,k) t^k                              *)
(* ========================================================================= *)

Definition stirling_pol (n : nat) : {poly rat} :=
  \sum_(k < n.+1) (stirling_c n k)%:R * 'X^k.

Lemma coef_stirling_pol n k : (stirling_pol n)`_k = (stirling_c n k)%:R.
Proof.
rewrite /stirling_pol coef_sum.
under eq_bigr => j _ do rewrite -polyC_natr coefCM coefXn.
case: (ltnP k n.+1) => [lt_kn | lt_nk].
  rewrite (bigD1 (Ordinal lt_kn)) //= eqxx mulr1 big1 ?addr0 //.
  move=> j neq_jk.
  by move: neq_jk; rewrite -val_eqE /= eq_sym => /negbTE ->; rewrite mulr0.
rewrite stirling_c_out // big1 // => j _.
have -> : (k == j :> nat) = false.
  by apply/negbTE; rewrite neq_ltn (leq_trans (ltn_ord j) lt_nk) orbT.
by rewrite mulr0.
Qed.

Lemma stirling_pol0 : stirling_pol 0 = 1.
Proof.
by rewrite /stirling_pol big_ord1 stirling_c00 expr0 mulr1.
Qed.

(** The row-polynomial recurrence: s_{n+1} = (n + t) s_n — a verbatim        *)
(* restatement of stirling_c_rec.                                            *)
Lemma stirling_pol_rec n :
  stirling_pol n.+1 = (n%:R%:P + 'X) * stirling_pol n.
Proof.
apply/polyP => k; rewrite coef_stirling_pol mulrDl coefD coefCM coefXM.
rewrite !coef_stirling_pol.
case: k => [|k] /=.
  rewrite addr0 stirling_cS0.
  case: n => [|n]; first by rewrite mul0r.
  by rewrite stirling_cS0 mulr0.
by rewrite stirling_c_rec natrD natrM.
Qed.

(* ========================================================================= *)
(* The exponential generating function                                       *)
(* ========================================================================= *)

Definition stirling_egf : {fps {poly rat}} :=
  \fps (stirling_pol n / n`!%:R) .x^n.

Lemma stirling_egf0 : stirling_egf``_0 = 1.
Proof. by rewrite /= stirling_pol0 fact0 divr1. Qed.

(** Coefficient shift under multiplication by x. *)
Lemma coef_fpsXfM (R : comNzRingType) (f : {fps R}) n :
  ('Xf * f)``_n = if n is m.+1 then f``_m else 0.
Proof.
rewrite coef_fpsM; case: n => [|m].
  by rewrite big_ord1 /= coefX /= mul0r.
rewrite big_ord_recl big_ord_recl /= !coefX /= mul0r add0r mul1r subSS subn0.
by rewrite big1 ?addr0 // => k _; rewrite coefX /= mul0r.
Qed.

(** The geometric series solves y' = y^2. *)
Lemma fps_geom_deriv (R : comUnitRingType) :
  fps_deriv (fps_geom R) = fps_geom R * fps_geom R.
Proof.
apply/fpsP => n; rewrite coef_fps_deriv coef_fpsM /=.
rewrite mulr1; under eq_bigr => k _ do rewrite mul1r.
by rewrite sumr_const card_ord.
Qed.

(** The formal ODE (1-x) S' = t S, from the row recurrence. *)
Lemma stirling_egf_ode1 :
  (1 - 'Xf) * fps_deriv stirling_egf = ('X : {poly rat}) *: stirling_egf.
Proof.
apply/fpsP => n.
rewrite mulrBl mul1r coef_fpsB coef_fpsXfM coef_fpsZ.
case: n => [|m].
  rewrite subr0 coef_fps_deriv /=.
  rewrite stirling_pol_rec stirling_pol0 mulr1 mulr0n add0r.
  rewrite mul1r (_ : 1`! = 1%N) // (_ : 0`! = 1%N) // mulr1n !divr1.
  by rewrite mul1r.
rewrite !coef_fps_deriv /=.
rewrite [(m.+2)`!]factS natrM invrM ?natU_polyrat ?factU_polyrat //.
rewrite mulrCA [m.+2%:R * _]mulrCA divrr ?natU_polyrat // mulr1.
rewrite stirling_pol_rec polyC_natr mulrDl !mulrA.
by rewrite mulrDl addrAC subrr add0r.
Qed.

(* ========================================================================= *)
(* The right-hand side (1-x)^(-t) := exp (t log (1/(1-x)))                    *)
(* ========================================================================= *)

Definition onesubX_pow_t : {fps {poly rat}} :=
  fps_exp (('X : {poly rat}) *: fps_log ((1 - 'Xf)^-1)).

Lemma onesubX_pow_t_ode1 :
  (1 - 'Xf) * fps_deriv onesubX_pow_t
  = ('X : {poly rat}) *: onesubX_pow_t.
Proof.
rewrite /onesubX_pow_t; set L := fps_log _.
have v0 : (('X : {poly rat}) *: L)``_0 = 0.
  by rewrite coef_fpsZ coef0_fps_log mulr0.
rewrite (fps_exp_deriv natU_polyrat v0) fps_derivZ.
have geom1 : ((1 - 'Xf)^-1 : {fps {poly rat}})``_0 = 1.
  by rewrite fps_inv_onesubX.
rewrite /L (fps_log_deriv natU_polyrat geom1).
rewrite invrK fps_inv_onesubX fps_geom_deriv.
rewrite -scalerAl -scalerAr; congr (_ *: _).
rewrite mulrA [(1 - 'Xf) * ((1 - 'Xf) * _)]mulrA mulrACA.
by rewrite !onesubX_mul_geom mulr1 mul1r.
Qed.

(** Both equations convert to the standard linear form y' = (t geom) y. *)
Lemma stirling_ode_convert (y : {fps {poly rat}}) :
  (1 - 'Xf) * fps_deriv y = ('X : {poly rat}) *: y ->
  fps_deriv y = (('X : {poly rat}) *: fps_geom _) * y.
Proof.
move=> H.
have := congr1 (fun z => fps_geom {poly rat} * z) H.
rewrite mulrA [fps_geom _ * (1 - 'Xf)]mulrC onesubX_mul_geom mul1r.
by rewrite -scalerAr scalerAl => ->.
Qed.

(* ========================================================================= *)
(* Stanley EC1 §1.3: the Stirling-cycle egf                                   *)
(* ========================================================================= *)

Theorem stirling_cycle_egf : stirling_egf = onesubX_pow_t.
Proof.
apply: (fps_lin_ode_uniq natU_polyrat
          (stirling_ode_convert stirling_egf_ode1)
          (stirling_ode_convert onesubX_pow_t_ode1)).
by rewrite stirling_egf0 coef0_fps_exp.
Qed.
