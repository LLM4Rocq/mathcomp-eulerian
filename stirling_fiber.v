(* Stirling cycle-number recurrence: insert_after construction.

   This file builds on cycles.v and cycles_rec.v.  It defines the
   "insert ord_max into s's cycle right after j0" operation
   [insert_after j0 s : {perm 'I_n.+1}] that splices ord_max into the
   j0-cycle of [s], preserving cycle count.

   We use Option B from STIRLING_FIBER_PLAN.md (no s^-1):
     insert_after j0 s ord_max          = lift ord_max (s j0)
     insert_after j0 s (lift ord_max j0)= ord_max
     insert_after j0 s (lift ord_max k) = lift ord_max (s k)   (k != j0)

   Cycle picture: an s-cycle p1 -> p2 -> ... -> pr -> p1 with j0 = pi
   becomes p1 -> ... -> j0 -> ord_max -> s j0 -> ... -> p1 (widened).
*)
From mathcomp Require Import all_ssreflect fingroup perm.
From mathcomp_eulerian Require Import ordinal_reindex perm_compress descent
                                       cycles cycles_rec.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* ========================================================================= *)
(* §A. The insert_after construction                                          *)
(* ========================================================================= *)

Section InsertAfter.
Variable n : nat.

Definition insert_after_fun (j0 : 'I_n) (s : {perm 'I_n}) (x : 'I_n.+1) :
  'I_n.+1 :=
  match unlift ord_max x with
  | None     => lift ord_max (s j0)
  | Some k   => if k == j0 then ord_max
                else lift ord_max (s k)
  end.

Lemma insert_after_fun_inj j0 s : injective (insert_after_fun j0 s).
Proof.
move=> x y.
rewrite /insert_after_fun.
case: (unliftP ord_max x) => [kx -> | ->];
case: (unliftP ord_max y) => [ky -> | ->];
rewrite ?liftK ?unlift_none.
- (* Some, Some *)
  case: (boolP (kx == j0)) => [/eqP Ekx | kx_ne];
  case: (boolP (ky == j0)) => [/eqP Eky | ky_ne].
  + by move=> _; rewrite Ekx Eky.
  + move=> H; exfalso; move: H => /eqP.
    by rewrite (negbTE (neq_lift _ _)).
  + move=> H; exfalso; move: H => /eqP.
    by rewrite (eq_sym _ ord_max) (negbTE (neq_lift _ _)).
  + by move=> /lift_inj /perm_inj ->.
- (* Some, None *)
  case: (boolP (kx == j0)) => [/eqP Ekx | kx_ne].
  + move=> H; exfalso.
    have := neq_lift ord_max (s j0).
    by rewrite -H eqxx.
  + move=> /lift_inj /perm_inj E.
    by rewrite E eqxx in kx_ne.
- (* None, Some *)
  case: (boolP (ky == j0)) => [/eqP Eky | ky_ne].
  + move=> H; exfalso.
    have := neq_lift ord_max (s j0).
    by rewrite H eqxx.
  + move=> /lift_inj /perm_inj E.
    by rewrite -E eqxx in ky_ne.
- (* None, None *)
  by [].
Qed.

Definition insert_after (j0 : 'I_n) (s : {perm 'I_n}) : {perm 'I_n.+1} :=
  perm (@insert_after_fun_inj j0 s).

Lemma insert_afterE j0 s x :
  insert_after j0 s x = insert_after_fun j0 s x.
Proof. by rewrite /insert_after permE. Qed.

Lemma insert_after_ord_max j0 s :
  insert_after j0 s ord_max = lift ord_max (s j0).
Proof. by rewrite insert_afterE /insert_after_fun unlift_none. Qed.

Lemma insert_after_j0 j0 s :
  insert_after j0 s (lift ord_max j0) = ord_max.
Proof. by rewrite insert_afterE /insert_after_fun liftK eqxx. Qed.

Lemma insert_after_other j0 s k :
  k != j0 -> insert_after j0 s (lift ord_max k) = lift ord_max (s k).
Proof.
move=> kne.
by rewrite insert_afterE /insert_after_fun liftK (negbTE kne).
Qed.

Lemma insert_after_ord_max_neq j0 s :
  insert_after j0 s ord_max != ord_max.
Proof. by rewrite insert_after_ord_max eq_sym neq_lift. Qed.

End InsertAfter.

(* ========================================================================= *)
(* §B. Sanity check.                                                          *)
(*                                                                            *)
(* Goal of plan was vm_compute cycle_count for n=2.  Unfortunately mathcomp's *)
(* {perm} type wraps finfun which is opaque to vm_compute (computing          *)
(* cycle_count of even the identity on 'I_2 times out).  We instead do        *)
(* symbolic sanity: insert_after preserves the j0-cycle structure pointwise.  *)
(* ========================================================================= *)

Lemma sanity_insert_after_pointwise n (j0 : 'I_n) (s : {perm 'I_n}) :
  let sigma := insert_after j0 s in
  [/\ sigma ord_max = lift ord_max (s j0),
      sigma (lift ord_max j0) = ord_max
    & forall k, k != j0 -> sigma (lift ord_max k) = lift ord_max (s k)].
Proof.
split; [ exact: insert_after_ord_max
       | exact: insert_after_j0
       | exact: insert_after_other ].
Qed.

(* ========================================================================= *)
(* §C. Cycle count of insert_after = cycle count of s                         *)
(*                                                                            *)
(* Strategy: decompose insert_after as a product of a transposition and       *)
(* a lift_perm fixing ord_max, then apply mathcomp's porbits_mul_tperm.       *)
(* ========================================================================= *)

Section CycleCountInsertAfter.
Variable n : nat.
Variable s : {perm 'I_n}.
Variable j0 : 'I_n.

Notation sigma := (insert_after j0 s).

(* Decomposition: sigma factors as (tperm ord_max (lift j0)) * lift_perm.
   In mathcomp, (p * q) x = q (p x), so we apply tperm first, then lift_perm. *)
Lemma insert_after_decomp :
  insert_after j0 s =
  ((tperm ord_max (lift ord_max j0)) * (perm.lift_perm ord_max ord_max s))%g.
Proof.
apply/permP => x.
rewrite permM.
case: (unliftP ord_max x) => [k -> | ->].
- (* x = lift ord_max k *)
  case: (altP (k =P j0)) => [-> | kne].
  + by rewrite tpermR perm.lift_perm_id insert_after_j0.
  + rewrite tpermD ?perm.lift_perm_lift.
    * by rewrite insert_after_other // eq_sym.
    * by rewrite neq_lift.
    * by apply: contra kne => /eqP /lift_inj ->; rewrite eqxx.
- by rewrite tpermL perm.lift_perm_lift insert_after_ord_max.
Qed.

Lemma cycle_count_insert_after :
  cycle_count (insert_after j0 s) = cycle_count s.
Proof.
have not_in :
  ord_max \notin porbit (perm.lift_perm ord_max ord_max s) (lift ord_max j0).
  rewrite porbit_lift_perm_id_lift.
  apply/imsetP => [[k _ /eqP H]].
  by move: H => /eqP H; have := neq_lift ord_max k; rewrite -H eqxx.
have lne' : (ord_max != lift ord_max j0) by rewrite neq_lift.
have key := porbits_mul_tperm
              (perm.lift_perm ord_max ord_max s) ord_max (lift ord_max j0).
move: key; rewrite /= not_in lne' /=.
rewrite -[#|porbits (perm.lift_perm _ _ _)|]
        /(cycle_count (perm.lift_perm ord_max ord_max s)).
rewrite cycle_count_lift_perm_id.
rewrite /cycle_count insert_after_decomp.
rewrite -[1.*2]/(2).
have -> : #|porbits s|.+1 + 1 = #|porbits s| + 2 by rewrite addn1 addn2.
by move=> /addIn.
Qed.

End CycleCountInsertAfter.

(* ========================================================================= *)
(* §D. Bijection: insert_after as a bijection between                         *)
(*       'I_n × {perm 'I_n}                                                    *)
(*     and                                                                    *)
(*       {sigma : {perm 'I_n.+1} | sigma ord_max != ord_max}                  *)
(* ========================================================================= *)

(* Injectivity in the (j0, s) pair. *)
Lemma insert_after_inj_pair n j0 j0' (s s' : {perm 'I_n}) :
  insert_after j0 s = insert_after j0' s' -> (j0 = j0' /\ s = s').
Proof.
move=> Hperm.
have Hj0 : j0 = j0'.
  have H := f_equal (fun p : {perm _} => p (lift ord_max j0)) Hperm.
  rewrite insert_after_j0 in H.
  case: (altP (j0 =P j0')) => // jne.
  rewrite (@insert_after_other n j0' s' j0 jne) in H.
  by have := neq_lift ord_max (s' j0); rewrite -H eqxx.
subst j0'.
split=> //.
apply/permP => k.
case: (altP (k =P j0)) => [-> | kne].
- have Hom := f_equal (fun p : {perm _} => p ord_max) Hperm.
  rewrite !insert_after_ord_max in Hom.
  exact: (@lift_inj _ ord_max) Hom.
- have H := f_equal (fun p : {perm _} => p (lift ord_max k)) Hperm.
  rewrite !insert_after_other // in H.
  exact: (@lift_inj _ ord_max) H.
Qed.

(* Surjectivity: every sigma with sigma ord_max != ord_max is in the image
   of insert_after.  Construction uses the perm_compress drop_perm operator
   on the conjugate "tau = tperm * sigma" which fixes ord_max. *)
Lemma insert_after_surj n (sigma : {perm 'I_n.+1}) :
  sigma ord_max != ord_max ->
  exists j0 (s : {perm 'I_n}), sigma = insert_after j0 s.
Proof.
move=> Hsi.
have Hsm : sigma^-1%g ord_max != ord_max.
  apply: contra Hsi => /eqP H.
  by have := f_equal sigma H; rewrite permKV => <-.
have [j0 Hj0] : exists j0, sigma^-1%g ord_max = lift ord_max j0.
  case: (unliftP ord_max (sigma^-1%g ord_max)) Hsm => [j0 Hj0 _ | -> /eqP].
  - by exists j0.
  - by [].
have key : sigma (lift ord_max j0) = ord_max by rewrite -Hj0 permKV.
set tau := (tperm ord_max (lift ord_max j0) * sigma)%g.
have tau_om : tau ord_max = ord_max by rewrite /tau permM tpermL.
exists j0, (drop_perm tau).
apply/permP => x.
rewrite insert_after_decomp permM.
have lpd := lift_perm_drop_perm tau.
rewrite tau_om in lpd.
have eq_tau : forall y,
  (perm.lift_perm ord_max ord_max (drop_perm tau)) y = tau y.
  move=> y.
  case: (unliftP ord_max y) => [k -> | ->].
  - rewrite perm.lift_perm_lift.
    have := f_equal (fun p : {perm _} => p (lift ord_max k)) lpd.
    by rewrite perm_compress.lift_perm_lift.
  - by rewrite perm.lift_perm_id tau_om.
by rewrite eq_tau /tau permM tpermK.
Qed.

(* ========================================================================= *)
(* §E. Per-fiber count and stirling_c_rec assembly                            *)
(* ========================================================================= *)

(* Count of permutations sigma of 'I_n.+1 with sigma ord_max != ord_max
   and a given cycle count.  Via the (j0, s) bijection, this is
   n * stirling_c n k.+1. *)
Lemma card_neq_ord_max_fiber n k :
  #|[set sigma : {perm 'I_n.+1} | (sigma ord_max != ord_max) &&
                                  (cycle_count sigma == k.+1)]|
  = n * stirling_c n k.+1.
Proof.
pose F := fun (p : 'I_n * {perm 'I_n}) => insert_after p.1 p.2.
have F_inj : injective F.
  move=> [j1 s1] [j2 s2] H.
  move: H; rewrite /F /= => H.
  have [E1 E2] := insert_after_inj_pair H.
  by rewrite E1 E2.
have im_eq :
  [set F p | p in [set p : 'I_n * {perm 'I_n} | cycle_count p.2 == k.+1]] =
  [set sigma : {perm 'I_n.+1} | (sigma ord_max != ord_max) &&
                                 (cycle_count sigma == k.+1)].
  apply/setP => sigma; rewrite !inE.
  apply/imsetP/andP.
  - case=> [[j s]]; rewrite inE /= => /eqP Hcs ->.
    by rewrite cycle_count_insert_after Hcs eqxx insert_after_ord_max_neq.
  - case=> [Hne /eqP Hcc].
    have [j0 [s Hs]] := insert_after_surj Hne.
    exists (j0, s); last by [].
    rewrite inE /=.
    by rewrite -(cycle_count_insert_after _ j0) -Hs Hcc.
rewrite -im_eq.
rewrite card_in_imset; last by move=> *; exact: F_inj.
rewrite -sum1_card.
rewrite (eq_bigl (fun p : 'I_n * {perm 'I_n} => cycle_count p.2 == k.+1)).
  rewrite -[\sum_(i | _) _]
          /(\sum_(p : 'I_n * {perm 'I_n} | cycle_count p.2 == k.+1) 1).
  rewrite -(pair_big xpredT (fun s : {perm 'I_n} => cycle_count s == k.+1)
                     (fun _ _ => 1)) /=.
  rewrite sum_nat_const card_ord.
  congr (n * _).
  rewrite /stirling_c -sum1_card.
  by apply: eq_bigl => s; rewrite inE.
by move=> p; rewrite inE.
Qed.

(* The eq_ord_max fiber: bijection via mathcomp's perm.lift_perm and
   perm_compress.drop_perm. *)
Lemma card_eq_ord_max_fiber n k :
  #|[set sigma : {perm 'I_n.+1} | (sigma ord_max == ord_max) &&
                                  (cycle_count sigma == k.+1)]|
  = stirling_c n k.
Proof.
pose F := fun (s : {perm 'I_n}) => perm.lift_perm ord_max ord_max s.
have F_inj : injective F.
  move=> s1 s2 H.
  apply/permP => k0.
  have := f_equal (fun p : {perm _} => p (lift ord_max k0)) H.
  rewrite !perm.lift_perm_lift.
  exact: (@lift_inj _ ord_max).
have im_eq :
  [set F s | s in [set s : {perm 'I_n} | cycle_count s == k]] =
  [set sigma : {perm 'I_n.+1} | (sigma ord_max == ord_max) &&
                                 (cycle_count sigma == k.+1)].
  apply/setP => sigma; rewrite !inE.
  apply/imsetP/andP.
  - case=> [s]; rewrite inE => /eqP Hcs ->.
    by rewrite /F perm.lift_perm_id eqxx cycle_count_lift_perm_id Hcs.
  - case=> [/eqP Hom /eqP Hcc].
    exists (drop_perm sigma); last first.
      rewrite /F.
      have lpd := lift_perm_drop_perm sigma.
      rewrite Hom in lpd.
      apply/permP => x.
      case: (unliftP ord_max x) => [k0 -> | ->].
      + rewrite perm.lift_perm_lift.
        have := f_equal (fun p : {perm _} => p (lift ord_max k0)) lpd.
        by rewrite perm_compress.lift_perm_lift.
      + by rewrite perm.lift_perm_id.
    rewrite inE.
    have key :
      cycle_count (perm.lift_perm ord_max ord_max (drop_perm sigma)) =
      cycle_count sigma.
      f_equal.
      apply/permP => x.
      case: (unliftP ord_max x) => [k0 -> | ->].
      + rewrite perm.lift_perm_lift.
        have lpd := lift_perm_drop_perm sigma.
        rewrite Hom in lpd.
        have := f_equal (fun p : {perm _} => p (lift ord_max k0)) lpd.
        by rewrite perm_compress.lift_perm_lift.
      + by rewrite perm.lift_perm_id.
    rewrite cycle_count_lift_perm_id in key.
    by have := key; rewrite Hcc => [/eq_add_S ->].
rewrite -im_eq card_in_imset; last by move=> *; exact: F_inj.
rewrite /stirling_c.
by apply: eq_card => s; rewrite !inE.
Qed.

(* Final assembly. *)
Lemma stirling_c_rec n k :
  stirling_c n.+1 k.+1 = n * stirling_c n k.+1 + stirling_c n k.
Proof.
rewrite -(card_neq_ord_max_fiber n k) -(card_eq_ord_max_fiber n k).
rewrite /stirling_c.
have setU :
  [set sigma : {perm 'I_n.+1} | cycle_count sigma == k.+1] =
  [set sigma : {perm 'I_n.+1} | (sigma ord_max != ord_max) &&
                                (cycle_count sigma == k.+1)] :|:
  [set sigma : {perm 'I_n.+1} | (sigma ord_max == ord_max) &&
                                (cycle_count sigma == k.+1)].
  apply/setP => sigma; rewrite !inE.
  by case E: (sigma ord_max == ord_max); rewrite ?orbT ?orbF /=.
have setI :
  [set sigma : {perm 'I_n.+1} | (sigma ord_max != ord_max) &&
                                (cycle_count sigma == k.+1)] :&:
  [set sigma : {perm 'I_n.+1} | (sigma ord_max == ord_max) &&
                                (cycle_count sigma == k.+1)] = set0.
  apply/setP => sigma; rewrite !inE.
  by case: (sigma ord_max == ord_max); rewrite //= andbF.
have := cardsUI
  [set sigma : {perm 'I_n.+1} | (sigma ord_max != ord_max) &&
                                (cycle_count sigma == k.+1)]
  [set sigma : {perm 'I_n.+1} | (sigma ord_max == ord_max) &&
                                (cycle_count sigma == k.+1)].
by rewrite setI cards0 addn0 -setU => ->.
Qed.
