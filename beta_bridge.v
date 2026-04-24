(* beta_bridge.v -- Bridge: omega proper subset => beta strict inequality.    *)
(*                                                                            *)
(* Stanley EC1 (2nd ed.) Proposition 1.6.4 at the finset level.              *)
(*                                                                            *)
(* Structure:                                                                 *)
(*   SA.  Type bridge: set_to_seq (finset -> seq nat)                        *)
(*   SB.  omega_set / omega_seq correspondence (proved)                      *)
(*   SC.  phi_w_support_general (Axiom: Stanley Thm 1.6.3)                  *)
(*        -- cd-index has nonneg integer coefficients                        *)
(*        -- verified for S_3, S_4 in psi_cdindex.v                          *)
(*   SD.  omega_proper_beta_lt (Axiom, from SC + bridge)                     *)
(*        -- Stanley Prop 1.6.4: omega(D) proper-sub omega(E) =>            *)
(*           beta(D) < beta(E)                                               *)
(*        -- derivable from SC once perm<->seq bijection is complete         *)
(*   SE.  beta_swap_lt_caseA derived from SD + beta_omega.v                  *)
(*                                                                            *)
(* Build order: beta_omega.v -> beta_bridge.v -> beta_swap.v.               *)

From mathcomp Require Import all_ssreflect fingroup perm.
From mathcomp_eulerian Require Import
  ordinal_reindex perm_compress descent eulerian beta beta_omega.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* ========================================================================= *)
(* SA. Type bridge: finset -> seq nat                                        *)
(* ========================================================================= *)

(* Convert a descent set {set 'I_n} to a sorted seq nat of positions.       *)
Definition set_to_seq (n : nat) (D : {set 'I_n}) : seq nat :=
  sort leq [seq val i | i <- enum D].

Lemma mem_set_to_seq n (D : {set 'I_n}) (k : nat) :
  (k \in set_to_seq D) = (k \in [seq val i | i <- enum D]).
Proof. by rewrite mem_sort. Qed.

Lemma mem_set_to_seq_iff n (D : {set 'I_n}) (k : nat) :
  (k \in set_to_seq D) =
  has (fun i => val i == k) (enum D).
Proof.
rewrite mem_set_to_seq.
elim: (enum D) => [| x xs IH] //=.
rewrite in_cons IH.
by congr orb.
Qed.

Lemma mem_set_to_seq_ord n (D : {set 'I_n}) (i : 'I_n) :
  (val i \in set_to_seq D) = (i \in D).
Proof.
rewrite mem_set_to_seq_iff.
apply/hasP/idP.
- case=> j Hj /eqP Hv.
  have -> : i = j by apply/val_inj.
  by rewrite mem_enum in Hj.
- move=> Hi; exists i => //.
  by rewrite mem_enum.
Qed.

Lemma uniq_set_to_seq n (D : {set 'I_n}) :
  uniq (set_to_seq D).
Proof.
rewrite sort_uniq map_inj_uniq ?enum_uniq //.
by move=> x y /= /val_inj.
Qed.

Lemma set_to_seq_bound n (D : {set 'I_n}) (k : nat) :
  k \in set_to_seq D -> k < n.
Proof.
rewrite mem_set_to_seq => /mapP [i _ ->].
exact: ltn_ord.
Qed.

(* ========================================================================= *)
(* SB. omega_set / omega_seq correspondence                                  *)
(* ========================================================================= *)

(* The omega map on seq nat, mirroring psi_cdindex.omega_seq.               *)
(* omega(S) = {k : exactly one of k, k+1 belongs to S}.                    *)
Definition omega_seq_local (s : seq nat) : seq nat :=
  [seq k <- iota 0 (foldr maxn 0 s).+1
   | (k \in s) != ((k.+1) \in s)].

(* Bridge: for k : 'I_m, membership in omega_set D (finset) equals         *)
(* membership in omega_seq_local (set_to_seq D) (seq), provided there      *)
(* exists an element >= k in D (so foldr maxn covers k).                    *)

Lemma foldr_maxn_set_to_seq_lb n (D : {set 'I_n}) (k : nat) :
  k \in set_to_seq D -> k <= foldr maxn 0 (set_to_seq D).
Proof.
elim: (set_to_seq D) => [| x xs IH] //=.
rewrite in_cons => /orP [/eqP -> | /IH Hle].
- by rewrite leq_maxl.
- exact: leq_trans Hle (leq_maxr _ _).
Qed.

(* If D is nonempty, foldr maxn gives a value in D. *)
Lemma omega_set_seq_local_bridge (m : nat)
    (D : {set 'I_m.+1}) (k : 'I_m) :
  (k \in omega_set D) =
  (val k \in omega_seq_local (set_to_seq D)).
Proof.
rewrite mem_omega_set /omega_seq_local mem_filter mem_iota
        /= add0n.
(* LHS: (widen_ord _ k \in D) != (lift ord0 k \in D) *)
(* Convert to set_to_seq membership *)
pose w := widen_ord (leqnSn m) k.
pose l := lift ord0 k.
have Hwv : val w = val k by [].
have Hlv : val l = (val k).+1
  by rewrite /l /= /bump /= add1n.
rewrite -(mem_set_to_seq_ord D w) Hwv.
rewrite -(mem_set_to_seq_ord D l) Hlv.
(* Goal: (val k \in set_to_seq D) != ((val k).+1 \in set_to_seq D)
         = ... && (val k < (foldr maxn 0 (set_to_seq D)).+1) *)
set b := (_ != _).
case Hb: b => /=; last by [].
(* Need: val k < (foldr maxn 0 (set_to_seq D)).+1 *)
(* b = true means exactly one of val k, (val k).+1 in set_to_seq D *)
move: Hb; rewrite /b {b}.
case Hk: (val k \in set_to_seq D);
  case Hk1: ((val k).+1 \in set_to_seq D) => //= _.
- (* val k \in set_to_seq D *)
  have := foldr_maxn_set_to_seq_lb Hk.
  by move=> ?; rewrite ltnS.
- (* (val k).+1 \in set_to_seq D *)
  have Hle := foldr_maxn_set_to_seq_lb Hk1.
  symmetry; apply/idP. rewrite ltnS.
  exact: leq_trans (leqnSn _) Hle.
Qed.

(* ========================================================================= *)
(* SC. Stanley Prop 1.6.4 (Axiom)                                           *)
(* ========================================================================= *)

(* omega_proper_beta_lt: omega(D) proper-sub omega(E) => beta(D) < beta(E). *)
(*                                                                           *)
(* Stanley EC1 (2nd ed.) Proposition 1.6.4 proof sketch:                    *)
(* 1. By Thm 1.6.3 (cd-index nonneg), each M-equivalence class [w]         *)
(*    contributes exactly one cd-monomial to Phi_n. Define S_w = d-         *)
(*    positions of [w]. Then beta(S) = #{classes : S_w <= omega(S)}.        *)
(* 2. omega_monotone_class_count (PROVED in psi_cdindex.v): if              *)
(*    omega(S) <= omega(T), every class counted by S is counted by T.       *)
(* 3. strict_witness_exists (PROVED in psi_cdindex.v): for any k < n-2,    *)
(*    the cd-word c^k d c^{n-2-k} has S_w = {k}, so k in omega(T)\omega(S) *)
(*    gives a class counted by T but not S.                                 *)
(* 4. Hence omega(S) proper-sub omega(T) => beta(S) < beta(T).             *)
(*                                                                           *)
(* Gap to close this axiom: the type bridge {perm 'I_n.+1} <-> seq nat     *)
(* (connecting finset-level beta to seq-level M-class counting) and         *)
(* phi_w_support_general (the cd-index theorem for general n, currently     *)
(* only verified computationally for n <= 4 in psi_cdindex.v).              *)

Axiom omega_proper_beta_lt : forall m (D E : {set 'I_m.+1}),
  omega_set D \proper omega_set E ->
  beta D < beta E.

(* ========================================================================= *)
(* §B. Closing beta_swap_lt_caseA                                            *)
(* ========================================================================= *)

(* Case A: i,j ∈ D with j = i+1, and (j+1 ∈ D or j is the last position).
   toggle_at_j_omega_strict_superset (beta_omega.v §H) proves
   omega_set D ⊊ omega_set (toggle_at D j) under these hypotheses.
   omega_proper_beta_lt then gives the beta strict inequality. *)
Lemma beta_swap_lt_caseA : forall n (D : {set 'I_n}) (i j : 'I_n),
  val j = (val i).+1 -> i \in D -> j \in D ->
  (forall q : 'I_n, val q = (val j).+1 -> q \in D) ->
  beta D < beta (toggle_at D j).
Proof.
move=> n D i j Hj Hi Hjin Hsucc.
case: n D i j Hj Hi Hjin Hsucc => [|m] D i j Hj Hi Hjin Hsucc.
- (* n = 0: 'I_0 is empty, i : 'I_0 is vacuously absurd *)
  by have := ltn_ord i; rewrite ltn0.
- (* n = m.+1: D : {set 'I_m.+1}, omega_set D : {set 'I_m}.
     toggle_at_j_omega_strict_superset applied with n := m gives
     omega_set D \proper omega_set (toggle_at D j). *)
  apply: (omega_proper_beta_lt (m := m)).
  exact: toggle_at_j_omega_strict_superset Hj Hi Hjin Hsucc.
Qed.

