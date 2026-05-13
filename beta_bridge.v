(* beta_bridge.v -- Bridge: omega proper subset => beta strict inequality.    *)
(*                                                                            *)
(* Stanley EC1 (2nd ed.) Proposition 1.6.4 at the finset level.              *)
(*                                                                            *)
(* Structure:                                                                 *)
(*   SA.  Type bridge: set_to_seq (finset -> seq nat)                        *)
(*   SB.  omega_set / omega_seq correspondence (proved)                      *)
(*   SC.  omega_proper_beta_lt + beta_swap_lt_caseA moved to                 *)
(*        perm_seq_bridge.v (which imports both this file and psi_cdindex)    *)
(*                                                                            *)
(* Build order: beta_omega.v -> beta_bridge.v -> perm_seq_bridge.v ->        *)
(*              beta_swap.v.                                                  *)

From mathcomp Require Import all_ssreflect fingroup perm.
From mathcomp_eulerian Require Import
  ordinal_reindex perm_compress descent eulerian beta beta_omega.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* ========================================================================= *)
(* SA. Type bridge: finset -> seq nat                                        *)
(* ========================================================================= *)

(** [set_to_seq D] -- convert the finset [D : {set 'I_n}] to the
    sorted [seq nat] of underlying positions; bridges the finset
    descent world to the seq-based [psi_cdindex] machinery. *)
Definition set_to_seq (n : nat) (D : {set 'I_n}) : seq nat :=
  sort leq [seq val i | i <- enum D].

(** [mem_set_to_seq] -- membership in [set_to_seq D] equals membership
    in the unsorted underlying value list (sorting is order-preserving
    on memberships). *)
Lemma mem_set_to_seq n (D : {set 'I_n}) (k : nat) :
  (k \in set_to_seq D) = (k \in [seq val i | i <- enum D]).
Proof. by rewrite mem_sort. Qed.

(** [mem_set_to_seq_iff] -- alternative form of membership in
    [set_to_seq D] as a [has] over [enum D]. *)
Lemma mem_set_to_seq_iff n (D : {set 'I_n}) (k : nat) :
  (k \in set_to_seq D) =
  has (fun i => val i == k) (enum D).
Proof.
rewrite mem_set_to_seq.
elim: (enum D) => [| x xs IH] //=.
rewrite in_cons IH.
by congr orb.
Qed.

(** [mem_set_to_seq_ord] -- ordinal-level membership bridge: [val i]
    is in [set_to_seq D] iff [i] is in [D]. *)
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

(** [uniq_set_to_seq] -- the seq-of-positions [set_to_seq D] has no
    duplicates. *)
Lemma uniq_set_to_seq n (D : {set 'I_n}) :
  uniq (set_to_seq D).
Proof.
rewrite sort_uniq map_inj_uniq ?enum_uniq //.
by move=> x y /= /val_inj.
Qed.

(** [set_to_seq_bound] -- every element of [set_to_seq D] is bounded
    above by [n]. *)
(* ========================================================================= *)
(* SB. omega_set / omega_seq correspondence                                  *)
(* ========================================================================= *)

(** [omega_seq_local s] -- the omega map at the seq level (mirrors
    [psi_cdindex.omega_seq]): the list of [k] in [iota 0 (max s).+1]
    such that exactly one of [k], [k+1] belongs to [s]. *)
Definition omega_seq_local (s : seq nat) : seq nat :=
  [seq k <- iota 0 (foldr maxn 0 s).+1
   | (k \in s) != ((k.+1) \in s)].

(* Bridge: for k : 'I_m, membership in omega_set D (finset) equals         *)
(* membership in omega_seq_local (set_to_seq D) (seq), provided there      *)
(* exists an element >= k in D (so foldr maxn covers k).                    *)

(** [foldr_maxn_set_to_seq_lb] -- any element of [set_to_seq D] is
    bounded above by [foldr maxn 0] over the same list (used to ensure
    the [iota] bound in [omega_seq_local] covers the relevant range). *)
Lemma foldr_maxn_set_to_seq_lb n (D : {set 'I_n}) (k : nat) :
  k \in set_to_seq D -> k <= foldr maxn 0 (set_to_seq D).
Proof.
elim: (set_to_seq D) => [| x xs IH] //=.
rewrite in_cons => /orP [/eqP -> | /IH Hle].
- by rewrite leq_maxl.
- exact: leq_trans Hle (leq_maxr _ _).
Qed.

(** [omega_set_seq_local_bridge] -- key bridge: [k \in omega_set D]
    (finset side) iff [val k \in omega_seq_local (set_to_seq D)] (seq
    side). Connects the two formulations of Stanley's omega map. *)
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
(* SC. omega_proper_beta_lt + beta_swap_lt_caseA                             *)
(* ========================================================================= *)
(* Moved to perm_seq_bridge.v (which imports both this file and psi_cdindex) *)
