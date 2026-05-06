(* Layer 1: drop_perm / lift_perm — permutation compression and expansion. *)
(* Given σ : {perm 'I_n.+1}, [drop_perm σ] is the permutation of 'I_n       *)
(* obtained by deleting the position [ord_max] (mapping to [σ ord_max]) and  *)
(* collapsing around that value.  The inverse operation [lift_perm k τ]     *)
(* inserts a new maximum position sent to [k].                                *)

From mathcomp Require Import all_ssreflect fingroup perm.
From mathcomp_eulerian Require Import ordinal_reindex.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* ========================================================================= *)
(* drop_perm                                                                *)
(* ========================================================================= *)

Section DropPerm.
Variables (n : nat) (s : {perm 'I_n.+1}).

(** [s] sends [ord_max] and [lift ord_max i] to distinct values, by injectivity. *)
Fact drop_fun_ne (i : 'I_n) : s ord_max != s (lift ord_max i).
Proof. by apply/eqP => /perm_inj /eqP; rewrite (negbTE (neq_lift _ _)). Qed.

(** [drop_fun i] is the unique [j : 'I_n] such that [s (lift ord_max i) = lift (s ord_max) j].
    This is [s] restricted to ['I_n.+1 \ {ord_max}] and reindexed onto ['I_n]. *)
Definition drop_fun (i : 'I_n) : 'I_n := sval (unlift_some (drop_fun_ne i)).

(** Defining equation for [drop_fun]: [s (lift ord_max i)] equals [lift (s ord_max) (drop_fun i)]. *)
Lemma drop_funE i : s (lift ord_max i) = lift (s ord_max) (drop_fun i).
Proof. by rewrite /drop_fun; case: (unlift_some _) => /= j -> _. Qed.

(** [drop_fun] is injective, inheriting injectivity from [s]. *)
Lemma drop_fun_inj : injective drop_fun.
Proof. by move=> i1 i2 /(congr1 (lift (s ord_max))); rewrite -!drop_funE => /perm_inj/lift_inj. Qed.

(** [drop_perm s] is the permutation of ['I_n] obtained by deleting position
    [ord_max] from [s] and collapsing around the value [s ord_max]. *)
Definition drop_perm : {perm 'I_n} := perm drop_fun_inj.

(** Equivalence with the underlying [drop_fun] for rewriting. *)
Lemma drop_permE i : drop_perm i = drop_fun i.
Proof. by rewrite permE. Qed.

(** Defining equation: lifting [drop_perm] back through [s ord_max] recovers [s]
    on lifted positions. Used to relate descents of [s] and [drop_perm s]. *)
Lemma lift_drop_permE i :
  lift (s ord_max) (drop_perm i) = s (lift ord_max i).
Proof. by rewrite drop_permE -drop_funE. Qed.

End DropPerm.

(* ========================================================================= *)
(* lift_perm                                                                 *)
(* ========================================================================= *)

Section LiftPerm.
Variables (n : nat) (k : 'I_n.+1) (t : {perm 'I_n}).

(** Underlying function of [lift_perm k t]: sends [ord_max] to [k] and lifts
    [t] elsewhere via [lift k]. *)
Definition lift_fun (i : 'I_n.+1) : 'I_n.+1 :=
  match unlift ord_max i with
  | Some j => lift k (t j)
  | None => k
  end.

(** [lift_fun] sends [ord_max] to [k]. *)
Lemma lift_fun_ord_max : lift_fun ord_max = k.
Proof. by rewrite /lift_fun unlift_none. Qed.

(** [lift_fun] on lifted positions equals [lift k (t .)]. *)
Lemma lift_fun_lift i : lift_fun (lift ord_max i) = lift k (t i).
Proof. by rewrite /lift_fun liftK. Qed.

(** [lift_fun] is injective: combine injectivity of [lift] and [t]. *)
Lemma lift_fun_inj : injective lift_fun.
Proof.
move=> i1 i2; rewrite /lift_fun.
case: unliftP => [j1 ->|->]; case: unliftP => [j2 ->|->] //.
- by move/lift_inj/perm_inj->.
- by move/eqP; rewrite eq_sym (negbTE (neq_lift _ _)).
- by move/eqP; rewrite (negbTE (neq_lift _ _)).
Qed.

(** [lift_perm k t] is the permutation of ['I_n.+1] obtained from [t : {perm 'I_n}]
    by inserting a new maximum position [ord_max] sent to [k]. Inverse of [drop_perm]. *)
Definition lift_perm : {perm 'I_n.+1} := perm lift_fun_inj.

(** Equivalence with the underlying [lift_fun] for rewriting. *)
Lemma lift_permE i : lift_perm i = lift_fun i.
Proof. by rewrite permE. Qed.

(** [lift_perm k t] sends [ord_max] to [k]. *)
Lemma lift_perm_ord_max : lift_perm ord_max = k.
Proof. by rewrite lift_permE lift_fun_ord_max. Qed.

(** [lift_perm k t] on lifted positions equals [lift k (t .)]. *)
Lemma lift_perm_lift i : lift_perm (lift ord_max i) = lift k (t i).
Proof. by rewrite lift_permE lift_fun_lift. Qed.

(** Only [ord_max] is sent to [k] by [lift_perm k t]; all other positions avoid [k]. *)
Lemma lift_perm_ne_k i : i != ord_max -> lift_perm i != k.
Proof.
case: (unliftP ord_max i) => [j ->|-> /eqP//] _.
by rewrite lift_perm_lift eq_sym neq_lift.
Qed.

End LiftPerm.

(* ========================================================================= *)
(* Cancellation lemmas                                                       *)
(* ========================================================================= *)

Section Cancellation.
Variable n : nat.

(** Left inverse: dropping a freshly lifted permutation recovers the original. *)
Lemma drop_perm_lift_perm (k : 'I_n.+1) (t : {perm 'I_n}) :
  drop_perm (lift_perm k t) = t.
Proof.
apply/permP => i; apply: (@lift_inj _ (lift_perm k t ord_max)).
by rewrite lift_drop_permE lift_perm_lift lift_perm_ord_max.
Qed.

(** Right inverse: lifting a dropped permutation at the dropped value recovers
    the original. Establishes the bijection [{perm 'I_n.+1}] ~= ['I_n.+1] x [{perm 'I_n}]. *)
Lemma lift_perm_drop_perm (s : {perm 'I_n.+1}) :
  lift_perm (s ord_max) (drop_perm s) = s.
Proof.
apply/permP => i; rewrite lift_permE /lift_fun.
by case: (unliftP ord_max i) => [j|]->//; rewrite lift_drop_permE.
Qed.

(** Restatement of [lift_perm_ord_max] with explicit arguments, for use by clients. *)
Lemma lift_perm_ord_max_eq (k : 'I_n.+1) (t : {perm 'I_n}) :
  (lift_perm k t) ord_max = k.
Proof. exact: lift_perm_ord_max. Qed.

End Cancellation.
