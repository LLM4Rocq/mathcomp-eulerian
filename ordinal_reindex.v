(* Layer 0: bump / unbump reindexing on 'I_n.                                *)
(* MathComp already provides [lift] and [unlift] with cancellation lemmas    *)
(* [liftK], [unliftK] and the nat-level [bump]/[unbump] with their monotony  *)
(* lemmas [leq_bump2]/[ltn_bump].  This layer adds the ordinal-level strict  *)
(* monotonicity lemmas used by the compression/expansion of permutations.   *)

From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section LiftOrd.
Variable n : nat.
Implicit Types (k : 'I_n.+1) (i j : 'I_n).

(** Weak monotonicity of [lift k : 'I_n -> 'I_n.+1]: lifting preserves [<=]. *)
Lemma leq_lift k i j : (lift k i <= lift k j) = (i <= j).
Proof. exact: leq_bump2. Qed.

(** Strict monotonicity of [lift k : 'I_n -> 'I_n.+1]: lifting preserves [<]. *)
Lemma ltn_lift k i j : (lift k i < lift k j) = (i < j).
Proof. by rewrite !ltnNge leq_lift. Qed.

(** The image of [lift k : 'I_n -> 'I_n.+1] is the complement of [{k}]:
    [lift k] surjects onto every ordinal of ['I_n.+1] except [k] itself. *)
End LiftOrd.

Section UnliftOrd.
Variable n : nat.
Implicit Types (k : 'I_n.+1) (j : 'I_n.+1).

(** Strict monotonicity of [unlift] where defined: if [j1, j2 != k] then the
    underlying ordinals returned by [unlift_some] respect the order of [j1, j2]. *)
End UnliftOrd.
