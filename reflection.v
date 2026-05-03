(* Layer 6 (Phase C): André's reflection method for Euler numbers.            *)
(*                                                                            *)
(* Stanley EC1 §1.6.4.                                                        *)
(*                                                                            *)
(* This file lands the definitions of Euler numbers via the alternating       *)
(* descent set and the trivial base cases.  The substantive recurrence        *)
(*                                                                            *)
(*    2 * eulerA n.+2 = \sum_(k < n.+2) 'C(n.+1, k) * eulerA k * eulerA (n.+1 - k) *)
(*                                                                            *)
(* is left for sessions C-2 through C-5.                                      *)

From mathcomp Require Import all_ssreflect fingroup perm.
From mathcomp_eulerian Require Import ordinal_reindex perm_compress
                                       descent eulerian beta beta_omega
                                       beta_swap.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* ========================================================================= *)
(* §A. Definitions                                                           *)
(* ========================================================================= *)

(* euler n = number of permutations of 'I_n.+1 with descent set equal to     *)
(* alt_desc_set n = {0, 2, 4, ...}.  In Stanley's notation this is A_{n+1}: *)
(* the count of down-up alternating permutations of length n+1.              *)
Definition euler (n : nat) : nat := beta (alt_desc_set n).

(* eulerA n = A_n in Stanley's notation, with the convention                  *)
(* A_0 := 1 (empty alternating permutation).                                  *)
Definition eulerA (n : nat) : nat :=
  if n is k.+1 then euler k else 1.

(* ========================================================================= *)
(* §B. Trivial base cases                                                    *)
(* ========================================================================= *)

Lemma eulerA_0 : eulerA 0 = 1.
Proof. by []. Qed.

(* alt_desc_set 0 = set0 since 'I_0 is empty.                                *)
Lemma alt_desc_set_0 : alt_desc_set 0 = set0.
Proof. by apply/setP; case; case. Qed.

(* euler 0 counts perms of 'I_1 with descent_set = set0; only id qualifies. *)
Lemma euler_0 : euler 0 = 1.
Proof. by rewrite /euler alt_desc_set_0 beta0. Qed.

Lemma eulerA_1 : eulerA 1 = 1.
Proof. by rewrite /eulerA euler_0. Qed.

(* alt_desc_set 1 = [set: 'I_1] since the unique element of 'I_1 has         *)
(* val 0 and ~~ odd 0 is true.                                               *)
Lemma alt_desc_set_1 : alt_desc_set 1 = [set: 'I_1].
Proof.
apply/setP => i; rewrite mem_alt_desc_set inE.
by have /eqP -> : val i == 0%N by rewrite -leqn0 -ltnS ltn_ord.
Qed.

(* euler 1 = beta (alt_desc_set 1) = beta setT = 1 (only [1;0] in S_2).      *)
Lemma euler_1 : euler 1 = 1.
Proof. by rewrite /euler alt_desc_set_1 beta_full. Qed.

Lemma eulerA_2 : eulerA 2 = 1.
Proof. by rewrite /eulerA euler_1. Qed.
