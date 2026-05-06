(* q-Eulerian polynomial: bivariate joint generating function for (maj, des).
   Stanley EC1 §1.4.

   A_n(q, t) = \sum_{σ ∈ S_{n+1}} q^{maj(σ)} · t^{des(σ)}

   Specializations:
     A_n(q, 1) = q-factorial [n+1]_q!  (sum over all des-counts, by maj_q_fact)
     A_n(1, t) = classical Eulerian polynomial \sum_k eulerian(n,k) t^k

   Encoded as {poly {poly int}}: outer indeterminate is t, inner is q.
*)

From mathcomp Require Import all_ssreflect fingroup perm ssrint ssralg poly.
From mathcomp_eulerian Require Import ordinal_reindex perm_compress
                                       descent eulerian beta inversions
                                       foata qfact.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.

Open Scope ring_scope.

(* ========================================================================= *)
(* §0. Notations                                                             *)
(* ========================================================================= *)

(* qpow k = q^k, embedded as a constant {poly {poly int}}. *)
Notation qpow k := (('X ^+ k : {poly int})%:P : {poly {poly int}}).

(* ========================================================================= *)
(* §1. Definition of the q-Eulerian polynomial                               *)
(* ========================================================================= *)

(** [q_eul_pol n] is the q-Eulerian polynomial
    [A_n(q,t) = \sum_(sigma in S_{n+1}) q^(maj sigma) * t^(des sigma)],
    the bivariate joint generating function of [maj] and [des] over
    permutations of [n+1] letters.  Stanley EC1 §1.4. *)
Definition q_eul_pol (n : nat) : {poly {poly int}} :=
  \sum_(σ : {perm 'I_n.+1}) qpow (maj σ) * 'X^(des σ).

(* ========================================================================= *)
(* §2. Specialization t = 1: q-factorial                                     *)
(* ========================================================================= *)

(** Specialization [t = 1] of [A_n(q,t)] recovers the q-factorial:
    [A_n(q, 1) = [n+1]_q!].  Direct consequence of [maj_q_fact]. *)
Theorem q_eul_pol_t1 n :
  (q_eul_pol n).[1] = q_fact n.
Proof.
rewrite /q_eul_pol horner_sum.
rewrite -[RHS]maj_q_fact.
apply: eq_bigr => σ _.
rewrite hornerM hornerXn expr1n mulr1.
by rewrite hornerC.
Qed.

(* ========================================================================= *)
(* §3. Classical Eulerian polynomial                                         *)
(* ========================================================================= *)

(** [eul_pol n] is the classical Eulerian polynomial
    [\sum_(k <= n) eulerian(n,k) * t^k], with coefficients the Eulerian
    numbers counting permutations of [n+1] letters by descent count.
    Stanley EC1 §1.4. *)
Definition eul_pol (n : nat) : {poly int} :=
  \sum_(k < n.+1) (eulerian n k)%:R * 'X^k.

(** The descent generating function expressed as the Eulerian polynomial:
    [\sum_(sigma in S_{n+1}) X^(des sigma) = eul_pol n].  Obtained by
    partitioning permutations according to their descent count. *)
Lemma sum_des_eq_eul_pol n :
  \sum_(σ : {perm 'I_n.+1}) 'X^(des σ) = eul_pol n :> {poly int}.
Proof.
rewrite /eul_pol.
pose F (s : {perm 'I_n.+1}) : 'I_n.+1 := Ordinal (leq_ltn_trans (des_le s) (ltnSn n)).
rewrite (partition_big F xpredT) //=.
apply: eq_bigr => k _.
rewrite /eulerian.
under eq_bigl => s do rewrite -val_eqE /F /=.
rewrite -sum1dep_card natr_sum big_distrl /=.
apply: eq_bigr => s /eqP Hs.
by rewrite Hs mul1r.
Qed.

(* ========================================================================= *)
(* §4. Specialization q = 1: classical Eulerian polynomial                   *)
(* ========================================================================= *)

(** [q1_subst] is the substitution [q := 1] on a bivariate polynomial in
    [{poly {poly int}}], implemented by evaluating each inner polynomial
    coefficient at [1]. *)
Definition q1_subst : {poly {poly int}} -> {poly int} :=
  map_poly (horner_eval (1 : int)).

(** Specialization [q = 1] of [A_n(q,t)] recovers the classical Eulerian
    polynomial: [A_n(1, t) = eul_pol n].  Each [q^(maj sigma)] becomes [1],
    leaving the descent generating function. *)
Theorem q_eul_pol_q1 n :
  q1_subst (q_eul_pol n) = eul_pol n.
Proof.
rewrite /q_eul_pol /q1_subst.
rewrite (raddf_sum (map_poly (horner_eval (1 : int)))) /=.
rewrite -sum_des_eq_eul_pol.
apply: eq_bigr => σ _.
rewrite rmorphM /= map_polyXn map_polyC /=.
rewrite /horner_eval hornerXn expr1n.
by rewrite mul1r.
Qed.

(* Verify everything is closed (no axioms). *)
