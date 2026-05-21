(* Stirling cycle number recurrence — partial.

   This file accompanies cycles.v.  The headline target is the
   classical recurrence

     stirling_c n.+1 k.+1 = n * stirling_c n k.+1 + stirling_c n k

   The plan, from a prior design session, is:

   - H1 (DONE in this file): direct porbits-decomposition of
     [perm.lift_perm ord_max ord_max s].  Show that
       porbits (perm.lift_perm ord_max ord_max s)
         = [set [set ord_max]] :|: [set (lift ord_max) @: P | P in porbits s]
     and conclude `cycle_count (perm.lift_perm ord_max ord_max s) =
                   (cycle_count s).+1`.

   - H2 (REJECTED — see §H2 below): the originally-proposed lemma
     [cycle_count (perm.lift_perm ord_max j s) = cycle_count s] for
     j != ord_max is FALSE.  Counterexample: n=2, s=identity, j=0;
     the lifted perm is a single 3-cycle (cycle_count 1) while
     cycle_count s = 2.  The combinatorially-correct construction
     for the j != ord_max class of the Stirling fiber bijection is
     a cycle-insertion operation [insert_after], not [lift_perm];
     this is deferred to a follow-up file [stirling_fiber.v].

   - stirling_fiber lemma + assembly: depends on [insert_after]
     (not on H2 of this file).

   THE NAME-COLLISION GOTCHA
   =========================

   `perm_compress.v` defines its own `lift_perm` with a different
   signature.  In any file that imports `perm_compress`, the bare
   name resolves to perm_compress's; mathcomp's must be qualified
   as `perm.lift_perm`, `perm.lift_perm_id`, `perm.lift_perm_lift`.
*)
From mathcomp Require Import all_ssreflect fingroup perm.
From mathcomp_eulerian Require Import ordinal_reindex perm_compress descent.
From mathcomp_eulerian Require Import cycles.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* ========================================================================= *)
(* §H1.  Cycle count of "extend with fixed ord_max" — PROVED *)
(* ========================================================================= *)

Section H1.
Variable n : nat.
Variable s : {perm 'I_n}.

(** Iterating [perm.lift_perm ord_max ord_max s] at [ord_max] stays at
    [ord_max].  Used in [porbit_lift_perm_id_max]. *)
Lemma lift_perm_id_iter i :
  ((perm.lift_perm ord_max ord_max s) ^+ i)%g ord_max = ord_max.
Proof.
elim: i => [|i IH]; first by rewrite expg0 perm1.
by rewrite expgSr permM IH perm.lift_perm_id.
Qed.

(** The [porbit] of [ord_max] under [perm.lift_perm ord_max ord_max s] is
    the singleton [{ord_max}]. *)
Lemma porbit_lift_perm_id_max :
  porbit (perm.lift_perm ord_max ord_max s) ord_max = [set ord_max].
Proof.
apply/setP=> y; rewrite !inE.
apply/porbitP/eqP.
- by case=> i ->; rewrite lift_perm_id_iter.
- by move=> ->; exists 0; rewrite expg0 perm1.
Qed.

(** Iteration on lifted points commutes with [lift ord_max]: applying
    [(perm.lift_perm ord_max ord_max s)^+i] at [lift ord_max k] is the
    lift of [(s^+i) k]. *)
Lemma lift_perm_id_iter_lift i (k : 'I_n) :
  ((perm.lift_perm ord_max ord_max s) ^+ i)%g (lift ord_max k)
  = lift ord_max ((s ^+ i)%g k).
Proof.
elim: i k => [|i IH] k; first by rewrite !expg0 !perm1.
by rewrite !expgSr !permM IH perm.lift_perm_lift.
Qed.

(** The [porbit] of [lift ord_max k] under the lifted perm is the
    [lift ord_max]-image of the [porbit] of [k] under [s]. *)
Lemma porbit_lift_perm_id_lift (k : 'I_n) :
  porbit (perm.lift_perm ord_max ord_max s) (lift ord_max k)
  = (lift ord_max) @: (porbit s k).
Proof.
apply/setP=> y; apply/porbitP/imsetP.
- case=> i ->; rewrite lift_perm_id_iter_lift.
  by exists ((s ^+ i)%g k); rewrite // mem_porbit.
- case=> z /porbitP[i ->] ->.
  by exists i; rewrite lift_perm_id_iter_lift.
Qed.

(** Decomposition of [porbits (perm.lift_perm ord_max ord_max s)] into
    the singleton orbit [{ord_max}] and the [lift ord_max]-images of
    the orbits of [s].  Used in [cycle_count_lift_perm_id]. *)
Lemma porbits_lift_perm_id :
  porbits (perm.lift_perm ord_max ord_max s)
  = ([set [set ord_max] : {set 'I_n.+1}] :|:
     [set (lift ord_max) @: (P : {set 'I_n}) | P in porbits s])%SET.
Proof.
apply/setP=> P; rewrite !inE.
apply/imsetP/orP.
- case=> y _ ->.
  case: (unliftP ord_max y) => [k -> | ->].
  + right; apply/imsetP.
    exists (porbit s k); first by apply/imsetP; exists k.
    by rewrite porbit_lift_perm_id_lift.
  + by left; rewrite porbit_lift_perm_id_max eqxx.
- case.
  + move=> /eqP ->; exists ord_max => //.
    by rewrite porbit_lift_perm_id_max.
  + case/imsetP=> Q /imsetP[k _ ->] ->.
    exists (lift ord_max k) => //.
    by rewrite porbit_lift_perm_id_lift.
Qed.

(** H1 proper: extending [s] with [ord_max] as a fixed point adds exactly
    one cycle.  Building block for the [j = ord_max] class of the
    Stirling fiber bijection (see [stirling_fiber.v]). *)
Lemma cycle_count_lift_perm_id :
  cycle_count (perm.lift_perm ord_max ord_max s) = (cycle_count s).+1.
Proof.
rewrite /cycle_count porbits_lift_perm_id cardsU1.
rewrite (card_imset _ _) /=; last first.
  move=> P Q /setP eqfPQ; apply/setP=> x.
  by have := eqfPQ (lift ord_max x); rewrite !(mem_imset _ _ lift_inj).
have not_in : [set ord_max] \notin
  [set (lift ord_max) @: (P : {set 'I_n}) | P in porbits s].
  apply/imsetP=> [[Q QinP /setP HQ]].
  have := HQ ord_max; rewrite inE eqxx /= => /esym.
  case/imsetP=> k _ /eqP.
  by rewrite (negbTE (neq_lift _ _)).
by rewrite not_in add1n.
Qed.

End H1.

(* ========================================================================= *)
(* §H2.  Cycle count under "lift to j != ord_max" — UNPROVABLE AS STATED *)
(* ========================================================================= *)

(* The originally-conjectured lemma

     Lemma cycle_count_lift_perm_swap n (s : {perm 'I_n}) (j : 'I_n.+1) :
       j != ord_max ->
       cycle_count (perm.lift_perm ord_max j s) = cycle_count s.

   IS MATHEMATICALLY FALSE.

   Counterexample 1.  n = 2, s = identity on 'I_2 (so cycle_count s = 2),
   j = 0 = lift ord_max ord0.  Compute:
     perm.lift_perm ord_max 0 1 (ord_max=2) = 0
     perm.lift_perm ord_max 0 1 (0)         = lift 0 (s 0) = lift 0 0 = 1
     perm.lift_perm ord_max 0 1 (1)         = lift 0 (s 1) = lift 0 1 = 2
   So the lifted perm is the 3-cycle 2→0→1→2, with cycle_count = 1 ≠ 2.

   Verified mechanically (test_action / test_action2 lemmas above
   established σ(2) = 0 and σ(0) = 1 for this concrete instance).

   ROOT CAUSE.  [perm.lift_perm ord_max j s] is a *renaming* operation:
   it sends [lift ord_max k] to [lift j (s k)], so it changes which value
   sits at each position.  This is NOT the cycle-insertion operation
   needed for the Stirling recurrence.  The combinatorially-correct
   operation is "insert ord_max into s's cycle right after element j0",
   defined for j0 : 'I_n by:
       insert_after j0 s ord_max          = lift ord_max (s j0)
       insert_after j0 s (lift ord_max j0)= ord_max
       insert_after j0 s (lift ord_max k) = lift ord_max (s k)   (k != j0)
   This different perm DOES preserve cycle_count (it splices ord_max into
   the j0-cycle without creating or destroying cycles), and is the right
   building block for the Stirling fiber bijection.

   ACTION ITEM.  The follow-up file [stirling_fiber.v] should:
   (1) define [insert_after j0 s : {perm 'I_n.+1}] as above;
   (2) prove [cycle_count (insert_after j0 s) = cycle_count s];
   (3) prove the Stirling fiber bijection using [insert_after] (NOT
       [lift_perm]) for the j != ord_max class, and [lift_perm
       ord_max ord_max] (i.e. H1 of this file) for the j = ord_max
       class.

   Hence: H1 of this file IS the building block for the j = ord_max
   class, but the j != ord_max class needs a different perm
   construction.  H2 as a lemma about [lift_perm] is abandoned. *)

(* ========================================================================= *)
(* §Bij.  Per-fiber bijection — NOT PROVED
          (depends on a future [insert_after] construction; see §H2 above) *)
(* ========================================================================= *)

(* Lemma stirling_fiber n k (j : 'I_n.+1) :
     #|[set s : {perm 'I_n.+1} | (s ord_max == j) && (cycle_count s == k.+1)]|
     = #|[set s : {perm 'I_n} |
            cycle_count s == (if j == ord_max then k else k.+1)]|.

   For j = ord_max:  bijection [s ↦ perm.lift_perm ord_max ord_max s]
   between [{perm 'I_n} with k cycles] and [{perm 'I_n.+1} fixing ord_max
   with k.+1 cycles].  Cycle-count step is [cycle_count_lift_perm_id]
   (H1) of this file.

   For j != ord_max:  write j = lift ord_max j0.  Bijection
   [(s, j0) ↦ insert_after j0 s] between [{perm 'I_n} with k.+1 cycles] x
   ['I_n] and [{perm 'I_n.+1} sending ord_max to j with k.+1 cycles].
   Needs the [insert_after] lemma described in §H2 above. *)

(* ========================================================================= *)
(* §Rec.  The recurrence itself — NOT PROVED *)
(* ========================================================================= *)

(* Lemma stirling_c_rec n k :
     stirling_c n.+1 k.+1 = n * stirling_c n k.+1 + stirling_c n k. *)
