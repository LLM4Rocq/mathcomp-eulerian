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

   - H2 (STUBBED): cycle_count under [perm.lift_perm ord_max j s]
     for j != ord_max equals cycle_count s.  Attempted via
     `porbits_mul_tperm`; the natural conjugation identity does not
     hold cleanly, and a direct porbits-of-merged-cycle proof would
     be of similar size to H1.  Left for follow-up.

   - stirling_fiber lemma + assembly: depends on H2.

   THE NAME-COLLISION GOTCHA
   =========================

   `perm_compress.v` defines its own `lift_perm` with a different
   signature.  In any file that imports `perm_compress`, the bare
   name resolves to perm_compress's; mathcomp's must be qualified
   as `perm.lift_perm`, `perm.lift_perm_id`, `perm.lift_perm_lift`.
*)
From mathcomp Require Import all_ssreflect fingroup perm.
From mathcomp_eulerian Require Import ordinal_reindex perm_compress descent cycles.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* ========================================================================= *)
(* §H1.  Cycle count of "extend with fixed ord_max" — PROVED                 *)
(* ========================================================================= *)

Section H1.
Variable n : nat.
Variable s : {perm 'I_n}.

(* Iterating the lifted perm at ord_max stays at ord_max. *)
Lemma lift_perm_id_iter i :
  ((perm.lift_perm ord_max ord_max s) ^+ i)%g ord_max = ord_max.
Proof.
elim: i => [|i IH]; first by rewrite expg0 perm1.
by rewrite expgSr permM IH perm.lift_perm_id.
Qed.

(* The orbit of ord_max under the lifted perm is the singleton {ord_max}. *)
Lemma porbit_lift_perm_id_max :
  porbit (perm.lift_perm ord_max ord_max s) ord_max = [set ord_max].
Proof.
apply/setP=> y; rewrite !inE.
apply/porbitP/eqP.
- by case=> i ->; rewrite lift_perm_id_iter.
- by move=> ->; exists 0; rewrite expg0 perm1.
Qed.

(* Iteration on lifted points commutes with lift. *)
Lemma lift_perm_id_iter_lift i (k : 'I_n) :
  ((perm.lift_perm ord_max ord_max s) ^+ i)%g (lift ord_max k)
  = lift ord_max ((s ^+ i)%g k).
Proof.
elim: i k => [|i IH] k; first by rewrite !expg0 !perm1.
by rewrite !expgSr !permM IH perm.lift_perm_lift.
Qed.

(* The orbit of [lift ord_max k] under the lifted perm is the lift
   of the orbit of k under s. *)
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

(* Decomposition of the porbits set into singleton {ord_max} and
   the image of the porbits of s under [lift ord_max]. *)
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

(* H1 proper: extending s with ord_max as a fixed point adds one cycle. *)
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
(* §H2.  Cycle count under "lift to j != ord_max" — NOT PROVED               *)
(* ========================================================================= *)

(* Lemma cycle_count_lift_perm_swap n (s : {perm 'I_n}) (j : 'I_n.+1) :
     j != ord_max ->
     cycle_count (perm.lift_perm ord_max j s) = cycle_count s.

   Approach attempted: express
     perm.lift_perm ord_max j s = (tperm ord_max j) * (perm.lift_perm ord_max ord_max s)
   and apply [porbits_mul_tperm] together with H1.

   This identity is FALSE: at [lift ord_max k], the LHS is [lift j (s k)]
   while the RHS is [tperm ord_max j (lift ord_max (s k))], and the latter
   only equals [lift j (s k)] when [s k != j0] (where [j = lift ord_max j0]).

   A clean proof would either:
   (a) directly decompose the porbits of [perm.lift_perm ord_max j s]
       (one cycle through ord_max merging with the s-cycle of j0, all
       other cycles lifted unchanged); or
   (b) construct an explicit auxiliary [s'] in 'I_n with a tperm-twist
       so that the conjugation identity holds.

   Both are substantial; deferred. *)

(* ========================================================================= *)
(* §Bij.  Per-fiber bijection — NOT PROVED (depends on H2)                   *)
(* ========================================================================= *)

(* Lemma stirling_fiber n k (j : 'I_n.+1) :
     #|[set s : {perm 'I_n.+1} | (s ord_max == j) && (cycle_count s == k.+1)]|
     = #|[set s : {perm 'I_n} | cycle_count s == (if j == ord_max then k else k.+1)]|.
   *)

(* ========================================================================= *)
(* §Rec.  The recurrence itself — NOT PROVED                                 *)
(* ========================================================================= *)

(* Lemma stirling_c_rec n k :
     stirling_c n.+1 k.+1 = n * stirling_c n k.+1 + stirling_c n k. *)
