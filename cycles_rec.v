(* Stirling cycle number recurrence — sketch / stub.

   This file is NOT in _CoqProject.  It exists as a scaffold for the
   classical recurrence

     stirling_c n.+1 k.+1 = n * stirling_c n k.+1 + stirling_c n k

   produced by a three-agent design session (mathematician / Rocq
   expert / devil's advocate, May 2026).  The design converged on a
   `porbits_mul_tperm`-based proof, but a first attempt to lift the
   `tperm × lift_perm` decomposition off the page hit a snag: the
   relationship between `lift_perm ord_max j s` and
   `lift_perm ord_max ord_max s` is subtler than a single tperm
   multiplication captures (the val-shifting in `lift j` vs
   `lift ord_max` interacts non-trivially with the tperm action).

   This file documents the architecture and the hard parts; the
   remaining work needs interactive iteration with rocq_step_multi
   and small-example sanity checks via vm_compute.

   ARCHITECTURE OF THE INTENDED PROOF
   ==================================

   - H1 (HARD, ~80-120 LOC): direct porbits-decomposition of
     [perm.lift_perm ord_max ord_max s].  Show that
       porbits (perm.lift_perm ord_max ord_max s)
         = [set [set ord_max]] :|: [set (lift ord_max) @: P | P in porbits s]
     and conclude `cycle_count (perm.lift_perm ord_max ord_max s) =
                   (cycle_count s).+1`.

   - H2 (~30-50 LOC, given H1): cycle_count under
     [perm.lift_perm ord_max j s] for j != ord_max equals cycle_count s.
     Several routes possible:
     (a) direct porbits decomposition with j-cycle merge,
     (b) via porbits_mul_tperm and a cycle-conjugation argument,
     (c) via an explicit "remove ord_max from cycle" perm
         construction in 'I_n.

   - stirling_fiber lemma (~60 LOC): per fixed value of σ ord_max,
     bijection between {σ ∈ S_{n+1} : σ ord_max = j ∧ cycle_count σ = k.+1}
     and {τ ∈ S_n : cycle_count τ = (k.+1 - δ_{j,ord_max})}.

   - assembly via partition_big over (fun σ => σ ord_max),
     bigD1 ord_max, then big_const for the n other values.

   THE NAME-COLLISION GOTCHA
   =========================

   `perm_compress.v` defines its own `lift_perm` with a different
   signature.  In any file that imports `perm_compress`, the bare
   name resolves to perm_compress's; mathcomp's must be qualified
   as `perm.lift_perm`, `perm.lift_perm_id`, `perm.lift_perm_lift`.

   STATUS
   ======

   See [`docs/plans/INVERSIONS_PLAN.md`](docs/plans/INVERSIONS_PLAN.md)
   for the full §1.3 extension plan.  The completed parts are:
     - cycles.v       (definitions + row sum)
     - inversions.v   (defs + identity values)
     - blueprint chapter ch_inversions.tex

   This file is the scaffold for the next interactive session.
*)
From mathcomp Require Import all_ssreflect fingroup perm.
From mathcomp_eulerian Require Import ordinal_reindex perm_compress descent cycles.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* ========================================================================= *)
(* §H1.  Cycle count of "extend with fixed ord_max" — TO PROVE              *)
(* ========================================================================= *)

(* Strategy: porbit (perm.lift_perm ord_max ord_max s) (lift ord_max k)
             = (lift ord_max) @: (porbit s k)
   (because the lifted perm acts as s on the embedded image, never
    visiting ord_max)
   plus
   porbit (perm.lift_perm ord_max ord_max s) ord_max = [set ord_max]
   (because ord_max is fixed)
   then porbits = singleton union of images, count via card_imset.       *)

(* Lemma cycle_count_lift_perm_id n (s : {perm 'I_n}) :
     cycle_count (perm.lift_perm ord_max ord_max s) = (cycle_count s).+1.
   Admitted. *)

(* ========================================================================= *)
(* §H2.  Cycle count under "lift to j != ord_max" — TO PROVE                *)
(* ========================================================================= *)

(* Lemma cycle_count_lift_perm_swap n (s : {perm 'I_n}) (j : 'I_n.+1) :
     j != ord_max ->
     cycle_count (perm.lift_perm ord_max j s) = cycle_count s.
   Admitted. *)

(* ========================================================================= *)
(* §Bij.  Per-fiber bijection — TO PROVE                                     *)
(* ========================================================================= *)

(* Lemma stirling_fiber n k (j : 'I_n.+1) :
     #|[set s : {perm 'I_n.+1} | (s ord_max == j) && (cycle_count s == k.+1)]|
     = #|[set s : {perm 'I_n} | cycle_count s == (if j == ord_max then k else k.+1)]|.
   Admitted. *)

(* ========================================================================= *)
(* §Rec.  The recurrence itself — TO PROVE                                  *)
(* ========================================================================= *)

(* Lemma stirling_c_rec n k :
     stirling_c n.+1 k.+1 = n * stirling_c n k.+1 + stirling_c n k.
   Admitted. *)
