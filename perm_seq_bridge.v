(* perm_seq_bridge.v -- Bridge between perm/finset world and seq/cd-index world *)
(*                                                                             *)
(* Proves omega_proper_beta_lt (Stanley Prop 1.6.4):                           *)
(*   omega_set D \proper omega_set E -> beta D < beta E                        *)
(*                                                                             *)
(* and beta_swap_lt_caseA (derived from omega_proper_beta_lt).                 *)
(*                                                                             *)
(* Dependencies (from psi_cdindex.v, all proved):                              *)
(*   - fact3: M-class descent patterns = expand_cde(phi_w)                     *)
(*   - strict_witness_exists: witness perm with S_w = {k}                      *)
(*   - omega_monotone_class_count: monotonicity of omega                       *)
(*                                                                             *)
(* No axioms. phi_w_support_general is imported from psi_cdindex.v.            *)
(* char_mono_class_inj (M-class char_mono injectivity) proved from             *)
(* fact3 + uniq_expand_cde.                                                    *)
(*                                                                             *)
(* Build order: beta_bridge.v -> perm_seq_bridge.v -> beta_swap.v.             *)

From mathcomp Require Import all_ssreflect fingroup perm.
From mathcomp_eulerian Require Import
  ordinal_reindex perm_compress descent eulerian beta beta_omega beta_bridge.
Require Import mmtree psi_core psi_comm psi_descent_v2 psi_descent_thms.
Require Import psi_cdindex_core psi_cdindex_witness psi_cdindex_support.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* ========================================================================= *)
(* SA. perm_to_seq: bijection between {perm 'I_n} and seqs of vals          *)
(* ========================================================================= *)

(** [perm_to_seq s] -- bridge from [{perm 'I_n}] to [seq nat]: the
    list [[val (s 0); val (s 1); ...; val (s (n-1))]]. *)
Definition perm_to_seq n (s : {perm 'I_n}) : seq nat :=
  [seq val (s i) | i <- enum 'I_n].

(** [perm_to_seq_size] -- the seq view of a permutation has length
    [n]. *)
Lemma perm_to_seq_size n (s : {perm 'I_n}) : size (perm_to_seq s) = n.
Proof. by rewrite /perm_to_seq size_map size_enum_ord. Qed.

(** [perm_to_seq_uniq] -- the seq view of a permutation has no
    duplicates (since [s] is injective). *)
Lemma perm_to_seq_uniq n (s : {perm 'I_n}) : uniq (perm_to_seq s).
Proof.
rewrite /perm_to_seq map_inj_uniq ?enum_uniq //.
move=> x y /= /val_inj; exact: perm_inj.
Qed.

(** [nth_perm_to_seq] -- accessing [perm_to_seq s] at index [k]
    yields [val (s (Ordinal Hk))]. *)
Lemma nth_perm_to_seq n (s : {perm 'I_n}) k (Hk : k < n) :
  nth 0 (perm_to_seq s) k = val (s (Ordinal Hk)).
Proof.
rewrite /perm_to_seq (nth_map (Ordinal Hk)); last by rewrite size_enum_ord.
congr (val (s _)).
by apply: val_inj => /=; rewrite nth_enum_ord.
Qed.

(** [perm_to_seq_inj] -- the [perm_to_seq] map is injective: distinct
    permutations yield distinct value lists. *)
Lemma perm_to_seq_inj n : injective (@perm_to_seq n).
Proof.
move=> s1 s2 Heq.
apply/permP => i.
have Hi := ltn_ord i.
have H := congr1 (fun w => nth 0 w (val i)) Heq.
rewrite !(nth_perm_to_seq _ Hi) in H.
have Hord : Ordinal Hi = i by apply: val_inj.
by rewrite Hord in H; apply: val_inj.
Qed.

(* ========================================================================= *)
(* SB. Descent equivalence: is_descent <-> is_descent_seq                    *)
(* ========================================================================= *)

(** [is_descent_perm_seq] -- descent equivalence: [is_descent s i]
    (perm side) equals [is_descent_seq (perm_to_seq s) (val i)] (seq
    side). *)
Lemma is_descent_perm_seq n (s : {perm 'I_n.+1}) (i : 'I_n) :
  is_descent s i = is_descent_seq (perm_to_seq s) (val i).
Proof.
rewrite /is_descent /is_descent_seq.
have Hi : val i < n.+1 := leq_trans (ltn_ord i) (leqnSn n).
have Hi1 : (val i).+1 < n.+1.
  by rewrite ltnS; exact: ltn_ord.
rewrite (nth_perm_to_seq s Hi) (nth_perm_to_seq s Hi1).
by congr (_ > _); congr (val (s _)); apply: val_inj.
Qed.

(* ========================================================================= *)
(* SC. descent_set <-> char_mono correspondence                              *)
(* ========================================================================= *)

(** [descent_to_bvec D] -- boolean-vector representation of a descent
    set, indexed by [enum 'I_n]: the [i]-th entry is [(i \in D)]. *)
Definition descent_to_bvec n (D : {set 'I_n}) : seq bool :=
  [seq (i \in D) | i <- enum 'I_n].

(** [size_descent_to_bvec] -- the boolean vector has length [n]. *)
Lemma size_descent_to_bvec n (D : {set 'I_n}) :
  size (descent_to_bvec D) = n.
Proof. by rewrite /descent_to_bvec size_map size_enum_ord. Qed.

(** [nth_descent_to_bvec] -- accessing [descent_to_bvec D] at [k]
    yields [(Ordinal Hk \in D)]. *)
Lemma nth_descent_to_bvec n (D : {set 'I_n}) k (Hk : k < n) :
  nth false (descent_to_bvec D) k = (Ordinal Hk \in D).
Proof.
rewrite /descent_to_bvec (nth_map (Ordinal Hk)); last by rewrite size_enum_ord.
congr (_ \in D).
by apply: val_inj => /=; rewrite nth_enum_ord.
Qed.

(** [char_mono_perm_to_seq] -- the seq-side [char_mono] of
    [perm_to_seq s] equals the perm-side boolean vector of
    [descent_set s]. Bridges [psi_cdindex] descent patterns to perm
    descent sets. *)
Lemma char_mono_perm_to_seq n (s : {perm 'I_n.+1}) :
  char_mono (perm_to_seq s) = descent_to_bvec (descent_set s).
Proof.
apply: (@eq_from_nth _ false).
  by rewrite /char_mono size_map size_iota perm_to_seq_size
             /descent_to_bvec size_map size_enum_ord.
rewrite /char_mono size_map size_iota perm_to_seq_size => k Hk.
rewrite (nth_map 0); last by rewrite size_iota.
rewrite nth_iota // add0n.
rewrite /descent_to_bvec (nth_map (Ordinal Hk)); last by rewrite size_enum_ord.
have -> : nth (Ordinal Hk) (enum 'I_n) k = Ordinal Hk.
  by apply: val_inj => /=; rewrite nth_enum_ord.
rewrite inE.
by symmetry; exact: is_descent_perm_seq.
Qed.

(** [descent_to_bvec_inj] -- two descent sets giving the same
    boolean vector must be equal. *)
Lemma descent_to_bvec_inj n : injective (@descent_to_bvec n).
Proof.
move=> D1 D2 Heq.
apply/setP => i.
have Hi := ltn_ord i.
have Hord : Ordinal Hi = i by apply: val_inj.
have := congr1 (fun v => nth false v (val i)) Heq.
rewrite !nth_descent_to_bvec // Hord.
by move=> ->.
Qed.

(* ========================================================================= *)
(* SD. M-class injectivity                                                   *)
(* ========================================================================= *)

(* phi_w_support_general is now imported from psi_cdindex.v (fully proved). *)

(* -- SD2. psi commutativity with apply_psis ------------------------------ *)

(** [psi_apply_psis_comm] -- the single [psi i] commutes with the
    iterated [apply_psis ss] (on uniq seqs), via [psi_comm]. *)
Lemma psi_apply_psis_comm i ss w :
  uniq w ->
  apply_psis ss (psi i w) = psi i (apply_psis ss w).
Proof.
move=> Hu.
elim: ss w Hu => [|j ss IH] w Hu //=.
rewrite (psi_comm j i Hu).
exact: IH (uniq_psi _ Hu).
Qed.

(** [apply_psis_rev] -- since each [psi i] is involutive and they
    commute, [apply_psis] is independent of the order of the
    operations: [rev ss] gives the same result as [ss]. *)
Lemma apply_psis_rev ss w :
  uniq w ->
  apply_psis (rev ss) w = apply_psis ss w.
Proof.
move=> Hu.
elim: ss w Hu => [|i ss IH] w Hu //=.
by rewrite rev_cons -cats1 apply_psis_cat /= IH // psi_apply_psis_comm.
Qed.

(** [apply_psis_revK] -- applying [ss] then [rev ss] cancels back to
    [w] (each [psi i] is involutive). *)
Lemma apply_psis_revK ss w :
  uniq w ->
  apply_psis (rev ss) (apply_psis ss w) = w.
Proof.
move=> Hu.
elim: ss w Hu => [|i ss IH] w Hu //=.
rewrite -/(apply_psis ss (psi i w)) rev_cons -cats1 apply_psis_cat /=.
rewrite IH; last exact: uniq_psi.
exact: psi_involutive.
Qed.

(** [apply_psis_cancel] -- [apply_psis ss] is its own inverse:
    applying [ss] twice cancels back to [w]. *)
Lemma apply_psis_cancel ss w :
  uniq w ->
  apply_psis ss (apply_psis ss w) = w.
Proof.
move=> Hu.
rewrite -{1}(apply_psis_rev ss (uniq_apply_psis ss Hu)).
exact: apply_psis_revK.
Qed.

(** [powerset_internal_apply_psis] -- the internal-vertex powerset
    used to enumerate the M-class is invariant under [apply_psis];
    consequence of [internal_vertices_apply_psis]. *)
Lemma powerset_internal_apply_psis ops w :
  uniq w ->
  powerset_internal (apply_psis ops w) =
  powerset_internal w.
Proof.
move=> Hu.
by rewrite /powerset_internal
   internal_vertices_apply_psis.
Qed.

(** [class_char_monos_uniq] -- the descent patterns of the M-class
    members of [w] are pairwise distinct (combines [fact3] with
    [uniq_expand_cde]). *)
Lemma class_char_monos_uniq w :
  uniq w ->
  uniq [seq char_mono (apply_psis ss w) | ss <- powerset_internal w].
Proof.
move=> Hu.
have Hfact := fact3 Hu.
rewrite -(sort_uniq leq_seqb) Hfact sort_uniq.
exact: uniq_expand_cde.
Qed.

(** [char_mono_class_inj] -- M-class injectivity: within the M-class
    of [w], two class members with the same descent pattern are
    actually the same sequence. Follows from [fact3] and
    [uniq_expand_cde]. *)
Lemma char_mono_class_inj w ss1 ss2 :
  uniq w ->
  ss1 \in powerset_internal w ->
  ss2 \in powerset_internal w ->
  char_mono (apply_psis ss1 w) =
    char_mono (apply_psis ss2 w) ->
  apply_psis ss1 w = apply_psis ss2 w.
Proof.
move=> Hu Hss1 Hss2 Hcm.
have Huniq_cm := class_char_monos_uniq Hu.
set g := fun ss =>
  char_mono (apply_psis ss w).
set psi_w := powerset_internal w.
have Hn1 :
  ss1 = nth [::] psi_w (index ss1 psi_w).
  by rewrite nth_index.
have Hn2 :
  ss2 = nth [::] psi_w (index ss2 psi_w).
  by rewrite nth_index.
have Hgn1 : g ss1 =
  nth (g [::]) [seq g s | s <- psi_w]
    (index ss1 psi_w).
  rewrite (nth_map [::]); last by rewrite index_mem.
  by rewrite -Hn1.
have Hgn2 : g ss2 =
  nth (g [::]) [seq g s | s <- psi_w]
    (index ss2 psi_w).
  rewrite (nth_map [::]); last by rewrite index_mem.
  by rewrite -Hn2.
have Hidxs : index ss1 psi_w <
  size [seq g s | s <- psi_w].
  by rewrite size_map index_mem.
have Hidxs2 : index ss2 psi_w <
  size [seq g s | s <- psi_w].
  by rewrite size_map index_mem.
have Hcm_idx :
  nth (g [::]) [seq g s | s <- psi_w]
    (index ss1 psi_w) =
  nth (g [::]) [seq g s | s <- psi_w]
    (index ss2 psi_w).
  by rewrite -Hgn1 -Hgn2 /g Hcm.
have := nth_uniq (g [::]) Hidxs Hidxs2
  Huniq_cm.
rewrite Hcm_idx eqxx => /esym/eqP Heq_idx.
have Hss_eq : ss1 = ss2
  by rewrite Hn1 Hn2 Heq_idx.
by rewrite Hss_eq.
Qed.

(* ========================================================================= *)
(* SE. Descent positions / omega bridge for boolean vectors                  *)
(* ========================================================================= *)

(** [desc_positions_bvec] -- the descent positions extracted from the
    boolean vector [descent_to_bvec D] coincide with [set_to_seq D]
    (both sorted-asc lists of positions of [D]). *)
Lemma desc_positions_bvec n (D : {set 'I_n}) :
  [seq i <- iota 0 n | nth false (descent_to_bvec D) i] =
  set_to_seq D.
Proof.
apply: (sorted_eq leq_trans anti_leq).
- by apply: (sorted_filter leq_trans); exact: iota_sorted.
- by rewrite /set_to_seq; apply: sort_sorted; exact: leq_total.
- apply: uniq_perm.
  + by apply: filter_uniq; apply: iota_uniq.
  + exact: uniq_set_to_seq.
  move=> x.
  rewrite mem_filter mem_iota add0n mem_set_to_seq.
  apply/andP/mapP.
  + case=> Hnth Hx.
    exists (Ordinal Hx); last by [].
    by rewrite mem_enum -(nth_descent_to_bvec D Hx).
  + case=> i Hi ->.
    rewrite mem_enum in Hi.
    split; last exact: ltn_ord.
    rewrite (nth_descent_to_bvec D (ltn_ord i)).
    by have -> : Ordinal (ltn_ord i) = i by apply: val_inj.
Qed.

(* ========================================================================= *)
(* SF. seq_to_perm: inverse of perm_to_seq                                  *)
(* ========================================================================= *)

Section SeqToPerm.

Variable n : nat.
Variable w : seq nat.
Hypothesis Hsz : size w = n.
Hypothesis Huniq : uniq w.
Hypothesis Hbnd : all (fun x => x < n) w.

(** [seq_nth_bound] -- under the section hypotheses (uniqness, bound,
    size), every entry of [w] read at an ordinal index is itself
    bounded by [n]. *)
Lemma seq_nth_bound (i : 'I_n) : nth 0 w (val i) < n.
Proof.
have Hi : val i < size w by rewrite Hsz; exact: ltn_ord.
exact: (allP Hbnd _ (mem_nth 0 Hi)).
Qed.

(** [seq_to_fun i] -- the underlying function [i |-> nth 0 w (val i)]
    on ordinals, used to lift a uniq bounded seq to a permutation. *)
Definition seq_to_fun (i : 'I_n) : 'I_n := Ordinal (seq_nth_bound i).

(** [seq_to_fun_inj] -- [seq_to_fun] is injective (uses uniqueness of
    [w]). *)
Lemma seq_to_fun_inj : injective seq_to_fun.
Proof.
move=> i j Heq.
apply/eqP; rewrite -(inj_eq val_inj) /=.
have Hi : val i < size w by rewrite Hsz; exact: ltn_ord.
have Hj : val j < size w by rewrite Hsz; exact: ltn_ord.
rewrite -(nth_uniq 0 Hi Hj Huniq).
suff -> : nth 0 w (val i) = nth 0 w (val j) by [].
by have := congr1 val Heq.
Qed.

(** [seq_to_perm] -- the permutation built from [seq_to_fun]; inverse
    of [perm_to_seq] for uniq, [n]-bounded seqs of length [n]. *)
Definition seq_to_perm : {perm 'I_n} := perm (@seq_to_fun_inj).

(** [seq_to_perm_nth] -- the value of [seq_to_perm] at [i] reads off
    the [val i]-th entry of [w]. *)
Lemma seq_to_perm_nth (i : 'I_n) :
  val (seq_to_perm i) = nth 0 w (val i).
Proof. by rewrite permE. Qed.

End SeqToPerm.

(* ========================================================================= *)
(* SG. Round-trip and helper lemmas                                          *)
(* ========================================================================= *)

(** [perm_to_seq_bnd] -- every entry of [perm_to_seq s] is strictly
    less than [n]. *)
Lemma perm_to_seq_bnd n (s : {perm 'I_n}) :
  all (fun x => x < n) (perm_to_seq s).
Proof. apply/allP => x /mapP [i _ ->]; exact: ltn_ord. Qed.

(** [perm_to_seq_seq_to_perm] -- round-trip identity:
    [perm_to_seq (seq_to_perm w) = w] for uniq, bounded seqs of size
    [n]. *)
Lemma perm_to_seq_seq_to_perm n (w : seq nat)
  (Hsz : size w = n) (Hu : uniq w) (Hb : all (fun x => x < n) w) :
  perm_to_seq (seq_to_perm Hsz Hu Hb) = w.
Proof.
apply: (@eq_from_nth _ 0).
  by rewrite perm_to_seq_size Hsz.
move=> k Hk; rewrite perm_to_seq_size in Hk.
rewrite /perm_to_seq (nth_map (Ordinal Hk)); last by rewrite size_enum_ord.
have Hord : nth (Ordinal Hk) (enum 'I_n) k = Ordinal Hk
  by apply: val_inj => /=; rewrite nth_enum_ord.
by rewrite Hord /= permE /seq_to_fun.
Qed.

(** [seq_to_perm_perm_to_seq] -- other-direction round-trip:
    [seq_to_perm (perm_to_seq s) = s] for any [s : {perm 'I_n}]. *)
Lemma seq_to_perm_perm_to_seq n (s : {perm 'I_n}) :
  seq_to_perm (perm_to_seq_size s) (perm_to_seq_uniq s) (perm_to_seq_bnd s) = s.
Proof.
apply: (perm_to_seq_inj (n:=n)).
by rewrite perm_to_seq_seq_to_perm.
Qed.

(** [all_bnd_apply_psis] -- the boundedness predicate
    [all (< n)] is preserved by [apply_psis] (uses
    [perm_eq_apply_psis]). *)
Lemma all_bnd_apply_psis n ss w :
  all (fun x => x < n) w -> uniq w ->
  all (fun x => x < n) (apply_psis ss w).
Proof.
move=> Hbnd Hu; apply/allP => x Hx.
by apply: (allP Hbnd); rewrite -(perm_mem (perm_eq_apply_psis ss w)).
Qed.

(** [apply_psis_size_eq] -- [apply_psis] preserves size: if [size w =
    n] then [size (apply_psis ss w) = n]. *)
Lemma apply_psis_size_eq n ss (w : seq nat) :
  size w = n -> size (apply_psis ss w) = n.
Proof. move=> <-; exact: size_apply_psis. Qed.

(* ========================================================================= *)
(* SH. expand_cde produces distinct elements                                 *)
(* ========================================================================= *)

(** [uniq_expand_cde] -- [expand_cde] produces a list of pairwise
    distinct boolean vectors (key for M-class injectivity). *)
Lemma uniq_expand_cde letters : uniq (expand_cde letters).
Proof.
elim: letters => [|[||] l IH] //=.
- rewrite cat_uniq !map_inj_uniq //; try by move=> x y [].
  rewrite IH andbT.
  apply/hasPn => x /mapP [t Ht ->].
  by apply/negP => /mapP [t' Ht' []].
- rewrite cat_uniq !map_inj_uniq //; try by move=> x y [] //.
  rewrite IH andbT.
  apply/hasPn => x /mapP [t Ht ->].
  by apply/negP => /mapP [t' Ht' []].
Qed.

(* ========================================================================= *)
(* SI. M-class helpers: membership, uniqueness                               *)
(* ========================================================================= *)

(** [nil_in_powerset_internal] -- the empty list is always a member
    of [powerset_internal w] (the M-class always contains [w]
    itself). *)
Lemma nil_in_powerset_internal w : [::] \in powerset_internal w.
Proof.
rewrite /powerset_internal.
set ivs := internal_vertices w.
have : [::] \in [:: [::] : seq nat] by rewrite mem_seq1.
elim: ivs [:: [::]] => [|i ivs IH] acc Hin //=.
apply: IH.
rewrite mem_cat; apply/orP; left; exact: Hin.
Qed.

(** [char_mono_in_expand_cde] -- the descent pattern of [w] itself
    appears in [expand_cde (phi_w w)] (corresponding to [ss = nil]
    in the [fact3] enumeration). *)
Lemma char_mono_in_expand_cde w :
  uniq w ->
  char_mono w \in expand_cde (phi_w w).
Proof.
move=> Hu.
have Hfact := fact3 Hu.
have : char_mono w \in
  [seq char_mono (apply_psis ss w) | ss <- powerset_internal w].
  apply/mapP; exists [::]; first exact: nil_in_powerset_internal.
  by rewrite apply_psis_nil.
by rewrite -(mem_sort leq_seqb) Hfact mem_sort.
Qed.

(* ========================================================================= *)
(* SJ. find_ss: search for class member with given descent pattern           *)
(* ========================================================================= *)

(** [find_ss w bv] -- search for an [ss] in [powerset_internal w]
    such that [apply_psis ss w] has descent pattern [bv]; returns the
    first match (or [::] if none). *)
Definition find_ss (w : seq nat) (bv : seq bool) : seq nat :=
  head [::] [seq ss <- powerset_internal w | char_mono (apply_psis ss w) == bv].

(** [find_ss_spec] -- whenever [bv] is a descent pattern realized in
    the M-class of [w], [find_ss w bv] returns a valid witness:
    in [powerset_internal w] and yielding the requested pattern. *)
Lemma find_ss_spec w bv :
  uniq w ->
  bv \in expand_cde (phi_w w) ->
  find_ss w bv \in powerset_internal w /\
  char_mono (apply_psis (find_ss w bv) w) = bv.
Proof.
move=> Hu Hbv.
rewrite /find_ss.
have Hmem : bv \in [seq char_mono (apply_psis ss w) | ss <- powerset_internal w].
  by rewrite -(mem_sort leq_seqb) (fact3 Hu) mem_sort.
have [ss Hss Heq] := mapP Hmem.
have Hfilter : ss \in [seq s <- powerset_internal w | char_mono (apply_psis s w) == bv].
  by rewrite mem_filter Hss andbT; apply/eqP.
set flt := [seq s <- _ | _].
have Hfilter' : ss \in flt by rewrite /flt.
have Hhead : head [::] flt \in flt.
  by case: (flt) Hfilter' => [//|x s] _; exact: mem_head.
rewrite mem_filter in Hhead.
by case/andP: Hhead => /eqP.
Qed.

(* ========================================================================= *)
(* SK. class_map: map a perm to the class member with a given descent        *)
(* ========================================================================= *)

(** [class_map bv sigma] -- map a permutation [sigma] to the M-class
    member with descent pattern [bv], packaged back as a perm. The
    core injection used in the proof of [omega_proper_beta_lt]. *)
Definition class_map n (bv : seq bool) (sigma : {perm 'I_n}) : {perm 'I_n} :=
  let w := perm_to_seq sigma in
  let ss := find_ss w bv in
  seq_to_perm (apply_psis_size_eq ss (perm_to_seq_size sigma))
              (uniq_apply_psis ss (perm_to_seq_uniq sigma))
              (all_bnd_apply_psis ss (perm_to_seq_bnd sigma) (perm_to_seq_uniq sigma)).

(** [perm_to_seq_class_map] -- [perm_to_seq] of [class_map bv sigma]
    is exactly [apply_psis (find_ss ... bv) (perm_to_seq sigma)]. *)
Lemma perm_to_seq_class_map n bv (sigma : {perm 'I_n}) :
  perm_to_seq (class_map bv sigma) =
  apply_psis (find_ss (perm_to_seq sigma) bv) (perm_to_seq sigma).
Proof. by rewrite /class_map perm_to_seq_seq_to_perm. Qed.

(* ========================================================================= *)
(* SL. omega bridge helpers                                                  *)
(* ========================================================================= *)

(** [omega_seq_mem_eq] -- the [psi_cdindex] [omega_seq] and the local
    [omega_seq_local] (in [beta_bridge]) agree on memberships
    (definitionally identical). *)
Lemma omega_seq_mem_eq (s : seq nat) k :
  (k \in omega_seq s) = (k \in omega_seq_local s).
Proof. by rewrite /omega_seq /omega_seq_local. Qed.

(** [omega_set_seq_bridge_bounded] -- bridge in the bounded form: for
    [k < m], [k \in omega_seq (set_to_seq D)] iff [Ordinal Hkm \in
    omega_set D]. *)
Lemma omega_set_seq_bridge_bounded m (D : {set 'I_m.+1}) (k : nat) (Hkm : k < m) :
  (k \in omega_seq (set_to_seq D)) = ((Ordinal Hkm) \in omega_set D).
Proof.
rewrite omega_seq_mem_eq.
by rewrite (omega_set_seq_local_bridge D (Ordinal Hkm)).
Qed.

(** [omega_seq_subset_bounded] -- a subset relation on omega-sets
    transports to membership at the seq level for any list of
    bounded indices. *)
Lemma omega_seq_subset_bounded m (D E : {set 'I_m.+1}) (ks : seq nat) :
  omega_set D \subset omega_set E ->
  all (fun k => k < m) ks ->
  all (fun k => k \in omega_seq (set_to_seq D)) ks ->
  all (fun k => k \in omega_seq (set_to_seq E)) ks.
Proof.
move/subsetP => Hsub /allP Hbnd /allP HD.
apply/allP => k Hk.
have Hkm := Hbnd _ Hk.
rewrite (omega_set_seq_bridge_bounded E Hkm).
apply: Hsub.
by rewrite -(omega_set_seq_bridge_bounded D Hkm); apply: HD.
Qed.

(* ========================================================================= *)
(* SM. S_w_seq bound: elements are < (size w).-2                             *)
(* ========================================================================= *)

(** [index_lt_sorted] -- in a uniq sorted list, order on values
    coincides with order on positions: [x < y] iff [index x s <
    index y s]. *)
Lemma index_lt_sorted (s : seq nat) (x y : nat) :
  sorted leq s -> uniq s -> x \in s -> y \in s ->
  (x < y) = (index x s < index y s).
Proof.
move=> Hsorted Hu Hx Hy.
have Hfwd := sorted_ltn_index leq_trans Hsorted.
apply/idP/idP.
- move=> Hlt.
  rewrite ltn_neqAle.
  apply/andP; split.
  + apply/negP => /eqP Heq.
    have Hxy : x = y.
      by have := nth_index 0 Hx; have := nth_index 0 Hy; rewrite Heq => -> ->.
    by rewrite Hxy ltnn in Hlt.
  + rewrite leqNgt; apply/negP => Hgt.
    have := Hfwd _ _ Hy Hx Hgt.
    by move=> Hyx; have := leq_ltn_trans Hyx Hlt; rewrite ltnn.
- move=> Hlt.
  have := Hfwd _ _ Hx Hy Hlt.
  move=> Hle.
  rewrite ltn_neqAle Hle andbT.
  apply/negP => /eqP Heq; subst y.
  by rewrite ltnn in Hlt.
Qed.

(** [window_size_bound] -- the [psi_cdindex] window size at position
    [i] is bounded by [size w - i]. *)
Lemma window_size_bound i w :
  window_size i w <= size w - i.
Proof.
rewrite /window_size.
have [_ H] := window_size_fuel_bound i (leqnn (size w)).
exact: H.
Qed.

(** [S_w_seq_all_lt] -- elements of [S_w_seq w] (the support indices
    of the omega map) are bounded by [(size w).-2]. *)
Lemma S_w_seq_all_lt w :
  2 <= size w ->
  all (fun k => k < (size w).-2) (S_w_seq w).
Proof.
move=> Hsz2.
apply/allP => k /mapP [i].
rewrite mem_filter => /andP [HisD Hiota] ->.
rewrite /classify_vertex_cde in HisD.
case Hint : (is_internal i w); rewrite Hint /= in HisD; last by [].
rewrite /is_internal in Hint.
move/andP: Hint => [Hisz Hws].
rewrite mem_iota in Hiota.
move/andP: Hiota => [H1 _].
have Hbd := window_size_bound i w.
suff Hi_le : i <= (size w).-2.
  by rewrite -ltnS prednK //; rewrite -[X in _ < X]prednK // -subn1 subn_gt0.
rewrite -subn2.
have H2si : 2 <= size w - i by exact: leq_trans Hws Hbd.
have Hisz' : i <= size w
  by apply: ltnW; rewrite -subn_gt0 (leq_trans _ H2si).
by rewrite leq_subRL // addnC -leq_subRL.
Qed.

(* ========================================================================= *)
(* SN. omega_proper_beta_lt -- Stanley Proposition 1.6.4                     *)
(* ========================================================================= *)

(* PROOF STRATEGY:
   1. Construct injection class_map (descent_to_bvec E) on {sigma | descent D}
   2. Show it maps into {tau | descent E}
   3. Show it is injective (via char_mono_class_inj)
   4. Show its image is proper (via strict_witness_exists)
   5. Conclude beta D < beta E by proper_card
*)

(** [omega_proper_beta_lt] -- Stanley EC1 (2nd ed.) Proposition 1.6.4
    at the finset level: a strict inclusion [omega_set D \proper
    omega_set E] of omega-sets implies the strict inequality
    [beta D < beta E] of descent counts. Headline result of this
    file; proof injects {sigma | descent D} into {tau | descent E}
    via the M-class [class_map] and exhibits a strict witness via
    [strict_witness_exists]. *)
Lemma omega_proper_beta_lt : forall m (D E : {set 'I_m.+1}),
  omega_set D \proper omega_set E ->
  beta D < beta E.
Proof.
move=> m D E Hprop.
have [Hsub [k Hkin Hknot]] := properP Hprop.
set bvD := descent_to_bvec D.
set bvE := descent_to_bvec E.
set f := class_map (n:=m.+2) bvE.
(* Step 1: show that for sigma with descent D, bvE is in expand_cde(phi_w(perm_to_seq sigma)) *)
have bvE_in_class : forall sigma : {perm 'I_m.+2}, descent_set sigma = D ->
  bvE \in expand_cde (phi_w (perm_to_seq sigma)).
  move=> sigma HdescD.
  have Huniq := perm_to_seq_uniq sigma.
  have Hsize := perm_to_seq_size sigma.
  (* char_mono(perm_to_seq sigma) = descent_to_bvec D = bvD *)
  have Hcm : char_mono (perm_to_seq sigma) = bvD.
    by rewrite char_mono_perm_to_seq HdescD.
  (* bvD is in expand_cde(phi_w(perm_to_seq sigma)) *)
  have HbvD_in : bvD \in expand_cde (phi_w (perm_to_seq sigma)).
    by rewrite -Hcm; exact: char_mono_in_expand_cde.
  (* By phi_w_support_general: S_w_seq is subset of omega_seq(desc_positions(bvD)) *)
  have Hsz2 : 2 <= size (perm_to_seq sigma) by rewrite Hsize.
  have HszBvD : size bvD = (size (perm_to_seq sigma)).-1.
    by rewrite /bvD size_descent_to_bvec Hsize.
  have Hsupport_D := phi_w_support_general Huniq Hsz2 HszBvD.
  rewrite -/bvD in Hsupport_D.
  have Hrew : (size (perm_to_seq sigma)).-1 = m.+1 by rewrite Hsize.
  have HD_all : all (fun j => j \in omega_seq [seq i <- iota 0 m.+1 | nth false bvD i])
                    (S_w_seq (perm_to_seq sigma)).
    by rewrite -[X in iota 0 X]Hrew -Hsupport_D.
  (* desc_positions(bvD) = set_to_seq D *)
  have Hdesc_D : [seq i <- iota 0 m.+1 | nth false bvD i] = set_to_seq D.
    by rewrite /bvD desc_positions_bvec.
  rewrite Hdesc_D in HD_all.
  (* S_w_seq elements are < m *)
  have Hlt_m : all (fun j => j < m) (S_w_seq (perm_to_seq sigma)).
    have := S_w_seq_all_lt Hsz2.
    apply: sub_all => j.
    by rewrite Hsize.
  (* By omega bridge: omega(D) subset => omega_seq(set_to_seq D) subset *)
  have HE_all : all (fun j => j \in omega_seq (set_to_seq E))
                    (S_w_seq (perm_to_seq sigma)).
    exact: omega_seq_subset_bounded Hsub Hlt_m HD_all.
  (* Reverse bridge: set_to_seq E = desc_positions(bvE) *)
  have Hdesc_E : [seq i <- iota 0 m.+1 | nth false bvE i] = set_to_seq E.
    by rewrite /bvE desc_positions_bvec.
  rewrite -Hdesc_E in HE_all.
  have HszBvE : size bvE = (size (perm_to_seq sigma)).-1.
    by rewrite /bvE size_descent_to_bvec Hsize.
  by rewrite (phi_w_support_general Huniq Hsz2 HszBvE) [X in iota 0 X]Hrew.
(* Step 2: f maps {descent D} into {descent E} *)
have f_descent_E : forall sigma : {perm 'I_m.+2}, descent_set sigma = D ->
  descent_set (f sigma) = E.
  move=> sigma HdescD.
  have Hspec := find_ss_spec (perm_to_seq_uniq sigma) (bvE_in_class sigma HdescD).
  have Hcm : char_mono (perm_to_seq (f sigma)) = bvE.
    by rewrite perm_to_seq_class_map; case: Hspec.
  have := char_mono_perm_to_seq (f sigma).
  rewrite Hcm => /descent_to_bvec_inj.
  by [].
(* Step 3: f is injective on {descent D} *)
have f_inj : {in [set sigma | descent_set sigma == D] &, injective f}.
  move=> sigma1 sigma2.
  rewrite !inE => /eqP Hd1 /eqP Hd2 Hfeq.
  (* perm_to_seq (f sigma1) = perm_to_seq (f sigma2) *)
  have Hseq : perm_to_seq (f sigma1) = perm_to_seq (f sigma2).
    by rewrite Hfeq.
  rewrite !perm_to_seq_class_map in Hseq.
  set w1 := perm_to_seq sigma1 in Hseq *.
  set w2 := perm_to_seq sigma2 in Hseq *.
  set ss1 := find_ss w1 bvE in Hseq *.
  set ss2 := find_ss w2 bvE in Hseq *.
  (* w1 and w2 are both uniq perms of iota 0 (m+2) *)
  have Hu1 := perm_to_seq_uniq sigma1.
  have Hu2 := perm_to_seq_uniq sigma2.
  (* Both have char_mono = bvD *)
  have Hcm1 : char_mono w1 = bvD by rewrite /w1 char_mono_perm_to_seq Hd1.
  have Hcm2 : char_mono w2 = bvD by rewrite /w2 char_mono_perm_to_seq Hd2.
  (* apply_psis ss1 w1 = apply_psis ss2 w2 =: w' *)
  set w' := apply_psis ss1 w1.
  have Hw' : apply_psis ss2 w2 = w'
    by rewrite -Hseq.
  have Hu' : uniq w'
    by apply: uniq_apply_psis.
  (* w1 = apply_psis ss1 w' by cancel *)
  have Hw1_class : w1 = apply_psis ss1 w'.
    by rewrite /w' apply_psis_cancel.
  (* w2 = apply_psis ss2 w' by cancel *)
  have Hw2_class : w2 = apply_psis ss2 w'.
    by rewrite -Hw' apply_psis_cancel.
  (* ss1, ss2 in powerset_internal w' *)
  have Hss1_pw : ss1 \in powerset_internal w'.
    rewrite /ss1 powerset_internal_apply_psis //.
    exact: (find_ss_spec Hu1
      (bvE_in_class sigma1 Hd1)).1.
  have Hss2_pw : ss2 \in powerset_internal w'.
    rewrite /ss2 -Hw' powerset_internal_apply_psis //.
    exact: (find_ss_spec Hu2
      (bvE_in_class sigma2 Hd2)).1.
  (* By char_mono_class_inj: w1 = w2 *)
  have Hw12 : w1 = w2.
    rewrite Hw1_class Hw2_class.
    apply: (char_mono_class_inj Hu' Hss1_pw Hss2_pw).
    by rewrite -Hw1_class -Hw2_class Hcm1 Hcm2.
  (* By perm_to_seq_inj: sigma1 = sigma2 *)
  by apply: perm_to_seq_inj; exact: Hw12.
(* Step 4: image is proper subset of {descent E} *)
(* Use strict_witness_exists: exists w0 with S_w = {val k}, contributing to E but not D *)
have Hkm : val k < m := ltn_ord k.
have Hkm2 : val k < (m.+2).-2 by rewrite /=.
have [w0 [Hu0 [Hsz0 HS0]]] := strict_witness_exists Hkm2.
(* w0 is a perm of some values, size m+2, uniq *)
(* bvE is in expand_cde(phi_w w0) because S_w = {val k} and k in omega(E) *)
have bvE_in_w0 : bvE \in expand_cde (phi_w w0).
  have Hsz2 : 2 <= size w0 by rewrite Hsz0.
  have HszBvE : size bvE = (size w0).-1.
    by rewrite /bvE size_descent_to_bvec Hsz0.
  have Hrew0 : (size w0).-1 = m.+1 by rewrite Hsz0.
  rewrite phi_w_support_general // HS0 /=.
  rewrite andbT.
  (* Need: val k in omega_seq(desc_positions(bvE)) *)
  have Hdesc_E : [seq i <- iota 0 m.+1 | nth false bvE i] = set_to_seq E.
    by rewrite /bvE desc_positions_bvec.
  rewrite [X in iota 0 X]Hrew0 Hdesc_E.
  rewrite (omega_set_seq_bridge_bounded E Hkm).
  by have -> : Ordinal Hkm = k by apply: val_inj.
(* bvD is NOT in expand_cde(phi_w w0) because k not in omega(D) *)
have bvD_notin_w0 : bvD \notin expand_cde (phi_w w0).
  have Hsz2 : 2 <= size w0 by rewrite Hsz0.
  have HszBvD : size bvD = (size w0).-1.
    by rewrite /bvD size_descent_to_bvec Hsz0.
  have Hrew0 : (size w0).-1 = m.+1 by rewrite Hsz0.
  rewrite phi_w_support_general // HS0 /=.
  rewrite andbT.
  have Hdesc_D : [seq i <- iota 0 m.+1 | nth false bvD i] = set_to_seq D.
    by rewrite /bvD desc_positions_bvec.
  rewrite [X in iota 0 X]Hrew0 Hdesc_D.
  rewrite (omega_set_seq_bridge_bounded D Hkm).
  have -> : Ordinal Hkm = k by apply: val_inj.
  by rewrite (negbTE Hknot).
(* w0 has values that might not be iota 0 (m+2), so we need to transfer *)
(* The strict_witness gives a raw seq, not necessarily in iota 0 n *)
(* We need an element of {perm 'I_{m+2}} with descent E not in Im(f) *)
(* For this, we use a different argument: counting. *)
(* From fact3: the M-class of any uniq w of size m+2 has exactly
   |expand_cde(phi_w w)| members, one per descent pattern. *)
(* We establish beta(D) + 1 <= beta(E) by showing:
   |Im(f)| = beta(D) (by injectivity via card_in_imset)
   Im(f) ⊆ {tau | descent E}
   And there exists tau not in Im(f) with descent E *)
(* Step 4a: Show w0 can be made into a perm of iota 0 (m+2) *)
(* Actually, strict_witness_exists gives ANY uniq seq of size m+2.
   We need one that is a perm of iota 0 (m+2).
   Since perm_eq preserves phi_w (by has_left_child_order_iso) and S_w_seq
   (up to appropriate adjustments), we can rank-normalize w0. *)
(* SIMPLER: perm_to_seq gives a perm of iota 0 n, and phi_w depends only on
   relative order. So we need: there exists sigma0 : {perm 'I_{m+2}} such that
   phi_w(perm_to_seq sigma0) = phi_w(w0) (up to rank normalization). *)
(* Actually, let's use a direct approach. We know:
   - f is injective on betaD_set: |Im(f)| = |betaD_set| = beta(D)
   - Im(f) ⊆ betaE_set

   If Im(f) = betaE_set, then beta(D) = beta(E).
   We need to show Im(f) ⊊ betaE_set.

   For this, consider any sigma with descent E in Im(f), say sigma = f(tau) for tau with descent D.
   Then perm_to_seq sigma = apply_psis ss (perm_to_seq tau) for some ss.
   phi_w(perm_to_seq sigma) = phi_w(perm_to_seq tau).
   And bvD ∈ expand_cde(phi_w(perm_to_seq tau)) = expand_cde(phi_w(perm_to_seq sigma)).

   So every sigma in Im(f) has bvD ∈ expand_cde(phi_w(perm_to_seq sigma)).

   But there exists sigma0 with descent E such that bvD ∉ expand_cde(phi_w(perm_to_seq sigma0)).
   This sigma0 is NOT in Im(f).
*)
(* We need: exists sigma0 : {perm 'I_{m+2}} with descent_set = E and
   bvD ∉ expand_cde(phi_w(perm_to_seq sigma0)). *)
(* By strict_witness_exists: w0 uniq, size m+2, S_w = {val k}.
   bvE ∈ expand_cde(phi_w(w0)) and bvD ∉ expand_cde(phi_w(w0)).
   We need to find sigma0 with perm_to_seq sigma0 having the same phi_w as w0. *)
(* Since perm_to_seq is surjective onto perms of iota 0 (m+2), and w0 is
   perm_eq to some perm of iota 0 (m+2) (after rank normalization)... *)
(* Actually, we directly need w0 to be a perm of iota 0 (m+2). *)
(* strict_witness_exists gives witness_perm n k = iota 1 k ++ [k+2; k+1] ++ iota (k+3) (n-k-2).
   This is a perm of [1..n], not [0..n-1]. We need to shift by -1. *)
(* ALTERNATIVELY: use a rank-normalization argument. *)
(* For any uniq w, sort leq w = sort leq (rank_normalize w),
   and phi_w only depends on relative order. *)
(* Let me use a more direct approach. We know w0 is uniq of size m+2.
   Let w0' be the rank-normalization of w0 (a perm of iota 0 (m+2)).
   phi_w(w0') = phi_w(w0) since phi_w depends only on relative order.
   S_w_seq(w0') = S_w_seq(w0) = [val k] similarly. *)
(* Then there exists sigma0 with perm_to_seq(sigma0) = w0'. *)
(* descent_set(sigma0): char_mono(w0') ∈ expand_cde(phi_w(w0')) = expand_cde(phi_w(w0)). *)
(* bvE ∈ expand_cde(phi_w(w0)), so by fact3, some member of class(w0') has char_mono = bvE. *)
(* That member, as a perm, has descent E. *)

(* Let me use a cleaner approach: the image of f on betaD_set is properly contained
   in betaE_set, by showing that any element of Im(f) has bvD in its expand_cde,
   but there exist elements of betaE_set that don't. *)

(* Image characterization: sigma ∈ Im(f|_{betaD_set}) implies
   bvD ∈ expand_cde(phi_w(perm_to_seq sigma)) *)
have img_has_bvD : forall sigma : {perm 'I_m.+2},
  sigma \in [set f tau | tau in [set s | descent_set s == D]] ->
  bvD \in expand_cde (phi_w (perm_to_seq sigma)).
  move=> sigma /imsetP [tau].
  rewrite inE => /eqP Hdtau ->.
  have Hcm : char_mono (perm_to_seq tau) = bvD
    by rewrite char_mono_perm_to_seq Hdtau.
  rewrite perm_to_seq_class_map.
  rewrite phi_w_apply_psis //.
    by rewrite -Hcm; exact: (char_mono_in_expand_cde (perm_to_seq_uniq tau)).
  exact: perm_to_seq_uniq.
(* Now we need a sigma with descent E but bvD ∉ expand_cde(phi_w(perm_to_seq sigma)). *)
(* Use w0 from strict_witness_exists. We need it as a perm of iota 0 (m+2). *)
(* w0 = witness_perm (m+2) (val k), which is a perm of [1..m+2].
   Subtracting 1 from each element gives a perm of [0..m+1] = iota 0 (m+2). *)
(* But the definitions are opaque; let me use perm_eq properties. *)
(* Since w0 is uniq of size m+2, let w0_norm = [seq (index x (sort leq w0)) | x <- w0].
   This is a perm of iota 0 (m+2), and it's order-isomorphic to w0. *)
(* phi_w(w0_norm) = phi_w(w0) by order-isomorphism invariance. *)
(* S_w_seq(w0_norm) = S_w_seq(w0) similarly. *)

(* For now, we bound beta(D) and beta(E) using the cardinality of Im(f). *)
(* |Im(f)| = beta(D) by injectivity *)
(* Im(f) ⊆ betaE_set *)
(* For strictness: we need |Im(f)| < |betaE_set|, i.e., Im(f) ⊊ betaE_set. *)

(* Im(f) ⊆ betaE_set *)
have img_sub : [set f tau | tau in [set s | descent_set s == D]]
               \subset [set s | descent_set s == E].
  apply/subsetP => sigma /imsetP [tau].
  rewrite !inE => /eqP Hdtau ->.
  by apply/eqP; exact: f_descent_E.

(* |Im(f)| = beta(D) *)
have card_img : #|[set f tau | tau in [set s | descent_set s == D]]| = beta D.
  by rewrite /beta (card_in_imset f_inj).

(* We need Im(f) ⊊ betaE_set *)
(* For this we show: exists sigma_new in betaE_set \ Im(f). *)
(* We need a perm with descent E whose phi_w doesn't support bvD. *)
(* Use w0 from strict_witness_exists. w0 is uniq, size m+2, S_w = {val k}. *)
(* We need a perm sigma0 of 'I_{m+2} such that phi_w(perm_to_seq sigma0) = phi_w(w0). *)
(* Define sigma0 via rank normalization of w0. *)

(* Rank normalization: map each element to its rank in sorted order *)
(* For uniq w0 of size m+2, the rank normalization is a perm of iota 0 (m+2). *)
set w0_sorted := sort leq w0.
set w0_norm := [seq index x w0_sorted | x <- w0].
(* w0_norm is uniq, size m+2, and a perm of iota 0 (m+2) *)
have Hsz_norm : size w0_norm = m.+2.
  by rewrite /w0_norm size_map Hsz0.
have Huniq_norm : uniq w0_norm.
  rewrite /w0_norm map_inj_in_uniq //.
  move=> x y Hx Hy Hxy.
  have Hx' : x \in w0_sorted by rewrite mem_sort.
  have Hy' : y \in w0_sorted by rewrite mem_sort.
  by apply: (index_inj 0 (s:=w0_sorted)).
have Hbnd_norm : all (fun x => x < m.+2) w0_norm.
  apply/allP => x /mapP [y Hy ->].
  rewrite -Hsz0 -(size_sort leq) index_mem.
  by rewrite mem_sort.
(* phi_w(w0_norm) = phi_w(w0) by order-isomorphism *)
(* This follows from has_left_child_order_iso + window_size invariance *)
(* For now, we use the fact that the relative order is preserved *)
have Horder_iso : forall p q : nat, p < size w0 -> q < size w0 ->
  (nth 0 w0 p < nth 0 w0 q) = (nth 0 w0_norm p < nth 0 w0_norm q).
  move=> p q Hp Hq.
  rewrite /w0_norm !(nth_map 0) //;
    try by rewrite -Hsz0; first [exact: Hp | exact: Hq].
  set sp := nth 0 w0 p; set sq := nth 0 w0 q.
  have Hsp : sp \in w0 by apply: mem_nth.
  have Hsq : sq \in w0 by apply: mem_nth.
  have Hsp_s : sp \in w0_sorted by rewrite mem_sort.
  have Hsq_s : sq \in w0_sorted by rewrite mem_sort.
  have Huniq_sorted : uniq w0_sorted by rewrite sort_uniq.
  have Hsorted : sorted leq w0_sorted
    by apply: sort_sorted; exact: leq_total.
  exact: index_lt_sorted Hsorted Huniq_sorted Hsp_s Hsq_s.
(* Convert w0_norm to a perm *)
set sigma0 := seq_to_perm Hsz_norm Huniq_norm Hbnd_norm.
have Hpts0 : perm_to_seq sigma0 = w0_norm.
  by rewrite perm_to_seq_seq_to_perm.
(* phi_w(perm_to_seq sigma0) depends only on relative order *)
(* phi_w(w0_norm) = phi_w(w0) because order-isomorphism preserves
   has_left_child (via has_left_child_order_iso) and window_size
   (via window_size_order_iso or similar) *)
(* For the general statement, we need phi_w_order_iso, which may need to be proved. *)
(* Actually, let me check if this is already available... *)
(* phi_w depends on classify_vertex_cde, which depends on is_internal and has_left_child.
   is_internal depends on window_size. Both window_size and has_left_child are
   order-isomorphism invariant (proved in psi_cdindex.v). *)
(* We need: phi_w is order-isomorphism invariant. This means:
   for w1, w2 of same size, uniq, with same relative order at all positions,
   phi_w(w1) = phi_w(w2). *)
(* This follows from classify_vertex_cde being order-invariant. *)
(* Let me introduce this as a derived fact. *)

(* First, check S_w_seq(w0_norm) = S_w_seq(w0) *)
(* S_w_seq depends on classify_vertex_cde, which depends on is_internal and has_left_child.
   Both are order-invariant. So S_w_seq is order-invariant. *)

(* For now, let me just show bvD ∉ expand_cde(phi_w(perm_to_seq sigma0)) *)
(* and bvE ∈ expand_cde(phi_w(perm_to_seq sigma0)) *)

(* Actually, showing phi_w(w0_norm) = phi_w(w0) requires proving that
   classify_vertex_cde is order-invariant. This in turn requires showing that
   window_size is order-invariant (in addition to has_left_child_order_iso). *)

(* Let me check if window_size_order_iso exists... *)
(* From psi_cdindex.v, we have window_size_apply_psis (line 666), but that's
   for apply_psis, not general order isomorphism. *)

(* ALTERNATIVE: Instead of rank normalization, use the fact that w0 is already
   a specific permutation (witness_perm n k = iota 1 k ++ [k+2; k+1] ++ iota (k+3) (n-k-2)).
   This is a perm of [1..n]. Subtracting 1 gives a perm of [0..n-1]. *)
(* But subtraction changes the actual values, not just the relative order. *)

(* SIMPLEST APPROACH: Show that for ANY uniq w of size m+2, if bvE ∈ expand_cde(phi_w w)
   then there exists a perm sigma with descent E in the M-class of the rank-normalization of w.
   And this perm is not in Im(f) if bvD ∉ expand_cde(phi_w w). *)

(* This is getting very complex. Let me use a cleaner argument. *)

(* CLEAN ARGUMENT for beta(D) < beta(E):

   We already showed:
   (a) |Im(f)| = beta(D)  [card_img]
   (b) Im(f) ⊆ betaE_set  [img_sub]

   So beta(D) = |Im(f)| ≤ |betaE_set| = beta(E).

   For strictness, we need |Im(f)| < |betaE_set|, i.e., betaE_set ⊄ Im(f).

   Every sigma in Im(f) satisfies: bvD ∈ expand_cde(phi_w(perm_to_seq sigma))  [img_has_bvD].

   So it suffices to find sigma_new ∈ betaE_set with bvD ∉ expand_cde(phi_w(perm_to_seq sigma_new)).

   Since w0 is uniq, size m+2, and w0_norm is order-isomorphic and a perm of iota 0 (m+2):
   - perm_to_seq sigma0 = w0_norm
   - phi_w(w0_norm) = phi_w(w0) (by order isomorphism invariance)
   - S_w_seq(w0_norm) = S_w_seq(w0) = [val k]

   So bvE ∈ expand_cde(phi_w(w0_norm)) and bvD ∉ expand_cde(phi_w(w0_norm)).

   By fact3: the M-class of w0_norm contains a member with char_mono = bvE.
   That member, as a perm (via seq_to_perm), has descent E.
   And its phi_w = phi_w(w0_norm), so bvD ∉ expand_cde(phi_w(...)).
   Hence it's not in Im(f).
*)

(* For the phi_w order-isomorphism invariance, we need a proved lemma. *)
(* Let me prove it inline. *)

have phi_w_order_iso : forall (s1 s2 : seq nat),
  size s1 = size s2 -> uniq s1 -> uniq s2 ->
  (forall p q, p < size s1 -> q < size s1 ->
    (nth 0 s1 p < nth 0 s1 q) = (nth 0 s2 p < nth 0 s2 q)) ->
  phi_w s1 = phi_w s2.
  move=> s1 s2 Hszeq Hu1 Hu2 Hord.
  (* phi_w = filter non-E from phi'_w = [classify_vertex_cde i s | i <- iota 0 (size s)] *)
  (* classify_vertex_cde depends on is_internal (window_size) and has_left_child *)
  (* Both are order-invariant *)
  rewrite /phi_w /phi'_w Hszeq.
  congr (filter _ _).
  apply: eq_map => i.
  rewrite /classify_vertex_cde.
  (* is_internal depends on window_size, which is determined by mm_pos recursion *)
  (* We need: is_internal i s1 = is_internal i s2 *)
  (* and has_left_child i s1 = has_left_child i s2 *)
  have Hint : is_internal i s1 = is_internal i s2.
    rewrite /is_internal Hszeq.
    case Hisz: (i < size s2) => //=.
    by rewrite (window_size_order_iso i Hszeq Hu1 Hu2 Hord).
  rewrite Hint.
  case: (is_internal i s2) => //=.
  by rewrite (has_left_child_order_iso i Hszeq Hu1 Hu2 Hord).

(* Rank-normalization lemmas needed for phi_w and S_w_seq invariance *)
have Hsz_norm' : size w0_norm = size w0.
  by rewrite /w0_norm size_map.
have Hord_rev : forall p' q', p' < size w0_norm -> q' < size w0_norm ->
  (nth 0 w0_norm p' < nth 0 w0_norm q') = (nth 0 w0 p' < nth 0 w0 q').
  move=> p' q'; rewrite Hsz_norm' => Hp' Hq'.
  by rewrite (Horder_iso p' q' Hp' Hq').

(* Now use phi_w_order_iso *)
have Hphi_w0 : phi_w w0_norm = phi_w w0.
  apply: phi_w_order_iso; [exact: Hsz_norm' | exact: Huniq_norm
    | exact: Hu0 | exact: Hord_rev].

(* S_w_seq is also order-invariant (same argument) *)
have HS_w0 : S_w_seq w0_norm = S_w_seq w0.
  rewrite /S_w_seq Hsz_norm'.
  congr (map _ _).
  apply: eq_in_filter => i _.
  rewrite /classify_vertex_cde.
  have Hint : is_internal i w0_norm = is_internal i w0.
    rewrite /is_internal Hsz_norm'.
    case Hisz: (i < size w0) => //=.
    by rewrite (window_size_order_iso i Hsz_norm' Huniq_norm Hu0 Hord_rev).
  rewrite Hint.
  case: (is_internal i w0) => //=.
  by rewrite (has_left_child_order_iso i Hsz_norm' Huniq_norm Hu0 Hord_rev).

(* bvE ∈ expand_cde(phi_w(perm_to_seq sigma0)) *)
have HbvE_sigma0 : bvE \in expand_cde (phi_w (perm_to_seq sigma0)).
  by rewrite Hpts0 Hphi_w0.

(* bvD ∉ expand_cde(phi_w(perm_to_seq sigma0)) *)
have HbvD_not_sigma0 : bvD \notin expand_cde (phi_w (perm_to_seq sigma0)).
  by rewrite Hpts0 Hphi_w0.

(* Find sigma_new with descent E from the M-class of sigma0 *)
set ss_new := find_ss (perm_to_seq sigma0) bvE.
have [Hss_new Hcm_new] := find_ss_spec (perm_to_seq_uniq sigma0) HbvE_sigma0.
set w_new := apply_psis ss_new (perm_to_seq sigma0).
have Hsz_new : size w_new = m.+2.
  by rewrite /w_new size_apply_psis perm_to_seq_size.
have Huniq_new : uniq w_new.
  by apply: uniq_apply_psis; exact: perm_to_seq_uniq.
have Hbnd_new : all (fun x => x < m.+2) w_new.
  by apply: all_bnd_apply_psis; [exact: perm_to_seq_bnd | exact: perm_to_seq_uniq].
set sigma_new := seq_to_perm Hsz_new Huniq_new Hbnd_new.
have Hpts_new : perm_to_seq sigma_new = w_new.
  by rewrite perm_to_seq_seq_to_perm.

(* descent_set sigma_new = E *)
have Hdesc_new : descent_set sigma_new = E.
  have Hcm : char_mono (perm_to_seq sigma_new) = bvE.
    by rewrite Hpts_new.
  have := char_mono_perm_to_seq sigma_new.
  rewrite Hcm => /descent_to_bvec_inj.
  by [].

(* sigma_new is not in Im(f) *)
have Hnotin : sigma_new \notin [set f tau | tau in [set s | descent_set s == D]].
  apply/negP => /imsetP [tau].
  rewrite inE => /eqP Hdtau Heq.
  have Hsigma_in : sigma_new \in [set f tau' | tau' in [set s | descent_set s == D]].
    by apply/imsetP; exists tau => //; rewrite inE Hdtau.
  have Habs : bvD \in expand_cde (phi_w (perm_to_seq sigma_new))
    by exact: img_has_bvD Hsigma_in.
  move: Habs.
  rewrite Hpts_new /w_new phi_w_apply_psis;
    last by exact: perm_to_seq_uniq.
  by rewrite Hpts0 Hphi_w0 (negbTE bvD_notin_w0).

(* sigma_new ∈ betaE_set *)
have Hin_E : sigma_new \in [set s | descent_set s == E].
  by rewrite inE Hdesc_new.

(* Im(f) ⊊ betaE_set *)
have Hproper : [set f tau | tau in [set s | descent_set s == D]]
               \proper [set s | descent_set s == E].
  rewrite properEcard img_sub /=.
  apply: (@leq_ltn_trans #|[set s | descent_set s == E] :\ sigma_new|).
    apply: subset_leq_card.
    apply/subsetP => x Hx.
    rewrite in_setD1.
    apply/andP; split.
      apply/negP => /eqP Heq; subst x.
      by move: Hnotin; rewrite Hx.
    exact: (subsetP img_sub _ Hx).
  by rewrite [X in _ < X](cardsD1 sigma_new) Hin_E ltnS leqnn.

(* Conclude *)
rewrite -card_img.
exact: proper_card Hproper.
Qed.

(* ========================================================================= *)
(* SG. beta_swap_lt_caseA (fully proved from omega_proper_beta_lt)           *)
(* ========================================================================= *)

(** [beta_swap_lt_caseA] -- Case A of the beta-swap lemma: when
    [i,j \in D] with [j = i+1] and the successor of [j] (if defined)
    is also in [D], toggling [j] strictly increases [beta]. Combines
    [toggle_at_j_omega_strict_superset] with [omega_proper_beta_lt]. *)
Lemma beta_swap_lt_caseA : forall n (D : {set 'I_n}) (i j : 'I_n),
  val j = (val i).+1 -> i \in D -> j \in D ->
  (forall q : 'I_n, val q = (val j).+1 -> q \in D) ->
  beta D < beta (toggle_at D j).
Proof.
move=> n D i j Hj Hi Hjin Hsucc.
case: n D i j Hj Hi Hjin Hsucc => [|m] D i j Hj Hi Hjin Hsucc.
- by have := ltn_ord i; rewrite ltn0.
- apply: (omega_proper_beta_lt (m := m)).
  exact: toggle_at_j_omega_strict_superset Hj Hi Hjin Hsucc.
Qed.
