(* perm_seq_basics.v -- psi-free perm <-> seq plumbing.

   Extracted from perm_seq_bridge.v (refactor: separate the §1.4 perm/seq
   bridge from the §1.6.3 cd-index proof of Stanley Prop 1.6.4).

   This file deliberately depends on NO psi_*.v / mmtree.v file, so that
   the §1.4 closure (descent, eulerian, foata, q-analogues) can be built
   without the cd-index machinery.  All proofs that genuinely need
   [psi]/[apply_psis] / [char_mono] / [omega_proper_beta_lt] stay in
   [perm_seq_bridge.v].

   The only new content here (vs. extracting verbatim) is the definition
   of [is_descent_seq], previously defined in [psi_descent_v2.v].  We
   move it here so [foata.v] and the other §1.4 files can use it without
   importing psi_descent_v2.  [psi_descent_v2.v] now imports
   [perm_seq_basics] for the definition. *)

From mathcomp Require Import all_ssreflect fingroup perm.
From mathcomp_eulerian Require Import
  ordinal_reindex perm_compress descent eulerian beta beta_omega beta_bridge.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* ========================================================================= *)
(* §0. Sequence-level descent predicate *)
(* ========================================================================= *)

(** [is_descent_seq w k] is the descent predicate: [k] is a descent of
    [w] iff [w_k > w_{k+1}].  Sequence-level mirror of Stanley's
    [Des(w) = { i : w_i > w_{i+1} }].  Moved here from
    [psi_descent_v2.v] so §1.4 files can use it without importing the
    cd-index machinery. *)
Definition is_descent_seq (w : seq nat) (k : nat) : bool :=
  nth 0 w k > nth 0 w k.+1.

(* ========================================================================= *)
(* §A. perm_to_seq: bijection between {perm 'I_n} and seqs of vals           *)
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
(* §B. Descent equivalence: is_descent <-> is_descent_seq                    *)
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
(* §C. descent_set <-> boolean-vector correspondence                         *)
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
(* §D. Descent positions / set bridge *)
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
(* §E. seq_to_perm: inverse of perm_to_seq *)
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

End SeqToPerm.

(* ========================================================================= *)
(* §F. Round-trip and helper lemmas *)
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

(* [seq_to_perm_perm_to_seq] removed: 0 uses anywhere; cleanup pass.  *)
