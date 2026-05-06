(* psi_cdindex_support_defs.v — cd-index support definitions and small lemmas *)
(*                                                                            *)
(* Split from psi_cdindex_support.v so that downstream heavy support proofs   *)
(* depend on a compact, separately checked API for cd-word widths, D-offsets, *)
(* expansion membership, and transition/omega bridges.                        *)

From mathcomp Require Import all_ssreflect.
Require Import mmtree psi_core psi_comm psi_descent_v2 psi_descent_thms.
Require Import psi_cdindex_core psi_cdindex_witness.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* -- D-offsets: cumulative bit-offset of each letter in a cd-word --------- *)
(* C contributes 1 bit, D contributes 2 bits, E contributes 0 bits.         *)

(** [cde_width l] is the number of bits a single cd-letter contributes to
    [expand_cde]: [C] contributes 1, [D] contributes 2, [E] contributes 0. *)
Definition cde_width (l : cde) : nat :=
  match l with C_letter => 1 | D_letter => 2 | E_letter => 0 end.

(** [cde_total_width m] is the bit-length of every element of
    [expand_cde m]; equals the sum of [cde_width] over [m]. *)
Definition cde_total_width (m : seq cde) : nat :=
  sumn [seq cde_width l | l <- m].

(** [cde_offset m i] is the cumulative bit-offset where the [i]-th letter
    of [m] starts in any element of [expand_cde m]. *)
Definition cde_offset (m : seq cde) (i : nat) : nat :=
  sumn [seq cde_width l | l <- take i m].

(** [D_offsets m] enumerates the bit positions where each [D] in [m]
    starts; these are exactly the indices at which an expansion must
    have a transition (the two bits of [d] differ). *)
Definition D_offsets (m : seq cde) : seq nat :=
  [seq cde_offset m i | i <- iota 0 (size m)
                       & is_D_letter (nth C_letter m i)].

(** [has_transition X k] holds iff bits [k] and [k.+1] of [X] differ. *)
Definition has_transition (X : seq bool) (k : nat) : bool :=
  nth false X k != nth false X k.+1.

(** [all_D_transitions m X] holds iff [X] has a bit transition at every
    [D]-offset of [m]; characterizes membership in [expand_cde m]. *)
Definition all_D_transitions (m : seq cde) (X : seq bool) : bool :=
  all (fun k => has_transition X k) (D_offsets m).

(** Every element of [expand_cde m] has length [cde_total_width m]. *)
Lemma size_in_expand_cde m X :
  X \in expand_cde m -> size X = cde_total_width m.
Proof.
elim: m X => [|[||] m IH] X /=.
- by rewrite mem_seq1 => /eqP ->.
- rewrite mem_cat => /orP [Hm|Hm];
    case/mapP: Hm => t Ht -> /=; by rewrite (IH t Ht).
- rewrite mem_cat => /orP [Hm|Hm];
    case/mapP: Hm => t Ht -> /=; by rewrite (IH t Ht).
- exact: IH.
Qed.

(* -- Core: expand_cde membership as D-transition condition ---------------- *)
(* Forward: membership implies transitions at all D-offsets.                *)

(** Cons-shift for [has_transition]: bumping the index by 1 corresponds
    to dropping a leading bit. *)
Lemma has_transition_cons b s k :
  has_transition (b :: s) k.+1 = has_transition s k.
Proof. by rewrite /has_transition. Qed.

(** Cons-shift by 2 for [has_transition]: dropping two leading bits. *)
Lemma has_transition_cons2 b1 b2 s k :
  has_transition (b1 :: b2 :: s) k.+2 = has_transition s k.
Proof. by rewrite /has_transition. Qed.

(** Cons-unfolding for [cde_offset] over a [C] head: shift by 1 bit. *)
Lemma cde_offset_C_succ m j :
  cde_offset (C_letter :: m) j.+1 = (cde_offset m j).+1.
Proof. by rewrite /cde_offset /= /cde_width. Qed.

(** Cons-unfolding for [cde_offset] over a [D] head: shift by 2 bits. *)
Lemma cde_offset_D_succ m j :
  cde_offset (D_letter :: m) j.+1 = (cde_offset m j).+2.
Proof. by rewrite /cde_offset /= /cde_width. Qed.

(** Forward direction of the transition characterisation: every [X] in
    [expand_cde m] has the required bit transitions at all [D]-offsets. *)
Lemma expand_cde_mem_transitions m X :
  X \in expand_cde m -> all_D_transitions m X.
Proof.
elim: m X => [|[||] m IH] X //=.
- (* C_letter: after /= the filter starts at iota 1 (size m) *)
  rewrite mem_cat => /orP [Hm|Hm];
    case/mapP: Hm => t Ht ->;
    rewrite /all_D_transitions /D_offsets /=;
    apply/allP => k;
    case/mapP => j; rewrite mem_filter mem_iota =>
      /andP [Hd /andP [Hj1 Hjsz]] ->;
    (case: j Hj1 Hd Hjsz => [//|j0] _ Hd Hjsz;
     rewrite cde_offset_C_succ has_transition_cons;
     have Hall := allP (IH t Ht) (cde_offset m j0);
     rewrite /all_D_transitions /D_offsets in Hall;
     apply: Hall;
     apply/mapP; exists j0; last done;
     by rewrite mem_filter mem_iota; apply/andP; split; first done;
        apply/andP; split; first by []).
- (* D_letter: after /= the 0 case is solved, rest uses iota 1 (size m) *)
  rewrite mem_cat => /orP [Hm|Hm];
    case/mapP: Hm => t Ht ->;
    rewrite /all_D_transitions /D_offsets /=;
    apply/allP => k;
    case/mapP => j; rewrite mem_filter mem_iota =>
      /andP [Hd /andP [Hj1 Hjsz]] ->;
    (case: j Hj1 Hd Hjsz => [//|j0] _ Hd Hjsz;
     rewrite cde_offset_D_succ has_transition_cons2;
     have Hall := allP (IH t Ht) (cde_offset m j0);
     rewrite /all_D_transitions /D_offsets in Hall;
     apply: Hall;
     apply/mapP; exists j0; last done;
     by rewrite mem_filter mem_iota; apply/andP; split;
        first (by move: Hd => /=); apply/andP; split; first by []).
- (* E_letter: cde_width E = 0, offsets shift by 0 *)
  rewrite /all_D_transitions /D_offsets /=.
  move=> HX; apply/allP => k.
  case/mapP => j; rewrite mem_filter mem_iota =>
    /andP [Hd /andP [Hj1 Hjsz]] ->.
  case: j Hj1 Hd Hjsz => [//|j0] _ Hd Hjsz.
  rewrite /cde_offset /= /cde_width add0n.
  have Hall := allP (IH X HX) (cde_offset m j0).
  rewrite /all_D_transitions /D_offsets in Hall.
  apply: Hall; apply/mapP; exists j0; last done.
  by rewrite mem_filter mem_iota; apply/andP; split;
     first (by move: Hd => /=); apply/andP; split; first by [].
Qed.

(* Backward: correct size + transitions at D-offsets implies membership.    *)

(** Backward direction: any bit-string of the right length with [D]-offset
    transitions is a member of [expand_cde m]. *)
Lemma transitions_expand_cde_mem m X :
  size X = cde_total_width m ->
  all_D_transitions m X ->
  X \in expand_cde m.
Proof.
elim: m X => [|[||] m IH] X /=.
- by move=> /size0nil ->.
- (* C_letter *)
  case: X => [// | b X] /= [HszX] Hall.
  rewrite mem_cat; apply/orP.
  have HallT : all_D_transitions m X.
    rewrite /all_D_transitions /D_offsets.
    apply/allP => k /mapP [j Hj ->].
    move: Hall; rewrite /all_D_transitions /D_offsets /=.
    move/allP => Hall2.
    have Hin : cde_offset (C_letter :: m) j.+1 \in
      [seq cde_offset (C_letter :: m) i
      | i <- iota 0 (size m).+1
      & is_D_letter (nth C_letter (C_letter :: m) i)].
      apply/mapP; exists j.+1 => //.
      move: Hj; rewrite !mem_filter => /andP [Hd Hj2].
      rewrite /= Hd /=.
      rewrite inE mem_iota; apply/orP; right.
      move: Hj2; rewrite mem_iota /= !add0n add1n => Hj2.
      by rewrite ltnS Hj2.
    move: (Hall2 _ Hin).
    by rewrite /has_transition /cde_offset /=.
  clear Hall; case: b; [right|left]; apply/mapP; exists X => //; exact: IH.
- (* D_letter *)
  case: X => [// | b1 [// | b2 X]] /= [HszX] Hall.
  rewrite mem_cat; apply/orP.
  have Htrans : b1 != b2.
    move: Hall; rewrite /all_D_transitions /D_offsets /=.
    case/andP => Htrans0 _; move: Htrans0.
    by rewrite /has_transition /=.
  have HallT : all_D_transitions m X.
    rewrite /all_D_transitions /D_offsets.
    apply/allP => k /mapP [j Hj ->].
    move: Hall; rewrite /all_D_transitions /D_offsets /=.
    case/andP => _ /allP Hall2.
    have Hin : cde_offset (D_letter :: m) j.+1 \in
      [seq cde_offset (D_letter :: m) i
            | i <- iota 1 (size m)
            & is_D_letter (nth C_letter (D_letter :: m) i)].
      apply/mapP; exists j.+1 => //.
      move: Hj; rewrite !mem_filter => /andP [Hd Hj2].
      rewrite /= Hd /=.
      rewrite mem_iota; move: Hj2.
      rewrite mem_iota /= !add0n add1n => Hj2.
      by rewrite ltnS.
    move: (Hall2 _ Hin).
    by rewrite /has_transition /cde_offset /=.
  clear Hall; case: b1 Htrans => /=; case: b2 => //= _.
  + right; apply/mapP; exists X => //; exact: IH.
  + left; apply/mapP; exists X => //; exact: IH.
- (* E_letter *)
  move=> HszX Hall; apply: IH => //.
  move: Hall; rewrite /all_D_transitions /D_offsets /=.
  move=> Hall2.
  rewrite /all_D_transitions /D_offsets.
  apply/allP => k /mapP [j Hj ->].
  move/allP: Hall2 => Hall2.
  have Hin : cde_offset (E_letter :: m) j.+1 \in
    [seq cde_offset (E_letter :: m) i
    | i <- iota 1 (size m)
    & is_D_letter (nth C_letter (E_letter :: m) i)].
    apply/mapP; exists j.+1 => //.
    move: Hj; rewrite !mem_filter => /andP [Hd Hj2].
    rewrite /= Hd /=.
    rewrite mem_iota; move: Hj2.
    rewrite mem_iota /= !add0n add1n => Hj2.
    by rewrite ltnS.
  move: (Hall2 _ Hin).
  by rewrite /has_transition /cde_offset /=.
Qed.

(** Combined characterisation: when [X] has the right length, membership
    in [expand_cde m] is equivalent to having a transition at every
    [D]-offset.  Pivot lemma used by [phi_w_support_general]. *)
Lemma expand_cde_mem_iff m X :
  size X = cde_total_width m ->
  (X \in expand_cde m) = all_D_transitions m X.
Proof.
move=> Hsz; apply/idP/idP.
- exact: expand_cde_mem_transitions.
- exact: transitions_expand_cde_mem Hsz.
Qed.

(* -- has_transition = omega_seq membership -------------------------------- *)
(* k ∈ omega_seq(desc(X)) iff nth false X k ≠ nth false X (k+1),           *)
(* where desc(X) = {i < m : X[i] = true}.                                  *)

(** Membership in the descent set [filter (nth X) (iota 0 m)] reduces to
    the bit at that index. *)
Lemma mem_filter_iota_nth (X : seq bool) m i :
  i < m ->
  (i \in [seq j <- iota 0 m | nth false X j]) = nth false X i.
Proof.
move=> Hi.
rewrite mem_filter mem_iota add0n Hi andbT /=.
by case: (nth false X i).
Qed.

(** Every element of [s] is bounded above by [foldr maxn 0 s]. *)
Lemma foldr_maxn_ge (s : seq nat) x : x \in s -> x <= foldr maxn 0 s.
Proof.
elim: s => [//|a s IH].
rewrite inE => /orP [/eqP -> | Hin].
- by rewrite /= leq_maxl.
- by rewrite /=; apply: leq_trans (IH Hin) _; exact: leq_maxr.
Qed.

(** Bool form of [omega_seq] membership: the XOR criterion plus the
    bound [k <= max s]. *)
Lemma mem_omega_seq (s : seq nat) k :
  k \in omega_seq s =
  ((k \in s) != (k.+1 \in s)) && (k < (foldr maxn 0 s).+1).
Proof. by rewrite /omega_seq mem_filter mem_iota add0n. Qed.

(** Bridge: a bit transition in [X] at index [k < m.-1] is equivalent to
    [k \in omega_seq] of [X]'s descent set.  Pivot used in the support
    proof to translate D-offset transitions into [omega_seq] membership. *)
Lemma has_transition_omega_seq X m k :
  k < m.-1 ->
  has_transition X k =
  (k \in omega_seq [seq i <- iota 0 m | nth false X i]).
Proof.
move=> Hk.
have Hk2 : k.+1 < m.
  by rewrite -[m](@prednK m) ?ltnS //; case: m Hk.
have Hk1 : k < m by exact: ltnW.
set desc := [seq i <- iota 0 m | nth false X i].
rewrite /has_transition mem_omega_seq.
have -> : (k \in desc) = nth false X k.
  by rewrite /desc mem_filter_iota_nth.
have -> : (k.+1 \in desc) = nth false X k.+1.
  by rewrite /desc mem_filter_iota_nth.
suff Hbound : (nth false X k != nth false X k.+1) ->
  k < (foldr maxn 0 desc).+1.
  case: (nth false X k != nth false X k.+1) (Hbound) => //= Hb.
  by rewrite Hb.
move=> Hneq.
move: Hneq.
case Hxk : (nth false X k); case Hxk1 : (nth false X k.+1) => //= _.
- have Hkin : k \in desc
    by rewrite /desc mem_filter mem_iota add0n Hk1 Hxk.
  by apply: (leq_ltn_trans (foldr_maxn_ge Hkin)); exact: ltnSn.
- have Hkin : k.+1 \in desc
    by rewrite /desc mem_filter mem_iota add0n Hk2 Hxk1.
  apply: (leq_ltn_trans _ (ltnSn _)).
  by apply: (leq_trans (leqnSn k)); exact: foldr_maxn_ge.
Qed.

(** [cde_total_width] is additive over concatenation. *)
Lemma cde_total_width_cat s1 s2 :
  cde_total_width (s1 ++ s2) =
  cde_total_width s1 + cde_total_width s2.
Proof. by rewrite /cde_total_width map_cat sumn_cat. Qed.
