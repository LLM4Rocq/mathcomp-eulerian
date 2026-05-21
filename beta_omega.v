(* beta_omega.v — Toggle operator, Stanley ω-map, and Foata block
   endpoints.

   Extracted from beta_swap.v §A, §H, §I to allow beta_bridge.v to import
   these without creating a dependency cycle with beta_swap.v.

   Contents:
     §A  sym_diff, toggle_at and basic lemmas
     §H  omega_set (Stanley §1.6 ω-map), toggle-at ω-superset lemmas
     §I  Foata block endpoints (block_left, block_right, chain-of-values)

   No axioms. Does not import beta_swap.v. *)

From mathcomp Require Import all_ssreflect fingroup perm.
From mathcomp_eulerian Require Import
  ordinal_reindex perm_compress descent eulerian beta.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* ========================================================================= *)
(* §A. Symmetric difference and single-position toggle                       *)
(* ========================================================================= *)

(** [sym_diff D E] -- symmetric difference [(D \ E) U (E \ D)] of two
    finsets over [{set 'I_n}]. *)
Definition sym_diff (n : nat) (D E : {set 'I_n}) : {set 'I_n} :=
  (D :\: E) :|: (E :\: D).

(** [toggle_at D i] -- single-position toggle: flips membership of [i]
    in the descent set [D] by symmetric difference with [[set i]]. *)
Definition toggle_at (n : nat) (D : {set 'I_n}) (i : 'I_n) : {set 'I_n} :=
  sym_diff D [set i].

(** [toggle_at_in] -- membership in [toggle_at D i] is xor of
    [(i == j)] and [(j \in D)]. *)
Lemma toggle_at_in n (D : {set 'I_n}) (i j : 'I_n) :
  (j \in toggle_at D i) = (i == j) (+) (j \in D).
Proof.
rewrite /toggle_at /sym_diff !inE eq_sym.
by case: eqP => _ /=; case: (j \in D).
Qed.

(** [toggle_atK] -- toggling at the same position twice is the
    identity. *)
Lemma toggle_atK n (D : {set 'I_n}) (i : 'I_n) :
  toggle_at (toggle_at D i) i = D.
Proof.
apply/setP => j; rewrite !toggle_at_in.
by case: eqP => _ /=; case: (j \in D).
Qed.

(** [toggle_at_self] -- at the toggled position, membership is
    flipped: [i \in toggle_at D i] iff [i \notin D]. *)
Lemma toggle_at_self n (D : {set 'I_n}) (i : 'I_n) :
  (i \in toggle_at D i) = ~~ (i \in D).
Proof. by rewrite toggle_at_in eqxx. Qed.

(** [toggle_at_other] -- away from the toggled position [i],
    membership in [D] is preserved. *)
Lemma toggle_at_other n (D : {set 'I_n}) (i j : 'I_n) :
  i != j -> (j \in toggle_at D i) = (j \in D).
Proof. by move=> H; rewrite toggle_at_in (negbTE H). Qed.

(* ========================================================================= *)
(* §H. Stanley ω-map and toggle-at ω-superset lemmas. *)
(* ========================================================================= *)

(** [omega_set D] -- Stanley's omega-map (Stanley EC1 §1.6) at the
    finset level: [k \in omega_set D] iff exactly one of [k] and [k+1]
    belongs to [D] (xor on consecutive positions). *)
Definition omega_set (n : nat) (D : {set 'I_n.+1}) : {set 'I_n} :=
  [set k : 'I_n | (widen_ord (leqnSn n) k \in D) != (lift ord0 k \in D)].

(** [mem_omega_set] -- unfolds membership of [k] in [omega_set D] to
    the underlying xor of consecutive [D]-memberships. *)
Lemma mem_omega_set n (D : {set 'I_n.+1}) (k : 'I_n) :
  (k \in omega_set D) =
  ((widen_ord (leqnSn n) k \in D) != (lift ord0 k \in D)).
Proof. by rewrite inE. Qed.

(** [toggle_at_omega_bit_i_new] -- when consecutive [i,j] are both in
    [D], toggling [i] turns the omega-bit at the connecting position
    [k] from off to on; produces the witness ordinal [k]. *)
Lemma toggle_at_omega_bit_i_new n (D : {set 'I_n.+1}) (i j : 'I_n.+1) :
  val j = (val i).+1 -> i \in D -> j \in D ->
  exists k : 'I_n,
    [/\ widen_ord (leqnSn n) k = i,
        lift ord0 k = j,
        k \notin omega_set D &
        k \in omega_set (toggle_at D i)].
Proof.
move=> Hj Hi Hj'.
have Hik : val i < n.
  by have := ltn_ord j; rewrite Hj -ltnS.
pose k := Ordinal Hik.
have Ewid : widen_ord (leqnSn n) k = i by apply/val_inj.
have Elif : lift ord0 k = j by apply/val_inj; rewrite /= /bump /= add1n -Hj.
have Hij : i != j by rewrite -val_eqE Hj /=; elim: (val i).
exists k; split => //.
  by rewrite mem_omega_set Ewid Elif Hi Hj'.
by rewrite mem_omega_set Ewid Elif toggle_at_self Hi /= toggle_at_other // Hj'.
Qed.

(** [toggle_at_omega_strict_superset] -- key omega-monotonicity step
    (left toggle): if [i,j] both in [D] with [j = i+1] and the
    predecessor of [i] also lies in [D] when defined, then toggling
    out [i] strictly enlarges [omega_set]. Feeds into [beta_swap] case
    analysis. *)
Lemma toggle_at_omega_strict_superset n
  (D : {set 'I_n.+1}) (i j : 'I_n.+1) :
  val j = (val i).+1 -> i \in D -> j \in D ->
  (forall p : 'I_n.+1, val p = (val i).-1 -> val i != 0 -> p \in D) ->
  omega_set D \proper omega_set (toggle_at D i).
Proof.
move=> Hj Hi Hj' Hpred.
have [k [Ewid Elif Hknot Hkin]] := toggle_at_omega_bit_i_new Hj Hi Hj'.
apply/properP; split; last by exists k.
apply/subsetP => x Hx.
have Hij : i != j by rewrite -val_eqE Hj /=; elim: (val i).
rewrite mem_omega_set in Hx *.
have Hxk : x != k.
  by apply/eqP => E; move: Hknot; rewrite -E mem_omega_set Hx.
case E0 : (val i == 0).
  have Hxwid : widen_ord (leqnSn n) x != i.
    apply/eqP => Exi; move/eqP: Hxk; apply; apply/val_inj.
    by move: (congr1 val Exi) (congr1 val Ewid); rewrite /= => <- <-.
  have Hxlif : lift ord0 x != i.
    by rewrite -val_eqE /= /bump /= add1n (eqP E0).
  by rewrite mem_omega_set !toggle_at_other //; rewrite eq_sym.
move/negbT: E0 => Hi0.
have Hxwid : widen_ord (leqnSn n) x != i.
  apply/eqP => Exi; move/eqP: Hxk; apply; apply/val_inj.
  by move: (congr1 val Exi) (congr1 val Ewid); rewrite /= => <- <-.
case Elxi : (lift ord0 x == i); last first.
  move/negbT: Elxi => Hxlif.
  by rewrite mem_omega_set !toggle_at_other //; rewrite eq_sym.
move/eqP: Elxi => Elxi.
have Hvx : val x = (val i).-1.
  have H := congr1 val Elxi.
  move: H; rewrite /= /bump /= add1n => H.
  by rewrite -H /=.
pose p := widen_ord (leqnSn n) x.
have Hvp : val p = (val i).-1 by rewrite /=.
have Hpd : p \in D by apply: Hpred.
rewrite mem_omega_set toggle_at_other; last by rewrite eq_sym.
rewrite Elxi toggle_at_self Hi /=.
by rewrite -/p Hpd.
Qed.

(** [toggle_at_j_omega_bit_i_new] -- right-toggle analogue of
    [toggle_at_omega_bit_i_new]: toggling [j] in the consecutive pair
    [i,j] turns the omega-bit at [k] from off to on. *)
Lemma toggle_at_j_omega_bit_i_new n (D : {set 'I_n.+1}) (i j : 'I_n.+1) :
  val j = (val i).+1 -> i \in D -> j \in D ->
  exists k : 'I_n,
    [/\ widen_ord (leqnSn n) k = i,
        lift ord0 k = j,
        k \notin omega_set D &
        k \in omega_set (toggle_at D j)].
Proof.
move=> Hj Hi Hj'.
have Hik : val i < n.
  by have := ltn_ord j; rewrite Hj -ltnS.
pose k := Ordinal Hik.
have Ewid : widen_ord (leqnSn n) k = i by apply/val_inj.
have Elif : lift ord0 k = j by apply/val_inj; rewrite /= /bump /= add1n -Hj.
have Hij : i != j by rewrite -val_eqE Hj /=; elim: (val i).
exists k; split => //.
  by rewrite mem_omega_set Ewid Elif Hi Hj'.
rewrite mem_omega_set Ewid Elif.
have Hji : j != i by rewrite eq_sym.
by rewrite (toggle_at_other _ Hji) Hi toggle_at_self Hj'.
Qed.

(** [toggle_at_j_omega_strict_superset] -- right-toggle omega
    monotonicity (case A of beta-swap): if [i,j] both in [D] with
    [j = i+1] and the successor of [j] is also in [D] (when defined),
    then toggling [j] strictly enlarges [omega_set]. *)
Lemma toggle_at_j_omega_strict_superset n
  (D : {set 'I_n.+1}) (i j : 'I_n.+1) :
  val j = (val i).+1 -> i \in D -> j \in D ->
  (forall q : 'I_n.+1, val q = (val j).+1 -> q \in D) ->
  omega_set D \proper omega_set (toggle_at D j).
Proof.
move=> Hj Hi Hj' Hsucc.
have [k [Ewid Elif Hknot Hkin]] := toggle_at_j_omega_bit_i_new Hj Hi Hj'.
apply/properP; split; last by exists k.
apply/subsetP => x Hx.
have Hxk : x != k.
  by apply/eqP => E; subst x; move: Hknot; rewrite Hx.
have Hij : i != j by rewrite -val_eqE Hj /=; elim: (val i).
rewrite mem_omega_set in Hx *.
case Elxj : (lift ord0 x == j).
- exfalso; move/eqP: Hxk; apply; apply/val_inj.
  have Hxval : val x = val i.
    have := congr1 val (eqP Elxj); rewrite /= /bump /= add1n Hj => [[]] //.
  rewrite Hxval; have := congr1 val Ewid; rewrite /= => <- //.
- case Ewxj : (widen_ord (leqnSn n) x == j).
  + rewrite mem_omega_set (eqP Ewxj) toggle_at_self Hj' /=.
    have Hlxnj : j != lift ord0 x by rewrite eq_sym; exact: negbT Elxj.
    rewrite toggle_at_other //.
    have Hvlx : val (lift ord0 x) = (val j).+1.
      have := congr1 val (eqP Ewxj); rewrite /= => Hvx.
      by rewrite /= /bump /= add1n Hvx.
    by rewrite (Hsucc _ Hvlx).
  + rewrite mem_omega_set.
    have Hwxnj : j != widen_ord (leqnSn n) x.
      by rewrite eq_sym; exact: negbT Ewxj.
    have Hlxnj : j != lift ord0 x by rewrite eq_sym; exact: negbT Elxj.
    by rewrite !toggle_at_other.
Qed.

(* ========================================================================= *)
(* §I. Foata block endpoints (Phase 1 of Track C). *)
(* ========================================================================= *)

Section FoataBlocks.
Variable n : nat.
Implicit Types (s : {perm 'I_n.+1}) (i : 'I_n).

(** [left_ok s i l] -- candidate left endpoint test: [l <= i] and every
    position between [l] and [i] is a descent of [s]. *)
Definition left_ok s i (l : 'I_n) : bool :=
  (val l <= val i)
  && [forall k : 'I_n, (val l <= val k <= val i) ==> is_descent s k].

(** [right_ok s i r] -- candidate right endpoint test: [i <= r] and
    every position between [i] and [r] is a descent of [s]. *)
Definition right_ok s i (r : 'I_n) : bool :=
  (val i <= val r)
  && [forall k : 'I_n, (val i <= val k <= val r) ==> is_descent s k].

(** [left_ok_self] -- a descent position [i] is its own valid left
    endpoint candidate. *)
Lemma left_ok_self s i : is_descent s i -> left_ok s i i.
Proof.
move=> Hi; rewrite /left_ok leqnn /=.
apply/forallP => k; apply/implyP; case/andP => H1 H2.
by have -> : k = i by apply/val_inj; apply/eqP; rewrite eqn_leq H2 H1.
Qed.

(** [right_ok_self] -- a descent position [i] is its own valid right
    endpoint candidate. *)
Lemma right_ok_self s i : is_descent s i -> right_ok s i i.
Proof.
move=> Hi; rewrite /right_ok leqnn /=.
apply/forallP => k; apply/implyP; case/andP => H1 H2.
by have -> : k = i by apply/val_inj; apply/eqP; rewrite eqn_leq H2 H1.
Qed.

(** [block_left s i] -- left endpoint of the maximal Foata descent
    block containing [i]: if [i] is a descent, the smallest [l <= i]
    such that all positions in [[l..i]] are descents; otherwise [i]. *)
Definition block_left s i : 'I_n :=
  if is_descent s i then [arg min_(l < i | left_ok s i l) val l]
  else i.

(** [block_right s i] -- right endpoint of the maximal Foata descent
    block containing [i]: if [i] is a descent, the largest [r >= i]
    such that all positions in [[i..r]] are descents; otherwise [i]. *)
Definition block_right s i : 'I_n :=
  if is_descent s i then [arg max_(r > i | right_ok s i r) val r]
  else i.

(** [block_left_left_ok] -- the chosen [block_left s i] satisfies the
    [left_ok] predicate (when [i] is a descent). *)
Lemma block_left_left_ok s i : is_descent s i -> left_ok s i (block_left s i).
Proof.
move=> Hi; rewrite /block_left Hi.
by case: arg_minnP; first exact: left_ok_self.
Qed.

(** [block_right_right_ok] -- the chosen [block_right s i] satisfies
    the [right_ok] predicate (when [i] is a descent). *)
Lemma block_right_right_ok s i :
  is_descent s i -> right_ok s i (block_right s i).
Proof.
move=> Hi; rewrite /block_right Hi.
by case: arg_maxnP; first exact: right_ok_self.
Qed.

(** [block_left_min] -- minimality of [block_left s i] among all
    valid left-endpoint candidates. *)
Lemma block_left_min s i (l : 'I_n) :
  is_descent s i -> left_ok s i l -> val (block_left s i) <= val l.
Proof.
move=> Hi Hl; rewrite /block_left Hi.
by case: arg_minnP; [exact: left_ok_self | move=> ? _; apply].
Qed.

(** [block_right_max] -- maximality of [block_right s i] among all
    valid right-endpoint candidates. *)
Lemma block_right_max s i (r : 'I_n) :
  is_descent s i -> right_ok s i r -> val r <= val (block_right s i).
Proof.
move=> Hi Hr; rewrite /block_right Hi.
by case: arg_maxnP; [exact: right_ok_self | move=> ? _; apply].
Qed.

(** [block_left_le] -- the left endpoint of the block does not exceed
    [i]. *)
Lemma block_left_le s i :
  is_descent s i -> val (block_left s i) <= val i.
Proof. by move=> /block_left_left_ok /andP[]. Qed.

(** [block_right_ge] -- the right endpoint of the block is at least
    [i]. *)
Lemma block_right_ge s i :
  is_descent s i -> val i <= val (block_right s i).
Proof. by move=> /block_right_right_ok /andP[]. Qed.

(** [block_left_descent] -- every position from [block_left s i] up
    to [i] is a descent of [s]. *)
Lemma block_left_descent s i (k : 'I_n) :
  is_descent s i ->
  val (block_left s i) <= val k <= val i -> is_descent s k.
Proof.
move=> Hi Hk.
have /andP [_ /forallP /(_ k) /implyP /(_ Hk) //] := block_left_left_ok Hi.
Qed.

(** [block_right_descent] -- every position from [i] up to
    [block_right s i] is a descent of [s]. *)
Lemma block_right_descent s i (k : 'I_n) :
  is_descent s i ->
  val i <= val k <= val (block_right s i) -> is_descent s k.
Proof.
move=> Hi Hk.
have /andP [_ /forallP /(_ k) /implyP /(_ Hk) //] := block_right_right_ok Hi.
Qed.

(** [block_descent_chain] -- every position in the full block
    [[block_left s i .. block_right s i]] is a descent of [s]. *)
Lemma block_descent_chain s i (k : 'I_n) :
  is_descent s i ->
  val (block_left s i) <= val k <= val (block_right s i) ->
  is_descent s k.
Proof.
move=> Hi Hk; case/andP: Hk => H1 H2.
case: (leqP (val k) (val i)) => Hki.
  have Hr : val (block_left s i) <= val k <= val i by rewrite H1 Hki.
  exact: block_left_descent Hi Hr.
have Hr : val i <= val k <= val (block_right s i) by rewrite (ltnW Hki) H2.
exact: block_right_descent Hi Hr.
Qed.

(** [block_left_le_right] -- block endpoints are ordered:
    [block_left s i <= block_right s i]. *)
(** [block_left_minimal] -- the block is left-maximal: the position
    immediately before [block_left s i] (when defined) is NOT a
    descent. *)
(** [block_right_maximal] -- the block is right-maximal: the position
    immediately after [block_right s i] is NOT a descent. *)
(** [block_chain_step] -- single-step value comparison: for any [k] in
    the block, [s] strictly decreases from position [k] to [k+1]. *)
Lemma block_chain_step s i (k : 'I_n) :
  is_descent s i ->
  val (block_left s i) <= val k <= val (block_right s i) ->
  s (widen_ord (leqnSn n) k) > s (lift ord0 k).
Proof. by move=> Hi Hk; have := block_descent_chain Hi Hk. Qed.

(** [block_chain_values] -- chain-of-values: the values [s p] are
    strictly decreasing across the entire Foata block (from
    [block_left s i] through to [block_right s i + 1]). *)
Lemma block_chain_values s i (p q : 'I_n.+1) :
  is_descent s i ->
  val (block_left s i) <= val p -> val q <= (val (block_right s i)).+1 ->
  val p < val q -> s p > s q.
Proof.
move=> Hi Hp Hq Hpq.
suff H : forall d (p' q' : 'I_n.+1),
    val q' = (val p' + d.+1)%N ->
    val (block_left s i) <= val p' ->
    val q' <= (val (block_right s i)).+1 ->
    s p' > s q'.
  pose d := (val q - val p).-1.
  have Hd : val q = (val p + d.+1)%N.
    have Hsub : val q - val p > 0 by rewrite subn_gt0.
    rewrite /d prednK // addnBA; last exact: ltnW.
    by rewrite addnC addnK.
  exact: (H d p q Hd Hp Hq).
move=> {p q Hp Hq Hpq}.
(* Induction on q using position-based step. *)
move=> d; elim: d => [|d IH] p q Hq Hp Hqr.
  (* d = 0: q = p+1, so positions are "consecutive" in 'I_n.+1 *)
  rewrite addn1 in Hq.
  (* Need a descent witness k : 'I_n with val k = val p. *)
  have Hp_lt : val p < n.
    have Hle : (val p).+1 <= (val (block_right s i)).+1 by rewrite -Hq.
    rewrite ltnS in Hle.
    exact: (leq_ltn_trans Hle (ltn_ord _)).
  pose k := Ordinal Hp_lt.
  have Hk_range : val (block_left s i) <= val k <= val (block_right s i).
    rewrite /= Hp /=.
    have Hle : (val p).+1 <= (val (block_right s i)).+1 by rewrite -Hq.
    by rewrite ltnS in Hle.
  have Hstep := block_chain_step Hi Hk_range.
  have Ep : p = widen_ord (leqnSn n) k by apply/val_inj.
  have Eq : q = lift ord0 k.
    by apply/val_inj; rewrite /= /bump /= add1n Hq.
  by rewrite Ep Eq.
(* d.+1 case: insert intermediate position p+1. *)
have Hp_le_br : val p <= val (block_right s i).
  have Hle : val p + d.+2 <= (val (block_right s i)).+1 by rewrite -Hq.
  rewrite -ltnS; apply: (leq_trans _ Hle).
  by rewrite addnS ltnS; apply: leq_addr.
have Hp_lt_n : val p < n by apply: (leq_ltn_trans Hp_le_br); apply: ltn_ord.
have Hp1_lt : (val p).+1 < n.+1 by rewrite ltnS.
pose p' := Ordinal Hp1_lt.
have Hp'_val : val p' = (val p).+1 by [].
(* step1: s p > s p' via block_chain_step (single descent). *)
pose k := Ordinal Hp_lt_n.
have Hk_range : val (block_left s i) <= val k <= val (block_right s i)
  by rewrite /= Hp /= Hp_le_br.
have Hstep := block_chain_step Hi Hk_range.
have Ep : p = widen_ord (leqnSn n) k by apply/val_inj.
have Ep' : p' = lift ord0 k by apply/val_inj; rewrite /= /bump /= add1n.
have step1 : s p > s p' by rewrite Ep Ep'.
have step2 : s p' > s q.
  apply: (IH p' q) => //.
    by rewrite Hp'_val Hq addnS.
  by apply: (leq_trans Hp); rewrite Hp'_val.
exact: (ltn_trans step2 step1).
Qed.

End FoataBlocks.

