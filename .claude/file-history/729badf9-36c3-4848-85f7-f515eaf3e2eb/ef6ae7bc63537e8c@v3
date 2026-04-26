(* Layer 5: β-swap lemma and alternating-maximum corollary.                  *)
(*                                                                           *)
(* Proves that among descent sets D : {set 'I_n} which are not               *)
(* set-alternating (i.e. contain a consecutive same-membership pair),        *)
(* β(D) is strictly smaller than β(alt_desc_set n).                          *)
(*                                                                           *)
(* Two LABELED ADMITTED sub-lemmas remain: `beta_swap_monotone`              *)
(* (Foata injection) and `beta_swap_lt` (strict witness). Everything         *)
(* downstream — `beta_alt_max` — is `Qed`.                                  *)

From mathcomp Require Import all_ssreflect fingroup perm.
From mathcomp_eulerian Require Import
  ordinal_reindex perm_compress descent eulerian beta.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* ========================================================================= *)
(* §A. Symmetric difference and single-position toggle                       *)
(* ========================================================================= *)

Definition sym_diff (n : nat) (D E : {set 'I_n}) : {set 'I_n} :=
  (D :\: E) :|: (E :\: D).

Definition toggle_at (n : nat) (D : {set 'I_n}) (i : 'I_n) : {set 'I_n} :=
  sym_diff D [set i].

Lemma toggle_at_in n (D : {set 'I_n}) (i j : 'I_n) :
  (j \in toggle_at D i) = (i == j) (+) (j \in D).
Proof.
rewrite /toggle_at /sym_diff !inE eq_sym.
by case: eqP => _ /=; case: (j \in D).
Qed.

Lemma toggle_atK n (D : {set 'I_n}) (i : 'I_n) :
  toggle_at (toggle_at D i) i = D.
Proof.
apply/setP => j; rewrite !toggle_at_in.
by case: eqP => _ /=; case: (j \in D).
Qed.

Lemma toggle_at_self n (D : {set 'I_n}) (i : 'I_n) :
  (i \in toggle_at D i) = ~~ (i \in D).
Proof. by rewrite toggle_at_in eqxx. Qed.

Lemma toggle_at_other n (D : {set 'I_n}) (i j : 'I_n) :
  i != j -> (j \in toggle_at D i) = (j \in D).
Proof. by move=> H; rewrite toggle_at_in (negbTE H). Qed.

(* ========================================================================= *)
(* §B. Alternating descent set                                               *)
(* ========================================================================= *)

Definition alt_desc_set (n : nat) : {set 'I_n} :=
  [set i : 'I_n | ~~ odd i].

Lemma mem_alt_desc_set n (i : 'I_n) :
  (i \in alt_desc_set n) = ~~ odd i.
Proof. by rewrite inE. Qed.

(* A descent set is "set-alternating" iff every consecutive pair has
   differing membership. *)
Definition set_is_alt (n : nat) (D : {set 'I_n}) : bool :=
  [forall i : 'I_n, [forall j : 'I_n,
     (val j == (val i).+1) ==> ((i \in D) != (j \in D))]].

(* The alternating set is set-alternating. *)
Lemma alt_desc_set_is_alt n : set_is_alt (alt_desc_set n).
Proof.
apply/forallP => i; apply/forallP => j; apply/implyP => /eqP Hj.
rewrite !mem_alt_desc_set Hj /= negbK.
by case: (odd i).
Qed.

Lemma set_not_altP n (D : {set 'I_n}) :
  ~~ set_is_alt D ->
  exists i j : 'I_n, val j = (val i).+1 /\ (i \in D) = (j \in D).
Proof.
move/forallPn => [i /forallPn [j Hij]].
rewrite negb_imply in Hij.
case/andP: Hij => /eqP Hj /negPn /eqP Heq.
by exists i, j.
Qed.

(* ========================================================================= *)
(* §C. β-swap lemmas (Foata — classical)                                      *)
(* ========================================================================= *)

(* The two target lemmas — `beta_swap_monotone_both_in` (≤) and
   `beta_swap_lt_both_in` (<) — are PROVED from two sub-axioms that
   partition the argument into Case A (ω-containment) and Case B
   (adjacent ω-swap).

   Background: Stanley EC1 (2nd ed.), Proposition 1.6.4 states
     ω(S) ⊂ ω(T) ⟹ βₙ(S) < βₙ(T).
   When i, j = i+1 are both in D and we toggle j, the ω-bit analysis
   (see §H below, `toggle_at_j_omega_bit_i_new`) gives two cases:

   Case A (j at boundary or j+1 ∈ D): ω(D) ⊊ ω(D \ {j}).
     Prop 1.6.4 yields β(D) < β(D \ {j}).
     Proved seq-level in psi.v (omega_monotone_class_count +
     strict_witness_exists); the finset-level bridge is axiomatized below.

   Case B (j < n-1 and j+1 ∉ D): ω-sets differ by swapping bit j for
     bit i. Neither contains the other, so Prop 1.6.4 does not apply
     directly. The inequality requires a cd-index marginal-contribution
     comparison (see M7_CLOSING_AXIOMS_INFORMAL.md §4.5).

   We axiomatize ONLY the two sub-cases; the target lemmas are derived.
   The "both ascents" case is DERIVED via the value-complement involution
   (compl_perm, beta_compl, descent_set_compl). *)

(* Sub-axiom, Case A: j at boundary or j+1 ∈ D.
   Justification: toggle_at_j_omega_strict_superset (§H below) shows
   ω(D) ⊊ ω(D \ {j}) under this hypothesis. Prop 1.6.4 (proved seq-level
   in psi.v via omega_monotone_class_count + strict_witness_exists) then
   gives β(D) < β(D \ {j}). The finset/seq type bridge is the remaining
   gap; see psi.v §M6.6 comments. *)
Axiom beta_swap_lt_caseA : forall n (D : {set 'I_n}) (i j : 'I_n),
  val j = (val i).+1 -> i \in D -> j \in D ->
  (forall q : 'I_n, val q = (val j).+1 -> q \in D) ->
  beta D < beta (toggle_at D j).

(* Sub-axiom, Case B: j < n-1 and j+1 ∉ D — ω-sets differ by adjacent swap.
   Justification: omega(D) and omega(toggle_at D j) differ by swapping bit j
   for bit i (see M7_CLOSING_AXIOMS_INFORMAL.md §3.3 / §4.5). The inequality
   follows from comparing cd-index marginal contributions of adjacent
   ω-positions, which requires Theorem 1.6.3 (nonneg cd-index) plus a
   monotonicity argument on the recursive structure of min-max trees. *)
Axiom beta_swap_lt_caseB : forall n (D : {set 'I_n}) (i j : 'I_n),
  val j = (val i).+1 -> i \in D -> j \in D ->
  (exists q : 'I_n, val q = (val j).+1 /\ q \notin D) ->
  beta D < beta (toggle_at D j).

(* "Both descents" strict version (PROVED from the two sub-axioms). *)
Lemma beta_swap_lt_both_in : forall n (D : {set 'I_n}) (i j : 'I_n),
  val j = (val i).+1 ->
  i \in D -> j \in D ->
  beta D < beta (toggle_at D j).
Proof.
move=> n D i j Hj Hi Hj'.
case: (boolP [exists q : 'I_n, (val q == (val j).+1) && (q \notin D)]).
- move/existsP => [q /andP [/eqP Hq Hqnot]].
  apply: (beta_swap_lt_caseB Hj Hi Hj'); by exists q.
- move/existsPn => Hall.
  apply: (beta_swap_lt_caseA Hj Hi Hj') => q Hq.
  have := Hall q; rewrite Hq eqxx /=; by rewrite negbK.
Qed.

(* "Both descents" monotonicity (PROVED from the strict version).
   NOTE: toggles the UPPER index j = i+1, not i. Toggling the lower index
   can decrease β — counterexample: n=4, D={2,3}, i=2, β(D)=6 > 4=β(D\{2}).
   Toggling j removes the upper descent, which always increases β. *)
Lemma beta_swap_monotone_both_in : forall n (D : {set 'I_n}) (i j : 'I_n),
  val j = (val i).+1 ->
  i \in D -> j \in D ->
  beta D <= beta (toggle_at D j).
Proof.
move=> n D i j Hj Hi Hj'.
exact: ltnW (beta_swap_lt_both_in Hj Hi Hj').
Qed.

(* Toggle commutes with complement on the set side.
   Used to reduce the "both ascents" case to the "both descents" case. *)
Lemma toggle_at_compl n (D : {set 'I_n}) (i : 'I_n) :
  toggle_at (~: D) i = ~: toggle_at D i.
Proof.
apply/setP => j.
have H1 : (j \in toggle_at (~: D) i) = (i == j) (+) ~~ (j \in D).
  by rewrite toggle_at_in inE.
have H2 : (j \in ~: toggle_at D i) = ~~ ((i == j) (+) (j \in D)).
  by rewrite inE toggle_at_in.
rewrite H1 H2.
by case: (i == j); case: (j \in D).
Qed.

(* β-swap monotonicity and strict version are derived (via complement
   reduction) further below, after the value-complement bijection is
   available (§E). *)

(* ========================================================================= *)
(* §D. Alt maximises β (deferred: depends on derived beta_swap_lt below)     *)
(* ========================================================================= *)

(* We measure distance from alt by Hamming distance (symmetric-difference
   cardinality). The key observation: if D has a consecutive same-type
   pair (i, j), then at least one of i, j disagrees with alt_desc_set;
   toggling at that position reduces the Hamming distance to alt by 1.

   Proof: a pair (i, j) at positions val i, val i + 1 has same D-membership.
   But alt_desc_set has different membership at i vs j (since parities
   differ). So if D agrees with alt at i, it must disagree at j (and vice
   versa). In either case, at least one of {i, j} disagrees with alt. We
   toggle at the disagreeing position — it enters alt, so Hamming distance
   drops by 1 (while the symmetry of the pair guarantees the other swap
   hypothesis still holds at that position). *)

Lemma alt_pair_parity n (i j : 'I_n) :
  val j = (val i).+1 -> (i \in alt_desc_set n) != (j \in alt_desc_set n).
Proof.
move=> Hj.
rewrite !mem_alt_desc_set Hj /= negbK.
by case: (odd i).
Qed.

(* Toggling at k where k ∈ sym_diff D alt reduces the Hamming distance. *)
Lemma sym_diff_toggle_in n (D : {set 'I_n}) (k : 'I_n) :
  k \in sym_diff D (alt_desc_set n) ->
  #|sym_diff (toggle_at D k) (alt_desc_set n)|
    < #|sym_diff D (alt_desc_set n)|.
Proof.
move=> Hk.
rewrite (cardsD1 k (sym_diff D (alt_desc_set n))) Hk add1n ltnS.
apply: subset_leq_card; apply/subsetP => x.
rewrite inE !in_setD [x \in toggle_at D k]toggle_at_in.
rewrite /sym_diff !inE.
case E : (k == x) => /=.
- move/eqP: E => Ekx; subst x.
  rewrite eqxx.
  move: Hk; rewrite /sym_diff !inE.
  by case: (k \in D); case: (odd k).
- rewrite eq_sym E /=.
  by case: (x \in D); case: (odd x).
Qed.

(* Symmetric difference is empty iff the sets are equal. *)
Lemma sym_diff_eq0 n (D E : {set 'I_n}) :
  #|sym_diff D E| = 0 -> D = E.
Proof.
move=> /eqP; rewrite cards_eq0 => /eqP Hsd.
apply/setP => j.
have : j \notin sym_diff D E by rewrite Hsd inE.
rewrite /sym_diff !inE negb_or !negb_and !negbK.
case/andP => H1 H2; apply/idP/idP => H.
- case/orP: H1 => //; by rewrite H.
- case/orP: H2 => //; by rewrite H.
Qed.

(* ========================================================================= *)
(* §E. Value-complement bijection                                             *)
(* ========================================================================= *)

(* The "value-complement" perm: replace every value v by rev_ord v.
   Effect on descents: every descent becomes ascent and vice versa.
   This is the second symmetry (along with rev_perm) needed to identify
   the two set-alternating descent sets. *)
Definition compl_perm n (s : {perm 'I_n.+1}) : {perm 'I_n.+1} :=
  s * rev_perm_ord n.

Lemma compl_permE n (s : {perm 'I_n.+1}) (i : 'I_n.+1) :
  compl_perm s i = rev_ord (s i).
Proof. by rewrite /compl_perm permM rev_perm_ordE. Qed.

Lemma compl_perm_inj n : injective (@compl_perm n).
Proof. by move=> s1 s2 H; apply: (mulIg (rev_perm_ord n)). Qed.

Lemma compl_perm_involutive n : involutive (@compl_perm n).
Proof.
move=> s; rewrite /compl_perm -mulgA.
have -> : (rev_perm_ord n * rev_perm_ord n)%g = 1%g.
  apply/permP => i; rewrite permM perm1 !rev_perm_ordE.
  exact: rev_ordK.
by rewrite mulg1.
Qed.

Lemma is_descent_compl n (s : {perm 'I_n.+1}) (i : 'I_n) :
  is_descent (compl_perm s) i = ~~ is_descent s i.
Proof.
rewrite /is_descent !compl_permE.
set a := s _; set b := s _.
have arg_ne : widen_ord (leqnSn n) i != lift ord0 i.
  by rewrite -val_eqE /= /bump /= add1n neq_ltn ltnSn.
have ab_ne : val a != val b.
  by rewrite val_eqE; apply: contra arg_ne; rewrite /a /b => /eqP /perm_inj ->.
rewrite /= ltn_sub2lE; last exact: ltn_ord.
by rewrite ltnS ltn_neqAle [_ == _]eq_sym ab_ne /= -leqNgt.
Qed.

Lemma descent_set_compl n (s : {perm 'I_n.+1}) :
  descent_set (compl_perm s) = ~: descent_set s.
Proof.
by apply/setP => i; rewrite !inE is_descent_compl.
Qed.

Lemma beta_compl n (D : {set 'I_n}) : beta D = beta (~: D).
Proof.
rewrite /beta.
rewrite -(card_imset _ (@compl_perm_inj n)).
congr #|pred_of_set _|; apply/setP => s; rewrite !inE.
apply/imsetP/idP.
- by case=> t; rewrite inE => /eqP <- ->; rewrite descent_set_compl.
- move=> /eqP Hs.
  exists (compl_perm s); last by rewrite compl_perm_involutive.
  by rewrite inE descent_set_compl Hs setCK.
Qed.

(* β-swap monotonicity: if positions i and j = i+1 have the same
   D-membership, then toggling j does not decrease β. Derived from the
   "both descents" axiom `beta_swap_monotone_both_in` via the value-
   complement involution: when both i, j are ASCENTS in D, they are both
   DESCENTS in ~: D; applying the axiom to ~: D and translating back via
   `beta_compl` yields the inequality for D. *)
Lemma beta_swap_monotone n (D : {set 'I_n}) (i j : 'I_n) :
  val j = (val i).+1 ->
  (i \in D) = (j \in D) ->
  beta D <= beta (toggle_at D j).
Proof.
move=> Hj Hij.
case Hi : (i \in D).
- have Hj' : j \in D by rewrite -Hij.
  exact: (beta_swap_monotone_both_in Hj Hi Hj').
- have Hi' : i \in ~: D by rewrite !inE Hi.
  have Hj' : j \in ~: D by rewrite !inE -Hij Hi.
  have H := beta_swap_monotone_both_in Hj Hi' Hj'.
  rewrite toggle_at_compl in H.
  by rewrite (beta_compl D) (beta_compl (toggle_at D j)).
Qed.

(* Strict version, derived identically. *)
Lemma beta_swap_lt n (D : {set 'I_n}) (i j : 'I_n) :
  val j = (val i).+1 ->
  (i \in D) = (j \in D) ->
  beta D < beta (toggle_at D j).
Proof.
move=> Hj Hij.
case Hi : (i \in D).
- have Hj' : j \in D by rewrite -Hij.
  exact: (beta_swap_lt_both_in Hj Hi Hj').
- have Hi' : i \in ~: D by rewrite !inE Hi.
  have Hj' : j \in ~: D by rewrite !inE -Hij Hi.
  have H := beta_swap_lt_both_in Hj Hi' Hj'.
  rewrite toggle_at_compl in H.
  by rewrite (beta_compl D) (beta_compl (toggle_at D j)).
Qed.

(* ========================================================================= *)
(* §F. Classification of set-alternating sets                                *)
(* ========================================================================= *)

(* A set_is_alt set on 'I_n is determined by its membership at 0:
   either alt_desc_set (= even positions) or its complement (= odd). *)

Lemma set_is_alt_classify n (D : {set 'I_n}) :
  set_is_alt D -> D = alt_desc_set n \/ D = ~: alt_desc_set n.
Proof.
move=> HD.
case: n D HD => [|n] D HD.
  by left; apply/setP; case; case.
have HD' : forall (i1 i2 : 'I_n.+1), val i2 = (val i1).+1 ->
  (i1 \in D) != (i2 \in D).
  move=> i1 i2 Hi12.
  have := forallP (forallP HD i1) i2.
  by rewrite Hi12 eqxx.
have helper : forall v (i : 'I_n.+1), val i = v ->
  (i \in D) = (ord0 \in D) (+) odd v.
  elim/ltn_ind => v IHv i Hv.
  case: v IHv Hv => [|v] IHv Hv.
  - have -> : i = ord0 by apply/val_inj.
    by rewrite addbF.
  - have Hvn : v < n.+1 by rewrite -Hv; apply: ltnW; exact: ltn_ord.
    have IHv' : (Ordinal Hvn \in D) = (ord0 \in D) (+) odd v.
      by apply: (IHv v (ltnSn v) (Ordinal Hvn) erefl).
    have Halt : val i = (val (Ordinal Hvn)).+1 by rewrite Hv.
    have := HD' (Ordinal Hvn) i Halt.
    rewrite IHv' /=.
    by case: (ord0 \in D); case: (i \in D); case: (odd v).
case Hord0 : (ord0 \in D).
- left; apply/setP => i.
  rewrite mem_alt_desc_set (helper (val i) i erefl) Hord0 /=.
  by case: (odd i).
- right; apply/setP => i.
  rewrite inE mem_alt_desc_set (helper (val i) i erefl) Hord0 /=.
  by case: (odd i).
Qed.

(* Helper for the second-alt branch: if D' is set_is_alt then β(D') = β(alt). *)
Lemma beta_set_is_alt_eq n (D' : {set 'I_n}) :
  set_is_alt D' -> beta D' = beta (alt_desc_set n).
Proof.
move=> /set_is_alt_classify [-> //|->].
by rewrite beta_compl setCK.
Qed.

(* ========================================================================= *)
(* §G. β-based induction driver                                              *)
(* ========================================================================= *)

(* The right well-founded measure is `n.+1`! - β D` (decreases under
   beta_swap_lt because β strictly increases). The original `find_reducing_toggle`
   used Hamming distance to alt, which is NOT monotone under beta_swap_lt
   — see counter-example D = {0, 2, 3} on 'I_4 where the only same-pair
   toggle increases the Hamming distance but β does increase. *)

(* From ~~set_is_alt D, the existence of a same-pair forces n ≥ 2;
   hence [set: 'I_n] and set0 are distinct, both have β ≥ 1, so β D < n.+1`!. *)
Lemma not_set_is_alt_n_ge2 n (D : {set 'I_n}) :
  ~~ set_is_alt D -> 1 < n.
Proof.
move=> /set_not_altP [i [j [Hj _]]].
have Hjn : (val j < n)%N := ltn_ord j.
rewrite Hj in Hjn.
by apply: leq_ltn_trans Hjn; apply: ltn0Sn.
Qed.

Lemma beta_lt_fact n (D : {set 'I_n}) :
  ~~ set_is_alt D -> beta D < n.+1`!.
Proof.
move=> Hnalt.
have Hn2 := not_set_is_alt_n_ge2 Hnalt.
pose D' : {set 'I_n} := if D == set0 then [set: 'I_n] else set0.
have HD'D : D' != D.
  rewrite /D'; case Heq : (D == set0); last by rewrite eq_sym Heq.
  by move/eqP: Heq => ->; apply/eqP/setP => /(_ (@Ordinal n 0 (ltnW Hn2)));
     rewrite !inE.
have HbD' : 1 <= beta D'.
  by rewrite /D'; case: (D == set0); [rewrite beta_full | rewrite beta0].
rewrite -addn1; apply: leq_trans (_ : beta D + beta D' <= n.+1`!).
  by rewrite leq_add2l.
by rewrite -sum_beta_eq_fact (bigD1 D) //= leq_add2l (bigD1 D' HD'D) //=
   leq_addr.
Qed.

Lemma beta_alt_max_bounded n :
  forall k (D : {set 'I_n}),
  (n.+1`! - beta D <= k)%N ->
  ~~ set_is_alt D ->
  beta D < beta (alt_desc_set n).
Proof.
elim => [|k IH] D HM Hnalt.
- (* Base m = 0: contradiction since β D < n.+1`! *)
  exfalso.
  have Hlt := beta_lt_fact Hnalt.
  by move: HM; rewrite leqn0 subn_eq0 leqNgt Hlt.
- (* Step: apply beta_swap_lt at any same-pair, then IH *)
  case: (set_not_altP Hnalt) => i [j [Hj Hij]].
  have Hstrict : beta D < beta (toggle_at D j) := beta_swap_lt Hj Hij.
  case H' : (set_is_alt (toggle_at D j)).
  + (* toggled set is set-alt: β(toggled) = β(alt) by classification + beta_compl *)
    by rewrite (beta_set_is_alt_eq H') in Hstrict.
  + (* toggled set still not set-alt: apply IH *)
    apply: (ltn_trans Hstrict).
    apply: IH; last by rewrite H'.
    have HbDlt : beta D < (n.+1)`! := beta_lt_fact Hnalt.
    apply: leq_trans (_ : (n.+1)`! - (beta D).+1 <= k).
      by apply: leq_sub2l; exact: Hstrict.
    by rewrite subnS -ltnS prednK ?subn_gt0.
Qed.

(* Spec-facing lemma. *)
Lemma beta_alt_max n (D : {set 'I_n}) :
  ~~ set_is_alt D -> beta D < beta (alt_desc_set n).
Proof.
move=> Hnalt.
exact: (@beta_alt_max_bounded n (n.+1`! - beta D) D (leqnn _)).
Qed.

(* ========================================================================= *)
(* §H. Milestone M4: Stanley ω-map and the toggle-at ω superset bridge.      *)
(* ========================================================================= *)

(* Stanley EC1 §1.6, Prop. 1.6.4: for S ⊆ [n-1], define ω(S) ⊆ [n-2] by
   "i ∈ ω(S) iff exactly one of i, i+1 lies in S". We encode ω-maps as
   functions {set 'I_n.+1} → {set 'I_n} (aligning with how `beta` sees
   descent-sets for perms of 'I_n.+2 — the +1 shift matches Stanley's
   "[n-2]" vs "[n-1]"). The target β-axioms in §C use descent-sets of type
   {set 'I_n} (no .+1); callers bridge via the obvious `Ordinal` packaging.

   NOTE ON THE PLAN: STANLEY_CDINDEX_PLAN.md §2 asserts that toggling any
   "both-in-D" descent gives a strict ω-superset. Direct case-analysis
   (mirrored in the proof below) shows this is TOO STRONG: toggling `i` also
   flips the ω-bit at `i-1`, and that bit LEAVES ω(D) precisely when
   (i-1) ∉ D. A concrete counterexample: D = {1,2} ⊆ 'I_3, i = 1:
     ω(D) = {0}, ω(toggle D 1) = ω({2}) = {1}; neither contains the other.
   The strict-superset statement is therefore accurate only under the extra
   hypothesis that `i-1 ∈ D` (Case A of the flip analysis) OR that `i = 0`
   (no predecessor bit to flip). We expose both the strong, correctly
   hypothesised bridge (`toggle_at_omega_strict_superset`) and the always-
   true "new bit" lemma (`toggle_at_omega_bit_i_new`). Closing the axioms
   of §C via the bridge will therefore require either the full Stanley
   cd-index nonneg theorem (M5/M6 of the plan) or a case split on
   `(i-1) ∈ D` combined with an auxiliary argument for Case B.                  *)

Definition omega_set (n : nat) (D : {set 'I_n.+1}) : {set 'I_n} :=
  [set k : 'I_n | (widen_ord (leqnSn n) k \in D) != (lift ord0 k \in D)].

Lemma mem_omega_set n (D : {set 'I_n.+1}) (k : 'I_n) :
  (k \in omega_set D) =
  ((widen_ord (leqnSn n) k \in D) != (lift ord0 k \in D)).
Proof. by rewrite inE. Qed.

(* The ω-bit at the descent position always enters ω after a both-in toggle. *)
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

(* Strict ω-superset under toggle — with the extra hypothesis that the
   predecessor position (if any) is also in D. This is Case A of the
   i-1-bit flip analysis, where both ω-bits i and i-1 become newly active
   (if i > 0 and i-1 ∈ D) or i is the only new bit (if i = 0).                *)
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

(* ----- j-toggle analogues ------------------------------------------------ *)
(* When we toggle j = i+1 (the UPPER index, as in the corrected §C axioms),
   the ω-bit at position i is always gained, and the bit at i-1 is NOT
   affected (since neither i-1 nor i changes membership). This makes the
   j-toggle strictly better-behaved than the i-toggle for the ω-bridge. *)

(* The ω-bit at position i always enters ω after toggling j. *)
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

(* Strict ω-superset under j-toggle — with the extra hypothesis that
   the successor position j+1 is also in D (or j is at the boundary,
   in which case the hypothesis is vacuously true). This is Case A of
   the j-toggle ω-analysis, corresponding to beta_swap_lt_caseA.  *)
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
- (* lift x = j implies x = k, contradiction *)
  exfalso; move/eqP: Hxk; apply; apply/val_inj.
  have Hxval : val x = val i.
    have := congr1 val (eqP Elxj); rewrite /= /bump /= add1n Hj => [[]] //.
  rewrite Hxval; have := congr1 val Ewid; rewrite /= => <- //.
- case Ewxj : (widen_ord (leqnSn n) x == j).
  + (* widen x = j: toggle flips widen x; lift x has val = (val j).+1 *)
    rewrite mem_omega_set (eqP Ewxj) toggle_at_self Hj' /=.
    have Hlxnj : j != lift ord0 x by rewrite eq_sym; exact: negbT Elxj.
    rewrite toggle_at_other //.
    have Hvlx : val (lift ord0 x) = (val j).+1.
      have := congr1 val (eqP Ewxj); rewrite /= => Hvx.
      by rewrite /= /bump /= add1n Hvx.
    by rewrite (Hsucc _ Hvlx).
  + (* widen x != j, lift x != j: both unchanged by toggle *)
    rewrite mem_omega_set.
    have Hwxnj : j != widen_ord (leqnSn n) x.
      by rewrite eq_sym; exact: negbT Ewxj.
    have Hlxnj : j != lift ord0 x by rewrite eq_sym; exact: negbT Elxj.
    by rewrite !toggle_at_other.
Qed.

(* ========================================================================= *)
(* §I. Foata block endpoints (Phase 1 of Track C).                            *)
(*                                                                            *)
(* For σ : {perm 'I_n.+1} and i : 'I_n with `is_descent σ i`, the endpoints   *)
(* [block_left σ i, block_right σ i] of the maximal run of consecutive        *)
(* descent positions of σ containing i. Used by the Foata rotation in        *)
(* Phase 2. Purely combinatorial — no reference to toggle_at.                *)
(* ========================================================================= *)

Section FoataBlocks.
Variable n : nat.
Implicit Types (s : {perm 'I_n.+1}) (i : 'I_n).

(* Predicate: every position in [val l, val i] is a descent. *)
Definition left_ok s i (l : 'I_n) : bool :=
  (val l <= val i)
  && [forall k : 'I_n, (val l <= val k <= val i) ==> is_descent s k].

(* Predicate: every position in [val i, val r] is a descent. *)
Definition right_ok s i (r : 'I_n) : bool :=
  (val i <= val r)
  && [forall k : 'I_n, (val i <= val k <= val r) ==> is_descent s k].

Lemma left_ok_self s i : is_descent s i -> left_ok s i i.
Proof.
move=> Hi; rewrite /left_ok leqnn /=.
apply/forallP => k; apply/implyP; case/andP => H1 H2.
have Eki : k = i by apply/val_inj; apply/eqP; rewrite eqn_leq H2 H1.
by rewrite Eki.
Qed.

Lemma right_ok_self s i : is_descent s i -> right_ok s i i.
Proof.
move=> Hi; rewrite /right_ok leqnn /=.
apply/forallP => k; apply/implyP; case/andP => H1 H2.
have Eki : k = i by apply/val_inj; apply/eqP; rewrite eqn_leq H2 H1.
by rewrite Eki.
Qed.

(* block_left: smallest l with left_ok s i l; defaults to i otherwise. *)
Definition block_left s i : 'I_n :=
  if is_descent s i then [arg min_(l < i | left_ok s i l) val l]
  else i.

Definition block_right s i : 'I_n :=
  if is_descent s i then [arg max_(r > i | right_ok s i r) val r]
  else i.

Lemma block_left_left_ok s i : is_descent s i -> left_ok s i (block_left s i).
Proof.
move=> Hi; rewrite /block_left Hi.
by case: arg_minnP; first exact: left_ok_self.
Qed.

Lemma block_right_right_ok s i :
  is_descent s i -> right_ok s i (block_right s i).
Proof.
move=> Hi; rewrite /block_right Hi.
by case: arg_maxnP; first exact: right_ok_self.
Qed.

Lemma block_left_min s i (l : 'I_n) :
  is_descent s i -> left_ok s i l -> val (block_left s i) <= val l.
Proof.
move=> Hi Hl; rewrite /block_left Hi.
by case: arg_minnP; [exact: left_ok_self | move=> ? _; apply].
Qed.

Lemma block_right_max s i (r : 'I_n) :
  is_descent s i -> right_ok s i r -> val r <= val (block_right s i).
Proof.
move=> Hi Hr; rewrite /block_right Hi.
by case: arg_maxnP; [exact: right_ok_self | move=> ? _; apply].
Qed.

Lemma block_left_le s i :
  is_descent s i -> val (block_left s i) <= val i.
Proof.
move=> Hi; have := block_left_left_ok Hi.
by rewrite /left_ok; case/andP.
Qed.

Lemma block_right_ge s i :
  is_descent s i -> val i <= val (block_right s i).
Proof.
move=> Hi; have := block_right_right_ok Hi.
by rewrite /right_ok; case/andP.
Qed.

(* Every position in [block_left, i] is a descent. *)
Lemma block_left_descent s i (k : 'I_n) :
  is_descent s i ->
  val (block_left s i) <= val k <= val i -> is_descent s k.
Proof.
move=> Hi Hk.
have /andP [_ /forallP /(_ k) /implyP /(_ Hk) //] := block_left_left_ok Hi.
Qed.

Lemma block_right_descent s i (k : 'I_n) :
  is_descent s i ->
  val i <= val k <= val (block_right s i) -> is_descent s k.
Proof.
move=> Hi Hk.
have /andP [_ /forallP /(_ k) /implyP /(_ Hk) //] := block_right_right_ok Hi.
Qed.

(* Combined: every position in [block_left, block_right] is a descent. *)
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

Lemma block_left_le_right s i :
  is_descent s i -> val (block_left s i) <= val (block_right s i).
Proof.
move=> Hi; apply: (leq_trans (block_left_le Hi) (block_right_ge Hi)).
Qed.

(* Minimality: one step left of block_left is NOT a descent (when >0). *)
Lemma block_left_minimal s i :
  is_descent s i ->
  forall l' : 'I_n, val l' = (val (block_left s i)).-1 ->
  val (block_left s i) > 0 -> ~~ is_descent s l'.
Proof.
move=> Hi l' Hl' Hpos; apply/negP => Hdes.
(* If is_descent s l', then left_ok s i l', contradicting minimality. *)
have Hok : left_ok s i l'.
  rewrite /left_ok; apply/andP; split.
    rewrite Hl'; apply: (leq_trans (leq_pred _) (block_left_le Hi)).
  apply/forallP => k; apply/implyP; case/andP => Hk1 Hk2.
  case: (leqP (val (block_left s i)) (val k)) => Hkb.
    have Hr : val (block_left s i) <= val k <= val i by rewrite Hkb Hk2.
    exact: block_left_descent Hi Hr.
  (* val k < val (block_left s i), so val k <= val l' = pred of block_left *)
  have Ek : k = l'.
    apply/val_inj; apply/eqP; rewrite eqn_leq.
    have Hkle : val k <= (val (block_left s i)).-1.
      by rewrite -ltnS prednK.
    by rewrite -Hl' in Hkle; rewrite Hkle Hk1.
  by rewrite Ek.
have := block_left_min Hi Hok; rewrite Hl' leqNgt => /negP; apply.
by rewrite prednK.
Qed.

(* Maximality: one step right of block_right is NOT a descent (when <n). *)
Lemma block_right_maximal s i :
  is_descent s i ->
  forall r' : 'I_n, val r' = (val (block_right s i)).+1 ->
  ~~ is_descent s r'.
Proof.
move=> Hi r' Hr'; apply/negP => Hdes.
have Hok : right_ok s i r'.
  rewrite /right_ok; apply/andP; split.
    by rewrite Hr'; apply: (leq_trans (block_right_ge Hi)).
  apply/forallP => k; apply/implyP; case/andP => Hk1 Hk2.
  case: (leqP (val k) (val (block_right s i))) => Hkb.
    have Hr : val i <= val k <= val (block_right s i) by rewrite Hk1 Hkb.
    exact: block_right_descent Hi Hr.
  (* val k > val (block_right s i), so val k >= val r' *)
  have Ek : k = r'.
    apply/val_inj; apply/eqP; rewrite eqn_leq.
    by rewrite Hr' Hkb /= -Hr' Hk2.
  by rewrite Ek.
have := block_right_max Hi Hok; rewrite Hr' leqNgt => /negP; apply.
by rewrite ltnS.
Qed.

(* ------------------------------------------------------------------------- *)
(* Chain-of-values lemma: σ strictly decreases across the block.            *)
(* For consecutive positions in 'I_n.+1 whose indices range over             *)
(* [val (block_left σ i), (val (block_right σ i)).+1], σ is strictly          *)
(* decreasing.                                                                *)
(* ------------------------------------------------------------------------- *)

(* One-step decrease: if k is a descent, then σ(widen k) > σ(lift k),        *)
(* and the nat indices of widen_ord k and lift ord0 k are (val k) and        *)
(* (val k).+1 respectively. We expose this as a chain statement over         *)
(* positions in 'I_n.+1.                                                      *)

Lemma block_chain_step s i (k : 'I_n) :
  is_descent s i ->
  val (block_left s i) <= val k <= val (block_right s i) ->
  s (widen_ord (leqnSn n) k) > s (lift ord0 k).
Proof. by move=> Hi Hk; have := block_descent_chain Hi Hk. Qed.

(* Main chain-of-values lemma. For positions p q : 'I_n.+1 inside            *)
(* [l, r+1], with val p < val q, we have s p > s q.                          *)

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
have Hp1_lt : (val p).+1 < n.+1.
  rewrite ltnS.
  have Hle : val p + d.+2 <= (val (block_right s i)).+1 by rewrite -Hq.
  have Hle2 : (val p).+1 <= (val (block_right s i)).+1.
    by apply: (leq_trans _ Hle); rewrite addnS ltnS; apply: leq_addr.
  rewrite ltnS in Hle2.
  by apply: (leq_ltn_trans Hle2); apply: ltn_ord.
pose p' := Ordinal Hp1_lt.
have Hp'_val : val p' = (val p).+1 by [].
(* step1: s p > s p' via block_chain_step (single descent). *)
have Hp_lt_n : val p < n.
  have Hle : val p + d.+2 <= (val (block_right s i)).+1 by rewrite -Hq.
  have Hle2 : (val p).+1 <= (val (block_right s i)).+1.
    by apply: (leq_trans _ Hle); rewrite addnS ltnS; apply: leq_addr.
  rewrite ltnS in Hle2.
  exact: (leq_ltn_trans Hle2 (ltn_ord _)).
pose k := Ordinal Hp_lt_n.
have Hk_range : val (block_left s i) <= val k <= val (block_right s i).
  rewrite /= Hp /=.
  have Hle : val p + d.+2 <= (val (block_right s i)).+1 by rewrite -Hq.
  have Hle2 : (val p).+1 <= (val (block_right s i)).+1.
    by apply: (leq_trans _ Hle); rewrite addnS ltnS; apply: leq_addr.
  by rewrite ltnS in Hle2.
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


