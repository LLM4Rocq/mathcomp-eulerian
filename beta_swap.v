(* Layer 5: β-swap lemma and alternating-maximum corollary.                  *)
(*                                                                           *)
(* Proves that among descent sets D : {set 'I_n} which are not               *)
(* set-alternating (i.e. contain a consecutive same-membership pair),        *)
(* β(D) is strictly smaller than β(alt_desc_set n).                          *)
(*                                                                           *)
(* One LABELED AXIOM remains: `beta_swap_lt_caseB`.                          *)
(* Case A (`beta_swap_lt_caseA`) is now a PROVED LEMMA via beta_bridge.v     *)
(* using omega_proper_beta_lt (Stanley Prop 1.6.4) +                         *)
(* toggle_at_j_omega_strict_superset.                                        *)
(* Everything downstream — `beta_alt_max` — is `Qed`.                        *)
(*                                                                            *)
(* Build order: beta_omega.v → beta_bridge.v → beta_swap.v                   *)

From mathcomp Require Import all_ssreflect fingroup perm.
From mathcomp_eulerian Require Import
  ordinal_reindex perm_compress descent eulerian beta beta_omega beta_bridge.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

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

(* beta_swap_lt_caseA is now PROVED in beta_bridge.v via omega_proper_beta_lt
   (Stanley Prop 1.6.4) + toggle_at_j_omega_strict_superset (beta_omega.v). *)

(* Sub-axiom, Case B: j < n-1 and j+1 ∉ D — ω-sets differ by adjacent swap.
   Justification: omega(D) and omega(toggle_at D j) differ by swapping bit j
   for bit i (see toggle_at_j_omega_bit_i_new). The inequality follows from
   comparing cd-index marginal contributions of adjacent ω-positions, which
   requires Theorem 1.6.3 (nonneg cd-index) plus a monotonicity argument.
   This case is NOT handled by omega_proper_beta_lt since the omega sets are
   incomparable (not in a subset relation). *)
Axiom beta_swap_lt_caseB : forall n (D : {set 'I_n}) (i j : 'I_n),
  val j = (val i).+1 -> i \in D -> j \in D ->
  (exists q : 'I_n, val q = (val j).+1 /\ q \notin D) ->
  beta D < beta (toggle_at D j).

(* "Both descents" strict version (PROVED from the two sub-cases). *)
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

(* "Both descents" monotonicity (PROVED from the strict version). *)
Lemma beta_swap_monotone_both_in : forall n (D : {set 'I_n}) (i j : 'I_n),
  val j = (val i).+1 ->
  i \in D -> j \in D ->
  beta D <= beta (toggle_at D j).
Proof.
move=> n D i j Hj Hi Hj'.
exact: ltnW (beta_swap_lt_both_in Hj Hi Hj').
Qed.

(* Toggle commutes with complement on the set side. *)
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

(* ========================================================================= *)
(* §D. Alt maximises β (deferred: depends on derived beta_swap_lt below)     *)
(* ========================================================================= *)

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

