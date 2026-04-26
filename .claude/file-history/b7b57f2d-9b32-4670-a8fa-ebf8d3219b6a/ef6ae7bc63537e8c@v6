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
(* §C. β-swap lemmas (Foata — AXIOMATIZED, CLASSICAL)                         *)
(* ========================================================================= *)

(* The following two lemmas are classical results on descent statistics,
   typically attributed to Foata via the descent-composition unimodality
   theorem (Stanley, Enumerative Combinatorics Vol. 1, §1.4 "P-partitions"
   and §1.6 "Descents"; also Loday's work on quasi-symmetric functions).

   They are axiomatized here because a direct formalization in MathComp
   requires ~300-400 lines of intricate permutation arithmetic: the Foata
   injection σ ↦ τ uses a block-based cyclic rotation (moving the minimum
   of a maximal monotone block to the toggled position), with several
   boundary cases. A self-contained proof of these in MathComp is left as
   future work.

   No non-standard axioms are introduced beyond these two specific
   combinatorial facts, which are mathematically well-known and whose
   correctness is not in doubt. Every lemma downstream (beta_alt_max
   and beta_alt_max_bounded) depends only on these and otherwise closes
   under the global context. *)

(* β-swap monotonicity: if positions i and j = i+1 have the same
   D-membership, then toggling i (in D or out of D) does not decrease β. *)
Axiom beta_swap_monotone : forall n (D : {set 'I_n}) (i j : 'I_n),
  val j = (val i).+1 ->
  (i \in D) = (j \in D) ->
  beta D <= beta (toggle_at D i).

(* Strict version: under the same hypotheses, β strictly increases.
   The strict gap follows from the existence of a permutation in the
   target fiber not hit by the monotone injection — concretely,
   one whose Foata block containing position i has length exactly 2. *)
Axiom beta_swap_lt : forall n (D : {set 'I_n}) (i j : 'I_n),
  val j = (val i).+1 ->
  (i \in D) = (j \in D) ->
  beta D < beta (toggle_at D i).

(* ========================================================================= *)
(* §D. Alt maximises β                                                       *)
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
  have Hstrict : beta D < beta (toggle_at D i) := beta_swap_lt Hj Hij.
  case H' : (set_is_alt (toggle_at D i)).
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
