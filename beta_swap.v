(* Layer 5: alternating-maximum corollary for β-numbers.                     *)
(*                                                                           *)
(* Proves that among descent sets D : {set 'I_n} which are not               *)
(* set-alternating (i.e. contain a consecutive same-membership pair),        *)
(* β(D) is strictly smaller than β(alt_desc_set n).                          *)
(*                                                                           *)
(* NO AXIOMS.  beta_alt_max is proved directly via omega_proper_beta_lt      *)
(* (Stanley Prop 1.6.4 in beta_bridge.v): we show ω(D) ⊊ ω(alt) = setT     *)
(* whenever D is not set-alternating.                                        *)
(*                                                                           *)
(* Historical note: the original proof went through per-step strict          *)
(* monotonicity (beta_swap_lt_caseB).  That axiom turned out to be FALSE —   *)
(* counterexample: n=3, D={0,1}, toggle_at D 1 = {0} gives β=3=3, not <.    *)
(* The direct ω-based proof bypasses the swap chain entirely.                *)
(*                                                                            *)
(* Build order: beta_omega.v → beta_bridge.v → beta_swap.v                   *)

From mathcomp Require Import all_ssreflect fingroup perm.
From mathcomp_eulerian Require Import
  ordinal_reindex perm_compress descent eulerian beta beta_omega beta_bridge.
Require Import perm_seq_bridge.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* ========================================================================= *)
(* §B. Alternating descent set                                               *)
(* ========================================================================= *)

(** [alt_desc_set n] -- the canonical alternating descent set on
    [{set 'I_n}]: the set of even positions [{i : ~~ odd i}]. The
    descent set that maximises [beta] (Stanley Cor 1.6.5). *)
Definition alt_desc_set (n : nat) : {set 'I_n} :=
  [set i : 'I_n | ~~ odd i].

(** [mem_alt_desc_set] -- membership in [alt_desc_set n] reduces to
    parity: [i \in alt_desc_set n] iff [~~ odd i]. *)
Lemma mem_alt_desc_set n (i : 'I_n) :
  (i \in alt_desc_set n) = ~~ odd i.
Proof. by rewrite inE. Qed.

(** [set_is_alt D] -- decidable predicate: [D] is "set-alternating"
    iff every consecutive ordinal pair has differing [D]-memberships. *)
Definition set_is_alt (n : nat) (D : {set 'I_n}) : bool :=
  [forall i : 'I_n, [forall j : 'I_n,
     (val j == (val i).+1) ==> ((i \in D) != (j \in D))]].

(** [alt_desc_set_is_alt] -- the canonical [alt_desc_set] satisfies
    [set_is_alt] (consecutive parities differ). *)
Lemma alt_desc_set_is_alt n : set_is_alt (alt_desc_set n).
Proof.
apply/forallP => i; apply/forallP => j; apply/implyP => /eqP Hj.
rewrite !mem_alt_desc_set Hj /= negbK.
by case: (odd i).
Qed.

(** [set_not_altP] -- reflection: if [D] is not set-alternating then
    there exist consecutive [i,j] with the same [D]-membership. *)
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
(* §C. Toggle and complement lemmas                                          *)
(* ========================================================================= *)

(** [toggle_at_compl] -- the [toggle_at] operation commutes with
    complementation: [toggle_at (~: D) i = ~: toggle_at D i]. *)
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
(* §D. Alternating-set lemmas and Hamming distance                           *)
(* ========================================================================= *)

(** [alt_pair_parity] -- consecutive ordinals have opposite memberships
    in [alt_desc_set] (parity flips). *)
Lemma alt_pair_parity n (i j : 'I_n) :
  val j = (val i).+1 -> (i \in alt_desc_set n) != (j \in alt_desc_set n).
Proof.
move=> Hj.
rewrite !mem_alt_desc_set Hj /= negbK.
by case: (odd i).
Qed.

(** [sym_diff_toggle_in] -- toggling at any [k] in the symmetric
    difference [sym_diff D alt] strictly reduces the Hamming
    distance from [D] to [alt_desc_set n]. *)
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

(** [sym_diff_eq0] -- a symmetric difference of cardinality zero
    forces the two sets to be equal. *)
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

(** [compl_perm s] -- value-complement permutation: post-compose [s]
    with [rev_perm_ord n] so that [compl_perm s i = rev_ord (s i)].
    Bijection used to prove [beta_compl] (set complement invariance). *)
Definition compl_perm n (s : {perm 'I_n.+1}) : {perm 'I_n.+1} :=
  s * rev_perm_ord n.

(** [compl_permE] -- evaluation rule for [compl_perm s]: it sends [i]
    to [rev_ord (s i)]. *)
Lemma compl_permE n (s : {perm 'I_n.+1}) (i : 'I_n.+1) :
  compl_perm s i = rev_ord (s i).
Proof. by rewrite /compl_perm permM rev_perm_ordE. Qed.

(** [compl_perm_inj] -- [compl_perm] is injective on permutations
    (right-cancellation by [rev_perm_ord]). *)
Lemma compl_perm_inj n : injective (@compl_perm n).
Proof. by move=> s1 s2 H; apply: (mulIg (rev_perm_ord n)). Qed.

(** [compl_perm_involutive] -- [compl_perm] is an involution:
    applying it twice is the identity (since [rev_perm_ord] is). *)
Lemma compl_perm_involutive n : involutive (@compl_perm n).
Proof.
move=> s; rewrite /compl_perm -mulgA.
have -> : (rev_perm_ord n * rev_perm_ord n)%g = 1%g.
  apply/permP => i; rewrite permM perm1 !rev_perm_ordE.
  exact: rev_ordK.
by rewrite mulg1.
Qed.

(** [is_descent_compl] -- value-complementing flips every descent
    bit: [is_descent (compl_perm s) i = ~~ is_descent s i]. *)
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

(** [descent_set_compl] -- value-complementing complements the
    descent set: [descent_set (compl_perm s) = ~: descent_set s]. *)
Lemma descent_set_compl n (s : {perm 'I_n.+1}) :
  descent_set (compl_perm s) = ~: descent_set s.
Proof.
by apply/setP => i; rewrite !inE is_descent_compl.
Qed.

(** [beta_compl] -- the count [beta D] is invariant under set
    complementation: [beta D = beta (~: D)]. Proven via the
    value-complement involution [compl_perm]. *)
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

(** [set_is_alt_classify] -- classification of set-alternating sets
    (Stanley §1.6): exactly two such sets exist, [alt_desc_set n] and
    its complement. Together with [beta_compl] this implies all
    set-alternating sets share the same beta value. *)
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

(** [beta_set_is_alt_eq] -- any set-alternating [D'] has the same
    beta as [alt_desc_set n] (consequence of [set_is_alt_classify]
    and [beta_compl]). *)
Lemma beta_set_is_alt_eq n (D' : {set 'I_n}) :
  set_is_alt D' -> beta D' = beta (alt_desc_set n).
Proof.
move=> /set_is_alt_classify [-> //|->].
by rewrite beta_compl setCK.
Qed.

(* ========================================================================= *)
(* §G. Direct ω-based proof that alt maximises β                             *)
(* ========================================================================= *)

(** [not_set_is_alt_n_ge2] -- if [D] fails [set_is_alt] then [n >= 2]
    (a violating consecutive pair requires at least two positions). *)
Lemma not_set_is_alt_n_ge2 n (D : {set 'I_n}) :
  ~~ set_is_alt D -> 1 < n.
Proof.
move=> /set_not_altP [i [j [Hj _]]].
have Hjn : (val j < n)%N := ltn_ord j.
rewrite Hj in Hjn.
by apply: leq_ltn_trans Hjn; apply: ltn0Sn.
Qed.

(** [omega_set_alt_full] -- the omega-set of [alt_desc_set m.+1] is
    the full set [[set: 'I_m]]: every consecutive position pair has
    differing memberships, so every omega-bit is on. *)
Lemma omega_set_alt_full m :
  @omega_set m (alt_desc_set m.+1) = [set: 'I_m].
Proof.
apply/setP => k.
have Hk := @mem_omega_set m (alt_desc_set m.+1) k.
rewrite Hk inE.
(* LHS is (widen_ord _ k \in alt_desc_set m.+1) != (lift ord0 k \in ...) *)
(* RHS is true *)
rewrite !inE /=.
(* Now should have ~~ odd (widen ...) != ~~ odd (lift ...) = true *)
(* widen_ord k has val k, lift ord0 k has val k.+1 *)
rewrite /bump /=.
by case: (odd (val k)).
Qed.

(** [not_set_is_alt_omega_not_full] -- a non-set-alternating [D] has
    [omega_set D] strictly smaller than the full set; the offending
    consecutive pair witnesses an "off" omega bit. *)
Lemma not_set_is_alt_omega_not_full m (D : {set 'I_m.+1}) :
  ~~ set_is_alt D -> omega_set D != [set: 'I_m].
Proof.
move/set_not_altP => [i [j [Hj Hij]]].
(* We have i,j consecutive with same membership.
   The omega bit at the position k with widen k = i, lift k = j
   is NOT set (since D(i) = D(j) means same membership). *)
have Hik : val i < m.
  by have := ltn_ord j; rewrite Hj -ltnS.
pose k := Ordinal Hik.
apply/eqP => Hfull.
have : k \in omega_set D by rewrite Hfull inE.
rewrite mem_omega_set.
have Ewid : widen_ord (leqnSn m) k = i by apply/val_inj.
have Elif : lift ord0 k = j by apply/val_inj; rewrite /= /bump /= add1n -Hj.
rewrite Ewid Elif Hij. by rewrite eqxx.
Qed.

(** [beta_alt_max] -- HEADLINE RESULT (Stanley EC1 Cor 1.6.5): for any
    descent set [D] that is not set-alternating, [beta D < beta
    (alt_desc_set n)]; the alternating set strictly maximises [beta].
    Proof goes via [omega_proper_beta_lt] using [omega_set_alt_full]
    and [not_set_is_alt_omega_not_full]. *)
Lemma beta_alt_max n (D : {set 'I_n}) :
  ~~ set_is_alt D -> beta D < beta (alt_desc_set n).
Proof.
move=> Hnalt.
have Hn2 := not_set_is_alt_n_ge2 Hnalt.
(* Need n >= 2 to apply omega_proper_beta_lt.
   Write n = m.+2 so D : {set 'I_{m.+2}} = {set 'I_{(m.+1).+1}}. *)
case: n D Hnalt Hn2 => [|[|m]] D Hnalt Hn2 //.
(* Now n = m.+2, D : {set 'I_{m.+2}}. *)
apply: (omega_proper_beta_lt (m := m.+1)).
(* omega_set D \proper omega_set (alt_desc_set (m.+2)) *)
rewrite omega_set_alt_full.
(* omega_set D \proper [set: 'I_{m.+1}] *)
apply/properP; split.
- by apply/subsetP => x _; rewrite inE.
- (* omega_set D != setT, so there exists k not in omega_set D *)
  (* Directly from the set_not_altP witness *)
  case: (set_not_altP Hnalt) => i0 [j0 [Hj0 Hij0]].
  have Hik0 : val i0 < m.+1.
    by have := ltn_ord j0; rewrite Hj0 -ltnS.
  pose k0 := Ordinal Hik0.
  have Hk0 : k0 \notin omega_set D.
    rewrite (@mem_omega_set m.+1).
    have Ew : widen_ord (leqnSn m.+1) k0 = i0 by apply/val_inj.
    have El : lift ord0 k0 = j0 by apply/val_inj; rewrite /= /bump /= add1n -Hj0.
    by rewrite Ew El Hij0 eqxx.
  exists k0; first by rewrite inE.
  exact: Hk0.
Qed.
