(* q-factorial generating function for inv and maj.
   Stanley EC1 §1.3.4, Cor 1.3.10:
       \sum_(σ ∈ S_{n+1}) q^(inv σ) = [n+1]_q!
       \sum_(σ ∈ S_{n+1}) q^(maj σ) = [n+1]_q!.

   The inv-side proof uses the insert_max bijection from eulerian.v.
   The maj-side proof is a one-liner via inv_maj_equidistr.
*)
From mathcomp Require Import all_ssreflect fingroup perm ssrint ssralg poly.
From mathcomp_eulerian Require Import ordinal_reindex perm_compress
                                       descent eulerian inversions foata.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.

Open Scope ring_scope.

(* ========================================================================= *)
(* §0. q-integer and q-factorial                                             *)
(* ========================================================================= *)

Definition q_int (n : nat) : {poly int} := \sum_(i < n) 'X^i.
Definition q_fact (n : nat) : {poly int} := \prod_(k < n.+1) q_int k.+1.

(* ========================================================================= *)
(* §1. sum_rev_X reindexing helper                                           *)
(* ========================================================================= *)

Lemma sum_rev_X n :
  \sum_(p < n.+1) 'X^(n - val p)%N = q_int n.+1 :> {poly int}.
Proof.
rewrite /q_int.
rewrite (reindex_inj rev_ord_inj) /=.
apply: eq_bigr => i _.
by rewrite /= subKn // -ltnS ltn_ord.
Qed.

(* ========================================================================= *)
(* §2. inv (insert_max_perm τ p) = inv τ + (n.+1 - val p)                    *)
(* ========================================================================= *)

(* The set of inversions of (insert_max_perm τ p) splits into:
   - "p-pairs"   : pairs (p, j) with p < j; all are inversions because
                   σ(p) = ord_max > σ(j).  Count = n.+1 - val p.
   - "non-p"     : pairs (lift p j1, lift p j2) with j1 < j2.  These are
                   inversions of σ iff (j1, j2) is an inversion of τ. *)

Section InvInsertMax.
Variables (n : nat) (t : {perm 'I_n.+1}) (p : 'I_n.+2).

Notation σ := (insert_max_perm t p).

(* Lift map on pairs of 'I_{n+1}, sending (j1, j2) -> (lift p j1, lift p j2). *)

Lemma is_inv_lift_pair (j1 j2 : 'I_n.+1) :
  is_inv σ (lift p j1) (lift p j2) = is_inv t j1 j2.
Proof.
rewrite /is_inv ltn_lift !insert_max_perm_lift.
suff -> : (widen_ord (leqnSn n.+1) (t j2) < widen_ord (leqnSn n.+1) (t j1))
       = (t j2 < t j1) :> bool by [].
by [].
Qed.

(* Pairs of inversions of σ in the "p row": (p, j) with p < j.
   For such j = lift p k (since j ≠ p), σ p = ord_max, σ (lift p k) is a widen,
   so σ p > σ (lift p k) always.  Hence each such pair is an inversion.       *)
Lemma is_inv_p_lift (k : 'I_n.+1) : is_inv σ p (lift p k) = (p < lift p k).
Proof.
rewrite /is_inv insert_max_perm_at_p insert_max_perm_lift /=.
rewrite andbC; apply/idP/idP.
- by case/andP.
- by move=> ->; rewrite andbT; exact: ltn_ord.
Qed.

(* Pairs (i, p) with i < p are NOT inversions: σ p = ord_max > σ i. *)
Lemma is_inv_lift_p (k : 'I_n.+1) : is_inv σ (lift p k) p = false.
Proof.
rewrite /is_inv insert_max_perm_at_p insert_max_perm_lift.
have H : (val (widen_ord (leqnSn n.+1) (t k)) < val (ord_max : 'I_n.+2))%N
  by rewrite /=; exact: ltn_ord.
by rewrite andbC ltnNge (ltnW H).
Qed.

End InvInsertMax.

(* Helper: count elements of 'I_n.+1 with val >= p. *)
Lemma sum_geq_p n p :
  (p <= n.+1)%N ->
  \sum_(k : 'I_n.+1 | (p <= k)%N) (1%N) = (n.+1 - p)%N.
Proof.
move=> Hpn.
rewrite sum1dep_card.
rewrite -(card_ord (n.+1 - p)).
have shift_proof (k : 'I_(n.+1 - p)) : (val k + p < n.+1)%N
  by rewrite addnC -ltn_subRL ltn_ord.
pose shift (k : 'I_(n.+1 - p)) : 'I_n.+1 := Ordinal (shift_proof k).
have shift_inj : injective shift by move=> k1 k2 [] /addIn /val_inj.
rewrite -(card_imset _ shift_inj).
apply: eq_card => x; rewrite inE.
apply/idP/imsetP.
- move=> Hpx.
  have Hxp : (val x - p < n.+1 - p)%N
    by rewrite ltn_sub2r ?ltn_ord ?(leq_ltn_trans Hpx) ?ltn_ord.
  exists (Ordinal Hxp); first by [].
  by apply: val_inj; rewrite /= subnK.
- by case=> k _ ->; rewrite /= leq_addl.
Qed.

(* inv as a 2D unconditional sum over the boolean is_inv. *)
Lemma inv_via_sum n (s : {perm 'I_n.+1}) :
  inv s = (\sum_i \sum_j is_inv s i j)%N.
Proof.
rewrite /inv -sum1_card.
rewrite (eq_bigl (fun ij => is_inv s ij.1 ij.2));
  last by move=> [i j]; rewrite inE.
rewrite [LHS]big_mkcond /=.
rewrite (eq_bigr (fun p : 'I_n.+1 * 'I_n.+1 => is_inv s p.1 p.2 : nat));
  last by move=> p _; case: (is_inv s p.1 p.2).
rewrite [RHS]pair_bigA.
by apply: eq_bigr => p _; case: p.
Qed.

(* The headline arithmetic lemma. *)
Lemma inv_insert_max n (t : {perm 'I_n.+1}) (p : 'I_n.+2) :
  inv (insert_max_perm t p) = (inv t + (n.+1 - val p))%N.
Proof.
rewrite (inv_via_sum (insert_max_perm t p)).
rewrite (bigD1 p) //=.
(* The "p-row" contributes (n.+1 - val p) inversions. *)
have HpRow : (\sum_(j : 'I_n.+2) is_inv (insert_max_perm t p) p j)%N
           = (n.+1 - val p)%N.
{ rewrite (bigD1 p) //=.
  rewrite /is_inv ltnn /=.
  rewrite (reindex (lift p)) /=; last first.
  { exists (fun j => odflt (Ordinal (ltn0Sn n)) (unlift p j)).
    - by move=> k _; rewrite liftK.
    - move=> j; rewrite inE => /eqP Hj.
      by case: (unliftP p j) Hj => [k -> _ /=|->]; rewrite ?liftK ?eqxx. }
  rewrite add0n.
  under eq_bigr => j _ do
    rewrite insert_max_perm_at_p insert_max_perm_lift /= ltn_ord andbT.
  under eq_bigl => j do rewrite eq_sym (negbTE (neq_lift _ _)).
  rewrite (eq_bigr (fun j : 'I_n.+1 => (val p <= val j) : nat));
    last first.
  { move=> j _; rewrite /bump.
    case Hpj: (val p <= val j); rewrite ?add1n ?add0n.
    - by rewrite ltnS Hpj.
    - move/negbT: Hpj; rewrite -ltnNge => /ltnW Hpj.
      by rewrite ltnNge Hpj. }
  rewrite (eq_bigl predT) //.
  rewrite -big_mkcond /=.
  apply: sum_geq_p.
  by have := ltn_ord p; rewrite ltnS. }
(* The non-p rows contribute inv t. *)
have HnonpRow : (\sum_(i : 'I_n.+2 | i != p)
                  \sum_(j : 'I_n.+2) is_inv (insert_max_perm t p) i j)%N
              = inv t.
{ rewrite (inv_via_sum t).
  rewrite (reindex (lift p)) /=; last first.
  { exists (fun j => odflt (Ordinal (ltn0Sn n)) (unlift p j)).
    - by move=> k _; rewrite liftK.
    - move=> j; rewrite inE => /eqP Hj.
      by case: (unliftP p j) Hj => [k -> _ /=|->]; rewrite ?liftK ?eqxx. }
  under eq_bigl => j do rewrite eq_sym (negbTE (neq_lift _ _)).
  rewrite (eq_bigl xpredT); last by [].
  apply: eq_bigr => k1 _.
  rewrite (bigD1 p) //=.
  rewrite is_inv_lift_p add0n.
  rewrite (reindex (lift p)) /=; last first.
  { exists (fun j => odflt (Ordinal (ltn0Sn n)) (unlift p j)).
    - by move=> k _; rewrite liftK.
    - move=> j; rewrite inE => /eqP Hj.
      by case: (unliftP p j) Hj => [k -> _ /=|->]; rewrite ?liftK ?eqxx. }
  under eq_bigl => j do rewrite eq_sym (negbTE (neq_lift _ _)).
  rewrite (eq_bigl xpredT); last by [].
  apply: eq_bigr => k2 _.
  by rewrite (is_inv_lift_pair t p k1 k2). }
by rewrite HpRow HnonpRow addnC.
Qed.

(* ========================================================================= *)
(* §3. Headline theorem: inv_q_fact                                          *)
(* ========================================================================= *)

Theorem inv_q_fact n :
  \sum_(σ : {perm 'I_n.+1}) 'X^(inv σ) = q_fact n :> {poly int}.
Proof.
elim: n => [|n IH].
- (* n = 0: sum over the single permutation of S_1 *)
  rewrite /q_fact big_ord_recl big_ord0 mulr1 /q_int big_ord_recl big_ord0 addr0.
  rewrite expr0.
  rewrite (big_pred1 1%g) /=; last first.
  { move=> s; symmetry; apply/eqP.
    apply/permP => i; rewrite perm1; apply/val_inj.
    by case: i (s _) => [[|m] H1] [[|m'] H2] //=. }
  by rewrite inv_id expr0.
- (* Inductive step *)
  rewrite (reindex (fun tp : {perm 'I_n.+1} * 'I_n.+2 =>
                      insert_max_perm tp.1 tp.2)) /=; last first.
  { exact: (onW_bij _ (insert_max_perm_bij n)). }
  rewrite -(pair_bigA _ (fun (τ : {perm 'I_n.+1}) (p : 'I_n.+2) =>
                          'X^(inv (insert_max_perm τ p)))) /=.
  under eq_bigr => τ _ do
    under eq_bigr => p _ do rewrite inv_insert_max exprD.
  under eq_bigr => τ _ do rewrite -big_distrr /=.
  rewrite -big_distrl /=.
  rewrite IH sum_rev_X.
  by rewrite /q_fact [in RHS]big_ord_recr.
Qed.

(* ========================================================================= *)
(* §4. Corollary: maj_q_fact via Foata                                       *)
(* ========================================================================= *)

Theorem maj_q_fact n :
  \sum_(σ : {perm 'I_n.+1}) 'X^(maj σ) = q_fact n :> {poly int}.
Proof.
rewrite -inv_q_fact.
rewrite [in RHS](reindex (@foata_perm n)) /=; last first.
{ exact: (onW_bij _ (injF_bij (@foata_perm_inj n))). }
by apply: eq_bigr => s _; rewrite foata_perm_inv_maj.
Qed.
