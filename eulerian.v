(* Layer 3: Eulerian numbers and their properties. *)
From mathcomp Require Import all_ssreflect fingroup perm binomial ssrint ssralg.
From mathcomp_eulerian Require Import ordinal_reindex perm_compress descent.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* ========================================================================= *)
(* Eulerian numbers                                                          *)
(* ========================================================================= *)

(** [eulerian n k] is the Eulerian number [A(n+1, k)]: the number of
    permutations of ['I_n.+1] with exactly [k] descents. Stanley's
    [A(n+1, k)] (Stanley EC1, S1.4). *)
Definition eulerian (n k : nat) : nat :=
  #|[set s : {perm 'I_n.+1} | des s == k]|.

(* ========================================================================= *)
(* Base cases and bounds                                                     *)
(* ========================================================================= *)

Section EulerianBasic.

(** Row sum: summing [eulerian n k] over [k <= n] gives the cardinality of
    [{perm 'I_n.+1}]. Partition of permutations by descent count. *)
Lemma eulerian_row_sum n : \sum_(k < n.+1) eulerian n k = #|{perm 'I_n.+1}|.
Proof.
rewrite /eulerian -sum1_card.
rewrite (partition_big
           (fun s : {perm 'I_n.+1} => inord (des s) : 'I_n.+1) xpredT) //=.
apply: eq_bigr => k _; rewrite -sum1_card; apply: eq_bigl => s; rewrite inE.
by rewrite -val_eqE /= inordK // ltnS des_le.
Qed.

(** Row sum equals [(n+1)!]: combines [eulerian_row_sum] with
    [|S_{n+1}| = (n+1)!]. *)
Lemma eulerian_row_sum_fact n : \sum_(k < n.+1) eulerian n k = n.+1`!.
Proof. by rewrite eulerian_row_sum card_Sn. Qed.

(** Out-of-range vanishing: [eulerian n k = 0] when [k > n], since no
    permutation has more than [n] descents. *)
Lemma eulerian_out_of_range n k : n < k -> eulerian n k = 0.
Proof.
move=> nk; apply/eqP; rewrite cards_eq0; apply/eqP/setP => s.
rewrite !inE; apply/negbTE; rewrite neq_ltn.
by rewrite (leq_ltn_trans (des_le s) nk).
Qed.

(** Only the identity has zero descents. Used to prove [eulerian n 0 = 1]. *)
Lemma des0_id n (s : {perm 'I_n.+1}) : des s = 0 -> s = 1%g.
Proof.
move=> Hds.
have Hds0 : descent_set s = set0.
  by apply/eqP; rewrite -cards_eq0; apply/eqP.
have Hmono : forall i : 'I_n,
    (val (s (widen_ord (leqnSn n) i)) < val (s (lift ord0 i)))%N.
  move=> i.
  have Hneq : widen_ord (leqnSn n) i != lift ord0 i.
    by apply/eqP => /(congr1 val) /=; rewrite /bump /= add1n => /n_Sn.
  have : i \notin descent_set s by rewrite Hds0 inE.
  rewrite mem_descent_set /is_descent -leqNgt ltn_neqAle => -> /=.
  by rewrite andbT; apply/eqP => /val_inj/perm_inj/eqP; apply/negP.
have Hle : forall i : 'I_n.+1, (val i <= val (s i))%N.
  case=> m; elim: m => [|m IHm] Hm; first exact: leq0n.
  have Hm1 : m < n.+1 by apply: ltnW.
  have Hmn : m < n by [].
  have := Hmono (Ordinal Hmn).
  have -> : widen_ord (leqnSn n) (Ordinal Hmn) = Ordinal Hm1 by exact: val_inj.
  have -> : lift ord0 (Ordinal Hmn) = Ordinal Hm.
    by apply: val_inj; rewrite /= /bump /= add1n.
  by move/(leq_ltn_trans (IHm Hm1)).
have Hsum : \sum_(i : 'I_n.+1) (val (s i) - val i)%N = 0.
  rewrite sumnB // [X in _ - X = _](reindex_inj (@perm_inj _ s)) subnn //.
apply/permP => i; rewrite perm1; apply/val_inj.
move/eqP: Hsum; rewrite (bigD1 i) //= addn_eq0 subn_eq0 => /andP[/eqP Hi _].
by apply/eqP; rewrite eqn_leq Hle /= -subn_eq0 Hi.
Qed.

(** Boundary value: [eulerian n 0 = 1], counting only the identity. *)
Lemma eulerian_n_0 n : eulerian n 0 = 1.
Proof.
rewrite /eulerian -(cards1 (1%g : {perm 'I_n.+1})); apply: eq_card => s.
rewrite !inE; apply/eqP/eqP => [/des0_id //|->]; exact: des_id.
Qed.

End EulerianBasic.

(* ========================================================================= *)
(* Symmetry: eulerian n k = eulerian n (n - k)                               *)
(* ========================================================================= *)

(** Reversal is injective on permutations (left cancellation by
    [rev_perm_ord]). *)
Lemma rev_perm_inj n : injective (@rev_perm n).
Proof. by move=> s1 s2; rewrite /rev_perm; exact: mulgI. Qed.

(** Reversal is an involution: [rev_perm (rev_perm s) = s]. *)
Lemma rev_perm_involutive n : involutive (@rev_perm n).
Proof. by move=> s; apply/permP => j; rewrite !rev_permE rev_ordK. Qed.

(** Symmetry of Eulerian numbers: [A(n+1, k) = A(n+1, n-k)] (Stanley EC1, S1.4).
    Proved via the reversal involution on [{perm 'I_n.+1}]. *)
Lemma eulerian_symm n k : k <= n -> eulerian n k = eulerian n (n - k).
Proof.
move=> kn; rewrite /eulerian.
rewrite -(card_imset _ (@rev_perm_inj n)).
congr #|pred_of_set _|; apply/setP => s; rewrite !inE.
apply/imsetP/idP.
+ by case=> t; rewrite inE => /eqP <- ->; rewrite des_rev_perm.
+ move=> /eqP Hs; exists (rev_perm s); last by rewrite rev_perm_involutive.
  by rewrite inE des_rev_perm Hs subKn.
Qed.

(** Boundary value: [eulerian n n = 1], counting only the reversal
    permutation. *)
Lemma eulerian_n_n n : eulerian n n = 1.
Proof. by rewrite (eulerian_symm (leqnn n)) subnn eulerian_n_0. Qed.

(* ========================================================================= *)
(* Recurrence:                                                               *)
(*   eulerian n.+1 k.+1 = k.+2 * eulerian n k.+1 + (n.+1 - k) * eulerian n k *)
(* (The k = 0 case is eulerian_n_0: eulerian n.+1 0 = 1.)                    *)
(*                                                                           *)
(* We prove this via the "insert-max-value" bijection                        *)
(*   {perm 'I_n.+2} ≅ {perm 'I_n.+1} × 'I_n.+2                             *)
(*   σ ↦ (τ, p) *)
(* where p = σ^{-1}(ord_max) is the position of the max value and τ is     *)
(* obtained by deleting that max from σ's one-line notation.                 *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Helpers on widen_ord (leqnSn n.+1) : 'I_n.+1 -> 'I_n.+2                   *)
(* ------------------------------------------------------------------------- *)

(** [widen_ord (leqnSn n.+1) : 'I_n.+1 -> 'I_n.+2] is injective. *)
Lemma widenSn_inj n : injective (widen_ord (leqnSn n.+1)).
Proof. by move=> i1 i2 H; apply/val_inj; exact: (congr1 val H). Qed.

(** Widening from ['I_n.+1] to ['I_n.+2] never reaches [ord_max]. *)
Lemma widenSn_neq_ord_max n (j : 'I_n.+1) :
  widen_ord (leqnSn n.+1) j != (ord_max : 'I_n.+2).
Proof.
by apply/eqP => H; move: (congr1 val H) (ltn_ord j) => /= ->; rewrite ltnn.
Qed.

(* ------------------------------------------------------------------------- *)
(* insert_max_perm: inserting max value at a given position                  *)
(* ------------------------------------------------------------------------- *)

Section InsertMax.
Variables (n : nat) (t : {perm 'I_n.+1}) (p : 'I_n.+2).

(** Underlying function of [insert_max_perm t p]: sends [p] to [ord_max] and
    elsewhere lifts [t] via [widen_ord]. *)
Definition insert_max_fun (i : 'I_n.+2) : 'I_n.+2 :=
  match unlift p i with
  | Some j => widen_ord (leqnSn _) (t j)
  | None => ord_max
  end.

(** [insert_max_fun] sends position [p] to [ord_max]. *)
Lemma insert_max_fun_p : insert_max_fun p = ord_max.
Proof. by rewrite /insert_max_fun unlift_none. Qed.

(** [insert_max_fun] on lifted positions widens [t]. *)
Lemma insert_max_fun_lift (j : 'I_n.+1) :
  insert_max_fun (lift p j) = widen_ord (leqnSn _) (t j).
Proof. by rewrite /insert_max_fun liftK. Qed.

(** [insert_max_fun] is injective: combine injectivity of [widen] and [t]. *)
Lemma insert_max_fun_inj : injective insert_max_fun.
Proof.
move=> i1 i2; rewrite /insert_max_fun.
case: (unliftP p i1) => [j1 ->|->]; case: (unliftP p i2) => [j2 ->|->].
- by move/widenSn_inj/perm_inj ->.
- by move/eqP; rewrite (negbTE (widenSn_neq_ord_max _)).
- by move/eqP; rewrite eq_sym (negbTE (widenSn_neq_ord_max _)).
- by [].
Qed.

(** [insert_max_perm t p] is the permutation of ['I_n.+2] obtained from
    [t : {perm 'I_n.+1}] by inserting the value [ord_max] at position [p].
    Underlies the bijection [{perm 'I_n.+2} ~= {perm 'I_n.+1} x 'I_n.+2]. *)
Definition insert_max_perm : {perm 'I_n.+2} := perm insert_max_fun_inj.

(** Equivalence with the underlying [insert_max_fun] for rewriting. *)
Lemma insert_max_permE i : insert_max_perm i = insert_max_fun i.
Proof. by rewrite permE. Qed.

(** [insert_max_perm t p] sends [p] to [ord_max], the inserted maximum value. *)
Lemma insert_max_perm_at_p : insert_max_perm p = ord_max.
Proof. by rewrite insert_max_permE insert_max_fun_p. Qed.

(** [insert_max_perm t p] on lifted positions widens [t]. *)
Lemma insert_max_perm_lift (j : 'I_n.+1) :
  insert_max_perm (lift p j) = widen_ord (leqnSn _) (t j).
Proof. by rewrite insert_max_permE insert_max_fun_lift. Qed.

End InsertMax.

(* ------------------------------------------------------------------------- *)
(* Inverse: extract_max_perm                                                *)
(* ------------------------------------------------------------------------- *)

Section ExtractMax.
Variables (n : nat) (s : {perm 'I_n.+2}) (p : 'I_n.+2).
Hypothesis (sp : s p = ord_max).

(** Off-position values of [s] avoid [ord_max] when [s p = ord_max], by
    injectivity. *)
Fact extract_max_ne (j : 'I_n.+1) : s (lift p j) != (ord_max : 'I_n.+2).
Proof.
rewrite -sp; apply/eqP => /perm_inj /eqP.
by rewrite eq_sym (negbTE (neq_lift _ _)).
Qed.

(** Underlying function of [extract_max_perm]: removes the value [ord_max]
    (located at position [p]) and reindexes the remaining values onto
    ['I_n.+1]. *)
Definition extract_max_fun (j : 'I_n.+1) : 'I_n.+1 :=
  odflt j (unlift ord_max (s (lift p j))).

(** Defining equation: widening [extract_max_fun j] recovers [s (lift p j)]. *)
Lemma extract_max_funE (j : 'I_n.+1) :
  widen_ord (leqnSn n.+1) (extract_max_fun j) = s (lift p j).
Proof.
rewrite /extract_max_fun.
case: (unliftP ord_max (s (lift p j))) => [k ->|H] /=.
- by apply: val_inj; rewrite /= /bump /= leqNgt ltn_ord.
- by move: (extract_max_ne j); rewrite H eqxx.
Qed.

(** [extract_max_fun] is injective. *)
Lemma extract_max_fun_inj : injective extract_max_fun.
Proof.
move=> j1 j2 /(congr1 (widen_ord (leqnSn n.+1))).
rewrite !extract_max_funE => /perm_inj /lift_inj //.
Qed.

(** [extract_max_perm sp] is the permutation of ['I_n.+1] obtained from
    [s : {perm 'I_n.+2}] (with [s p = ord_max]) by deleting the value
    [ord_max]. *)
Definition extract_max_perm : {perm 'I_n.+1} := perm extract_max_fun_inj.

(** Equivalence with the underlying [extract_max_fun] for rewriting. *)
Lemma extract_max_permE j : extract_max_perm j = extract_max_fun j.
Proof. by rewrite permE. Qed.

(** Defining equation: widening [extract_max_perm j] recovers [s (lift p j)]. *)
Lemma extract_max_widen (j : 'I_n.+1) :
  widen_ord (leqnSn n.+1) (extract_max_perm j) = s (lift p j).
Proof. by rewrite extract_max_permE extract_max_funE. Qed.

End ExtractMax.

(* ------------------------------------------------------------------------- *)
(* Bijection: insert_max_perm and extract_max_perm are inverses             *)
(* ------------------------------------------------------------------------- *)

Section InsertExtractBij.
Variable n : nat.

(** Left inverse: extracting the max from a freshly inserted permutation
    recovers [t]. *)
(** Right inverse: inserting the extracted max back at position [p]
    recovers [s]. *)
Lemma insert_extract_max (s : {perm 'I_n.+2}) (p : 'I_n.+2)
    (sp : s p = ord_max) :
  insert_max_perm (extract_max_perm sp) p = s.
Proof.
apply/permP => i; rewrite insert_max_permE /insert_max_fun.
case: (unliftP p i) => [j ->|->]; last exact/esym.
by rewrite -extract_max_widen.
Qed.

End InsertExtractBij.

(* ------------------------------------------------------------------------- *)
(* Descent count under insertion                                            *)
(* ------------------------------------------------------------------------- *)

Section DesInsertMax.
Variables (n : nat) (t : {perm 'I_n.+1}).

(** Inserting [ord_max] at position [0] adds exactly one descent (a fresh
    descent is created at position [0] from the new max value). *)
Lemma des_insert_max_ord0 :
  des (insert_max_perm t ord0) = (des t).+1.
Proof.
rewrite /des /descent_set.
suff -> : [set i : 'I_n.+1 | is_descent (insert_max_perm t ord0) i]
        = (ord0 : 'I_n.+1) |: [set lift ord0 j | j in [set i | is_descent t i]].
  rewrite cardsU1 card_imset; last exact: lift_inj.
  have -> : ord0 \notin [set lift ord0 j | j in [set i | is_descent t i]].
    apply/imsetP => -[x _ Hx].
    by have := neq_lift ord0 x; rewrite -Hx eqxx.
  by rewrite add1n.
apply/setP => i; rewrite !inE.
case: (unliftP ord0 i) => [j ->|->].
- rewrite eq_sym (negbTE (neq_lift _ _)) /=.
  have E1 : widen_ord (leqnSn n.+1) (lift ord0 j)
          = lift ord0 (widen_ord (leqnSn n) j) :> 'I_n.+2.
    by apply/val_inj; rewrite /= /bump leq0n /= add1n.
  rewrite /is_descent E1 !insert_max_perm_lift.
  apply/idP/imsetP.
  + by move=> H; exists j; first by rewrite inE /is_descent.
  + by case=> j' /[!inE] Hj' /lift_inj ->; rewrite /is_descent.
- rewrite eqxx orTb /is_descent.
  have -> : widen_ord (leqnSn n.+1) (ord0 : 'I_n.+1) = ord0 :> 'I_n.+2.
    by apply/val_inj.
  by rewrite insert_max_perm_at_p insert_max_perm_lift /=; apply: ltn_ord.
Qed.

(** Inserting [ord_max] at position [ord_max] (the rightmost position) does not
    change the descent count. *)
Lemma des_insert_max_ord_max :
  des (insert_max_perm t (ord_max : 'I_n.+2)) = des t.
Proof.
rewrite /des /descent_set.
suff -> : [set i : 'I_n.+1 | is_descent (insert_max_perm t ord_max) i]
        = [set (lift ord_max j : 'I_n.+1)
            | j in [set i : 'I_n | is_descent t i]].
  by rewrite card_imset //; exact: lift_inj.
apply/setP => i; rewrite !inE.
case: (unliftP ord_max i) => [j ->|->].
- have E1 : widen_ord (leqnSn n.+1) (lift ord_max j)
          = lift ord_max (widen_ord (leqnSn n) j) :> 'I_n.+2.
    apply/val_inj; rewrite /= /bump /=.
    rewrite leqNgt (ltn_ord j) /=.
    by rewrite leqNgt (leq_trans (ltn_ord j) (leqnSn n)).
  have E2 : lift ord0 (lift ord_max j : 'I_n.+1)
          = lift ord_max (lift ord0 j) :> 'I_n.+2.
    apply/val_inj => /=.
    rewrite /bump /=.
    have H2 : (n <= j) = false by apply/negbTE; rewrite -ltnNge; apply: ltn_ord.
    have H3 : (n.+1 <= j.+1) = false
      by apply/negbTE; rewrite -ltnNge; apply: ltn_ord.
    by rewrite H2 H3.
  rewrite /is_descent E1 E2 !insert_max_perm_lift.
  apply/idP/imsetP.
  + by move=> H; exists j; first by rewrite inE /is_descent.
  + by case=> j' /[!inE] Hj' /lift_inj ->; rewrite /is_descent.
- rewrite /is_descent.
  have E1 : widen_ord (leqnSn n.+1) (ord_max : 'I_n.+1)
          = lift ord_max (ord_max : 'I_n.+1) :> 'I_n.+2.
    by apply/val_inj; rewrite /= /bump /= leqNgt ltnSn.
  have -> : lift ord0 (ord_max : 'I_n.+1) = ord_max :> 'I_n.+2.
    by apply/val_inj.
  rewrite E1 insert_max_perm_lift insert_max_perm_at_p.
  apply/idP/imsetP.
  + by move=> H; move: (ltn_ord (t (ord_max : 'I_n.+1)));
       rewrite ltnNge /= in H; case/negP: H; apply: ltnW.
  + case=> j _ /eqP; rewrite -val_eqE /= /bump /= leqNgt ltn_ord /= => /eqP eqn.
    rewrite add0n in eqn.
    by move: (ltn_ord j); rewrite -eqn ltnn.
Qed.

(** Inserting [ord_max] at an interior position above [j] adds a descent
    iff [j] was an ascent in [t]. Key combinatorial lemma for the
    Eulerian recurrence. *)
Lemma des_insert_max_interior (j : 'I_n) :
  des (insert_max_perm t (lift ord0 (widen_ord (leqnSn n) j))) =
    des t + ~~ is_descent t j.
Proof.
set h := widen_ord (leqnSn n) j.
set p := lift ord0 h.
set sigma := insert_max_perm t p.
rewrite /des /descent_set.
suff -> : [set i | is_descent sigma i]
        = [set lift h x | x in [set y | is_descent t y] :|: [set j]].
  rewrite card_imset; last exact: lift_inj.
  rewrite setUC cardsU1 inE /=.
  by case: (is_descent t j); rewrite addnC.
apply/setP => i; rewrite !inE.
case: (unliftP h i) => [x ->|->].
- (* Goal: is_descent σ (lift h x) = x ∈ descent_set t ∪ {j}
         (up to lift h) *)
  have sigma_lift0 : forall x : 'I_n,
    sigma (lift ord0 (lift h x)) = widen_ord (leqnSn n.+1) (t (lift ord0 x)).
    move=> y.
    have E : lift ord0 (lift h y) = lift p (lift ord0 y) :> 'I_n.+2.
      by apply/val_inj => /=; rewrite /p /=; rewrite /bump /= addnCA.
    by rewrite /sigma E insert_max_perm_lift.
  have -> :
      (lift h x \in
       [set lift h x0 | x0 in [set y | is_descent t y] :|: [set j]])
      = (is_descent t x) || (x == j).
    apply/imsetP/idP => [[y]|].
    + by rewrite !inE => /orP[Hy|/eqP ->] /lift_inj ->;
         [rewrite Hy|rewrite eqxx orbT].
    + case/orP => [H|/eqP ->].
      - by exists x; rewrite // !inE H.
      - by exists j; rewrite // !inE eqxx orbT.
  rewrite /is_descent sigma_lift0 /=.
  case: (eqVneq x j) => [->|xnj].
  + have -> : sigma (widen_ord (leqnSn n.+1) (lift h j)) = ord_max.
      have E : widen_ord (leqnSn n.+1) (lift h j) = p :> 'I_n.+2.
        by apply/val_inj; rewrite /= /p /= /bump /= leqnn.
      by rewrite /sigma E insert_max_perm_at_p.
    by rewrite orbT; apply: ltn_ord.
  + rewrite orbF.
    have E : widen_ord (leqnSn n.+1) (lift h x) =
             lift p (widen_ord (leqnSn n) x) :> 'I_n.+2.
      apply/val_inj; rewrite /= /p /= /bump /=.
      case: (ltngtP x j) => [Hxj|Hxj|Hxj].
      - by [].
      - by [].
      - by rewrite -val_eqE /= Hxj eqxx in xnj.
    by rewrite /sigma E insert_max_perm_lift.
- (* Goal: is_descent σ h = h ∈ image (false) *)
  have Rfalse :
      (h \in [set lift h x | x in [set y | is_descent t y] :|: [set j]])
      = false.
    by apply/negbTE/imsetP => -[y _ Hy]; have := neq_lift h y; rewrite -Hy eqxx.
  rewrite Rfalse /is_descent.
  have E1 : widen_ord (leqnSn n.+1) h = lift p h :> 'I_n.+2.
    apply/val_inj; rewrite /= /p /= /bump /=.
    by rewrite add1n ltnn.
  have E2 : lift ord0 h = p :> 'I_n.+2 by [].
  rewrite E1 E2 insert_max_perm_lift insert_max_perm_at_p.
  apply/negbTE; rewrite -leqNgt.
  by apply: ltnW; rewrite /=; exact: ltn_ord.
Qed.

End DesInsertMax.

(* ------------------------------------------------------------------------- *)
(* Bijection on fibers: {σ : σ^{-1} ord_max = p} ≃ {perm 'I_n.+1}        *)
(* ------------------------------------------------------------------------- *)

(** The inverse of [insert_max_perm t p] sends [ord_max] back to [p]:
    identifies the fiber of position-of-max under insertion. *)
Lemma insert_max_perm_fiber n (p : 'I_n.+2) (t : {perm 'I_n.+1}) :
  ((insert_max_perm t p)^-1)%g ord_max = p.
Proof.
apply: (@perm_inj _ (insert_max_perm t p)).
by rewrite permKV insert_max_perm_at_p.
Qed.

(** The pairing map [(t, p) |-> insert_max_perm t p] is injective. *)
(** The pairing map [(t, p) |-> insert_max_perm t p] is surjective: every
    permutation of ['I_n.+2] arises by inserting the max at some position. *)
(* ------------------------------------------------------------------------- *)
(* Cardinality of descent / ascent sets                                      *)
(* ------------------------------------------------------------------------- *)

(** The descent count [des t] equals the sum of descent indicators
    over positions. *)
Lemma sum_descent n (t : {perm 'I_n.+1}) :
  \sum_(j : 'I_n) is_descent t j = des t.
Proof.
rewrite /des /descent_set -sum1dep_card [RHS]big_mkcond /=.
by apply: eq_bigr => j _; case: (is_descent t j).
Qed.

(** The ascent count [n - des t] equals the sum of ascent indicators
    over positions. *)
(* ------------------------------------------------------------------------- *)
(* Main recurrence                                                           *)
(* ------------------------------------------------------------------------- *)

(** Proof-irrelevant variant of [extract_insert_max], threading any
    equality proof [insert_max_perm t p p = ord_max] rather than the
    canonical one. *)
(** The pairing map [(t, p) |-> insert_max_perm t p] is a bijection
    [{perm 'I_n.+1} x 'I_n.+2] ~= [{perm 'I_n.+2}]. Foundation of the
    recurrence. *)
Lemma insert_max_perm_bij n :
  bijective (fun tp : {perm 'I_n.+1} * 'I_n.+2 => insert_max_perm tp.1 tp.2).
Proof.
pose g (s : {perm 'I_n.+2}) : {perm 'I_n.+1} * 'I_n.+2 :=
  (extract_max_perm (permKV s ord_max), (s^-1)%g ord_max).
exists g.
- move=> [t p] /=; rewrite /g /=.
  (* First extract p *)
  congr pair; last exact: insert_max_perm_fiber.
  apply/permP => j; apply: (@widenSn_inj n).
  rewrite extract_max_widen.
  have E : lift ((insert_max_perm t p)^-1%g ord_max) j = lift p j :> 'I_n.+2.
    by apply/val_inj; rewrite /= insert_max_perm_fiber.
  by rewrite E insert_max_perm_lift.
- move=> s /=; rewrite /g; exact: insert_extract_max.
Qed.

(* ------------------------------------------------------------------------- *)
(* Main recurrence                                                            *)
(* ------------------------------------------------------------------------- *)

(** Eulerian recurrence (Stanley EC1, S1.4):
    [A(n+2, k+1) = (k+2) A(n+1, k+1) + (n+1-k) A(n+1, k)].
    Proved via the insert-max bijection. *)
Lemma eulerian_rec n k :
  eulerian n.+1 k.+1 = k.+2 * eulerian n k.+1 + (n.+1 - k) * eulerian n k.
Proof.
rewrite /eulerian -sum1dep_card.
rewrite (reindex _ (onW_bij _ (insert_max_perm_bij n))) /=.
rewrite -(pair_big_dep xpredT
            (fun t p => des (insert_max_perm t p) == k.+1)
            (fun _ _ => 1)) /=.
have lom : lift ord0 (ord_max : 'I_n.+1) = (ord_max : 'I_n.+2) by apply/val_inj.
under eq_bigr => t _ do
  rewrite big_mkcond big_ord_recl big_ord_recr /= lom
          des_insert_max_ord0 des_insert_max_ord_max.
under eq_bigr => t _ do under eq_bigr => i _ do rewrite des_insert_max_interior.
under eq_bigr => t _.
  rewrite (bigID (fun i : 'I_n => is_descent t i)) /=.
  under eq_bigr => i Hi do rewrite Hi addn0.
  under [X in _ + X + _]eq_bigr => i Hi do rewrite (negbTE Hi) addn1.
  over.
have asc_card (u : {perm 'I_n.+1}) : #|[set x | ~~ is_descent u x]| = n - des u.
  have -> : [set x | ~~ is_descent u x] = ~: [set x | is_descent u x].
    by apply/setP => i; rewrite !inE.
  by rewrite cardsCs setCK card_ord.
under eq_bigr => t _ do
  rewrite !eqSS !sum_nat_cond_const -/(descent_set t) -/(des t) asc_card.
rewrite -!sum1dep_card !big_distrr /=.
rewrite [X in _ = _ + X]big_mkcond /=
        [X in _ = X + _]big_mkcond /= -big_split /=.
apply: eq_bigr => t _; rewrite !muln1.
case E1: (des t == k); case E2: (des t == k.+1);
  rewrite /= ?addn0 ?add0n ?mul0n ?muln0.
- move/eqP: E1 E2 => ->; move/eqP => Habs.
  by exfalso; move: (ltnSn k); rewrite {1}Habs ltnn.
- move/eqP: E1 => <-.
  by rewrite add0n muln1 add1n subSn //; apply: des_le.
- by move/eqP: E2 => ->; rewrite muln1 addn0 addn1.
- by [].
Qed.

(* ========================================================================= *)
(* Worpitzky's identity                                                       *)
(*   x^(n+1) = \sum_(k < n+1) eulerian n k * C(x+k, n+1)                      *)
(* ========================================================================= *)

(** Key algebraic identity for Worpitzky's induction step (valid for [k <= n]):
    [x * C(x+k, n+1) = (k+1) C(x+k, n+2) + (n+1-k) C(x+k+1, n+2)]. *)
Lemma worpitzky_binom_id x k n : k <= n ->
  x * 'C(x + k, n.+1) =
    k.+1 * 'C(x + k, n.+2) + (n.+1 - k) * 'C(x + k.+1, n.+2).
Proof.
move=> kle.
rewrite addnS binS mulnDr addnA -mulnDl.
have -> : k.+1 + (n.+1 - k) = n.+2 by rewrite addSn subnKC// ltnW.
rewrite mul_bin_left -mulnDl.
case: (leqP n.+1 (x + k)) => h.
- symmetry; rewrite addnBA; first by rewrite subnK // addnK.
  exact: ltnW.
- by rewrite !bin_small ?muln0 //; exact: (leq_trans h (leqnSn _)).
Qed.

(** Worpitzky's identity (Stanley EC1, S1.4):
    [x^(n+1) = sum_(k < n+1) A(n+1, k) * C(x+k, n+1)].
    Proved by induction on [n] using [eulerian_rec] and [worpitzky_binom_id]. *)
Lemma worpitzky n x :
  x ^ n.+1 = \sum_(k < n.+1) eulerian n k * 'C(x + k, n.+1).
Proof.
elim: n x => [|n IH] x.
  by rewrite big_ord1 eulerian_n_0 mul1n bin1 addn0 expn1.
rewrite expnS IH big_distrr /=.
under eq_bigr => k _.
  rewrite mulnA (mulnC x) -mulnA.
  rewrite (worpitzky_binom_id _ _ (n := n)); last by rewrite -ltnS.
  rewrite mulnDr.
  over.
rewrite big_split /=.
rewrite big_ord_recl eulerian_n_0 mul1n addn0.
rewrite [RHS]big_ord_recl eulerian_n_0 mul1n addn0.
under [X in _ = _ + X]eq_bigr => i _ do rewrite eulerian_rec mulnDl.
rewrite big_split /=.
rewrite mul1n -addnA.
congr (_ + _).
congr (_ + _); last first.
- by apply: eq_bigr => i _; rewrite mulnCA /bump /= add1n mulnA.
rewrite [RHS]big_ord_recr /= eulerian_out_of_range ?ltnSn // muln0 mul0n addn0.
apply: eq_bigr => i _.
by rewrite /bump /= !add1n mulnCA mulnA.
Qed.

(* ========================================================================= *)
(* Closed form (Eulerian explicit formula):                                   *)
(*   eulerian n k = \sum_(j <= k) (-1)^j C(n+2, j) (k+1-j)^(n+1)  [in int]    *)
(* ========================================================================= *)

Import GRing.Theory.
Local Open Scope ring_scope.

(* Alternating binomial convolution identity.                                *)
(* \sum_j (-1)^j C(n+2, j) C(t-j, n+1) = [t == n+1]                          *)

(** Signed Pascal extension: a saturated-arithmetic-friendly form of Pascal's
    rule, valid for all [t] (including [t = 0], where [t.-1 = 0]). *)
Lemma binS' t n : 'C(t, n.+2) = 'C(t.-1, n.+2) + 'C(t.-1, n.+1).
Proof. by case: t => [|t]//=; rewrite binS. Qed.

(** Key recurrence for the alternating binomial sum: [g(N+1, u) = g(N, u.-1)].
    Proved via Pascal applied to both binomial factors plus a reindex. *)
Lemma aux_id_step (N u : nat) :
  \sum_(j < N.+4) (-1 : int) ^ j *+ 'C(N.+3, j) *+ 'C(u - j, N.+2) =
  \sum_(j < N.+3) (-1 : int) ^ j *+ 'C(N.+2, j) *+ 'C(u.-1 - j, N.+1).
Proof.
rewrite big_ord_recl [(-1) ^ ord0]expr0 bin0 mulr1n subn0.
under eq_bigr => i _ do rewrite binS mulrnDr mulrnDl.
rewrite big_split /=.
have beta_eq :
  \sum_(i < N.+3) ((-1 : int) ^ i.+1 *+ 'C(N.+2, i) *+ 'C(u - i.+1, N.+2)) =
  - \sum_(i < N.+3) ((-1 : int) ^ i *+ 'C(N.+2, i) *+ 'C(u.-1 - i, N.+2)).
  rewrite -sumrN; apply: eq_bigr => i _.
  by case: u => [|u']//=; rewrite exprSz mulN1r !mulNrn.
have alpha_eq :
  ('C(u, N.+2)%:R : int) +
  \sum_(i < N.+3) ((-1 : int) ^ i.+1 *+ 'C(N.+2, i.+1) *+ 'C(u - i.+1, N.+2)) =
  \sum_(j < N.+4) ((-1 : int) ^ j *+ 'C(N.+2, j) *+ 'C(u - j, N.+2)).
  rewrite [RHS]big_ord_recl [(-1) ^ ord0]expr0 bin0 mulr1n subn0.
  by congr (_ + _); apply: eq_bigr => i _.
rewrite addrA alpha_eq [\sum_(j < N.+4) _]big_ord_recr /= bin_small //.
rewrite mul0rn addr0 beta_eq.
rewrite -[_ + - _]/(_ - _) -sumrB; apply: eq_bigr => i _.
have aux v : ((v - i).-1 = v.-1 - i)%N by case: v => [|v']//=; rewrite -subnS.
by rewrite (binS' (u - i) N) (aux u) mulrnDr addrAC subrr add0r.
Qed.

(** Alternating binomial convolution identity:
    [sum_j (-1)^j C(n+2, j) C(t-j, n+1) = [t == n+1]].
    Used in the inversion step of [eulerian_explicit]. *)
Lemma aux_id (n t : nat) :
  \sum_(j < n.+3) (-1) ^ j *+ 'C(n.+2, j) *+ 'C(t - j, n.+1) =
  (t == n.+1)%:Z.
Proof.
elim: n t => [|n IH] t; last by rewrite aux_id_step IH; case: t.
under eq_bigr => j _ do rewrite bin1.
transitivity ((t - 0)%:R + (-1 : int) *+ (2 * (t - 1)) + (t - 2)%N%:R : int).
  rewrite 3!big_ord_recl big_ord0 addr0 -!exprnP /=.
  by rewrite expr0 !exprS expr0 mulr1 mulrN1 opprK !mulr1n
             -mulrnA addrA (mulnC 2).
rewrite subn0; case: t => [|[|[|t]]] /=.
- by rewrite !muln0 !mulr0n !add0r.
- by rewrite !muln0 !mulr0n addr0.
- rewrite !muln1 !mulr0n addr0.
  have -> : (-1 : int) *+ 2 = -1 + -1 by rewrite mulr2n.
  have -> : (2%N)%:R = 1 + 1 :> int by rewrite (_ : (2 = 1 + 1)%N) // natrD.
  by rewrite !addrA addrK addrN.
- have -> : (2 * t.+2 = t.+3 + t.+1)%N by rewrite mul2n -addnn addSnnS addnC.
  rewrite mulrnDr !mulNrn -[(t.+3 == 1)%:Z]/(0 : int).
  by rewrite !addrA addrN add0r addNr.
Qed.

(* ------------------------------------------------------------------------- *)
(* Closed form (Eulerian explicit formula) — TODO                       *)
(* ------------------------------------------------------------------------- *)
(*                                                                            *)
(* Given aux_id, the proof of eulerian_explicit follows by Worpitzky          *)
(* inversion:                                                                 *)
(*                                                                            *)
(* RHS = sum_(j < k.+1) (-1)^j *+ C(n+2, j) *+ (k+1-j)^(n+1)                  *)
(*     = sum_j (-1)^j *+ C(n+2, j) *+ sum_m eulerian n m * C(k+1-j+m, n+1)    *)
(*       [Worpitzky at x = k+1-j]                                             *)
(*     = sum_m eulerian n m *+ K(n, k, m)                                     *)
(*       [exchange_big]                                                       *)
(*  where K(n, k, m) := sum_j (-1)^j *+ C(n+2, j) *+ C(k+1+m-j, n+1)          *)
(*                    = aux_id(n, k+1+m)  [extending sum bound]               *)
(*                    = (k+1+m == n+1)%:Z = [m == n - k]                      *)
(*     = eulerian n (n-k)%:Z                                                  *)
(*     = eulerian n k       [eulerian_symm].                                  *)

(** Eulerian explicit formula (Stanley EC1, S1.4):
    [A(n+1, k) = sum_(j <= k) (-1)^j C(n+2, j) (k+1-j)^(n+1)].
    Proved by Worpitzky inversion against [aux_id]. *)
Lemma eulerian_explicit n k :
  (eulerian n k)%:Z =
    \sum_(j < k.+1) (-1) ^ j *+ 'C(n.+2, j) *+ (k.+1 - j) ^ n.+1.
Proof.
under eq_bigr => j _ do
  rewrite -mulr_natr -mulr_natr worpitzky natr_sum big_distrr /=.
rewrite exchange_big /=.
under eq_bigr => m _.
  rewrite (eq_bigr (fun j : 'I_k.+1 => (eulerian n m)%:R *
                     ((-1) ^ j * 'C(n.+2, j)%:R * 'C(k.+1 - j + m, n.+1)%:R)));
    last by move=> j _; rewrite natrM mulrCA -!mulrA mulrCA.
  rewrite -big_distrr /=.
  rewrite (eq_bigr (fun i : 'I_k.+1 =>
    (-1 : int) ^ i *+ 'C(n.+2, i) *+ 'C(k.+1 + m - i, n.+1)));
    last by move=> i _; rewrite !mulr_natr; do 2 f_equal;
            rewrite -addnBAC // ltnW // ltn_ord.
  over.
have inner_eq : forall m, m < n.+1 ->
  \sum_(i < k.+1) (-1 : int)^i *+ 'C(n.+2, i) *+ 'C(k.+1 + m - i, n.+1) =
  (k.+1 + m == n.+1)%:Z.
  move=> m Hm; rewrite -(aux_id n (k.+1 + m)).
  pose F (i : nat) := (-1 : int)^i *+ 'C(n.+2, i) *+ 'C(k.+1 + m - i, n.+1).
  rewrite -[LHS]/(\sum_(i < k.+1) F i) -[RHS]/(\sum_(i < n.+3) F i).
  pose N := maxn k.+1 n.+3.
  rewrite (big_ord_widen N F (leq_maxl _ _)) (big_ord_widen N F (leq_maxr _ _)).
  rewrite big_mkcond [RHS]big_mkcond /=; apply: eq_bigr => i _ /=; rewrite /F.
  case Hin: (i < n.+3); case Hik: (i < k.+1) => //=.
  - rewrite (_ : 'C(k.+1 + m - i, n.+1) = 0)%N ?mulr0n //.
    apply/bin_small/(leq_ltn_trans _ Hm).
    by rewrite leq_subLR leq_add2r leqNgt Hik.
  - rewrite (_ : 'C(n.+2, i) = 0)%N ?mulr0n ?mul0rn //.
    by apply: bin_small; rewrite leqNgt Hin.
under eq_bigr => m _ do rewrite (inner_eq m (ltn_ord m)).
case: (leqP k n) => Hkn; last first.
  rewrite eulerian_out_of_range // big1 // => i _.
  rewrite (_ : (k.+1 + i == n.+1) = false) ?mulr0 //.
  apply/negbTE; rewrite neq_ltn; apply/orP; right.
  by rewrite ltnS (leq_trans Hkn) // leq_addr.
have HmO : (n - k < n.+1)%N by rewrite ltnS leq_subr.
pose m0 := Ordinal HmO.
rewrite (bigD1 m0) //= [in (k.+1 + m0 == n.+1)%N]/m0 /= addSn addnC subnK //.
rewrite eqxx mulr1.
rewrite big1 ?addr0 ?(eulerian_symm Hkn) ?natz // => i Hi.
rewrite (_ : (k.+1 + i == n.+1) = false) ?mulr0 //.
apply: contraNF Hi => /eqP H; apply/eqP/val_inj => /=.
by apply: (@addnI k.+1); rewrite [RHS]addnC addnS subnK // -H.
Qed.
