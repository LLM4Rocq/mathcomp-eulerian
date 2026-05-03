(* Layer 6 (Phase C): André's reflection method for Euler numbers.            *)
(*                                                                            *)
(* Stanley EC1 §1.6.4.                                                        *)
(*                                                                            *)
(* This file lands the definitions of Euler numbers via the alternating       *)
(* descent set and the trivial base cases.  The substantive recurrence        *)
(*                                                                            *)
(*    2 * eulerA n.+2 = \sum_(k < n.+2) 'C(n.+1, k) * eulerA k * eulerA (n.+1 - k) *)
(*                                                                            *)
(* is left for sessions C-2 through C-5.                                      *)

From mathcomp Require Import all_ssreflect fingroup perm.
From mathcomp_eulerian Require Import ordinal_reindex perm_compress
                                       descent eulerian beta beta_omega
                                       beta_swap.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* ========================================================================= *)
(* §A. Definitions                                                           *)
(* ========================================================================= *)

(* euler n = number of permutations of 'I_n.+1 with descent set equal to     *)
(* alt_desc_set n = {0, 2, 4, ...}.  In Stanley's notation this is A_{n+1}: *)
(* the count of down-up alternating permutations of length n+1.              *)
Definition euler (n : nat) : nat := beta (alt_desc_set n).

(* eulerA n = A_n in Stanley's notation, with the convention                  *)
(* A_0 := 1 (empty alternating permutation).                                  *)
Definition eulerA (n : nat) : nat :=
  if n is k.+1 then euler k else 1.

(* ========================================================================= *)
(* §B. Trivial base cases                                                    *)
(* ========================================================================= *)

Lemma eulerA_0 : eulerA 0 = 1.
Proof. by []. Qed.

(* alt_desc_set 0 = set0 since 'I_0 is empty.                                *)
Lemma alt_desc_set_0 : alt_desc_set 0 = set0.
Proof. by apply/setP; case; case. Qed.

(* euler 0 counts perms of 'I_1 with descent_set = set0; only id qualifies. *)
Lemma euler_0 : euler 0 = 1.
Proof. by rewrite /euler alt_desc_set_0 beta0. Qed.

Lemma eulerA_1 : eulerA 1 = 1.
Proof. by rewrite /eulerA euler_0. Qed.

(* alt_desc_set 1 = [set: 'I_1] since the unique element of 'I_1 has         *)
(* val 0 and ~~ odd 0 is true.                                               *)
Lemma alt_desc_set_1 : alt_desc_set 1 = [set: 'I_1].
Proof.
apply/setP => i; rewrite mem_alt_desc_set inE.
by have /eqP -> : val i == 0%N by rewrite -leqn0 -ltnS ltn_ord.
Qed.

(* euler 1 = beta (alt_desc_set 1) = beta setT = 1 (only [1;0] in S_2).      *)
Lemma euler_1 : euler 1 = 1.
Proof. by rewrite /euler alt_desc_set_1 beta_full. Qed.

Lemma eulerA_2 : eulerA 2 = 1.
Proof. by rewrite /eulerA euler_1. Qed.

(* ========================================================================= *)
(* §C. descent_set under insert_max_perm                                     *)
(* ========================================================================= *)

(* These lemmas refine the existing [des_insert_max_*] (which give descent   *)
(* COUNT changes) into descent SET characterizations.  They are proved by    *)
(* the same case analysis as the count versions in eulerian.v.               *)

(* Inserting ord_max at position 0: a forced descent appears at slot 0,     *)
(* and old descents shift up by one (slot k of t becomes slot k+1).         *)
Lemma descent_set_insert_max_ord0 n (t : {perm 'I_n.+1}) :
  descent_set (insert_max_perm t (ord0 : 'I_n.+2))
  = (ord0 : 'I_n.+1) |: [set lift ord0 j | j in descent_set t].
Proof.
rewrite /descent_set; apply/setP => i; rewrite !inE.
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

(* Inserting ord_max at position ord_max (= n.+1): no new descent created;  *)
(* old descents at slot k stay at slot k (no shift, since we use lift       *)
(* ord_max to embed 'I_n.+1 into 'I_n.+2 by widening).                     *)
Lemma descent_set_insert_max_ord_max n (t : {perm 'I_n.+1}) :
  descent_set (insert_max_perm t (ord_max : 'I_n.+2))
  = [set (lift ord_max j : 'I_n.+1) | j in descent_set t].
Proof.
rewrite /descent_set; apply/setP => i; rewrite !inE.
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
    have H3 : (n.+1 <= j.+1) = false by apply/negbTE; rewrite -ltnNge; apply: ltn_ord.
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
  + case=> j' _ /eqP; rewrite -val_eqE /= /bump /= leqNgt ltn_ord /= => /eqP eqn.
    rewrite add0n in eqn.
    by move: (ltn_ord j'); rewrite -eqn ltnn.
Qed.

(* Interior insertion at position p = lift ord0 (widen_ord _ j) where        *)
(* j : 'I_n.  In one-line notation, this places ord_max at slot p (which    *)
(* equals j.+1).  The descent set is the [lift h]-image of                  *)
(*    descent_set t  ∪  {j}                                                  *)
(* where h = widen_ord (leqnSn n) j.  Intuition:                             *)
(*  - slots strictly below j: inherited from t (no shift).                   *)
(*  - slot j: forced ASCENT (going INTO ord_max), so slot val j of the new  *)
(*    perm — here represented as lift h applied to the [ord0..j-1]-part —   *)
(*    is NOT a descent.                                                      *)
(*  - slot j.+1 = val p: forced DESCENT (going OUT OF ord_max).             *)
(*  - slots strictly above j.+1: inherited from t at slots > j (shifted     *)
(*    up by one).                                                            *)
(* The clean statement uses lift h to package both shifts uniformly.        *)
Lemma descent_set_insert_max_interior n (t : {perm 'I_n.+1}) (j : 'I_n) :
  let h := widen_ord (leqnSn n) j in
  descent_set (insert_max_perm t (lift ord0 h))
  = [set lift h x | x in descent_set t :|: [set j]].
Proof.
move=> h; set p := lift ord0 h; set sigma := insert_max_perm t p.
rewrite /descent_set; apply/setP => i; rewrite !inE.
case: (unliftP h i) => [x ->|->].
- have sigma_lift0 : forall y : 'I_n,
    sigma (lift ord0 (lift h y)) = widen_ord (leqnSn n.+1) (t (lift ord0 y)).
    move=> y.
    have E : lift ord0 (lift h y) = lift p (lift ord0 y) :> 'I_n.+2.
      by apply/val_inj => /=; rewrite /p /=; rewrite /bump /= addnCA.
    by rewrite /sigma E insert_max_perm_lift.
  have -> : (lift h x \in [set lift h x0 | x0 in descent_set t :|: [set j]])
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
    have E : widen_ord (leqnSn n.+1) (lift h x) = lift p (widen_ord (leqnSn n) x) :> 'I_n.+2.
      apply/val_inj; rewrite /= /p /= /bump /=.
      case: (ltngtP x j) => [Hxj|Hxj|Hxj].
      - by [].
      - by [].
      - by rewrite -val_eqE /= Hxj eqxx in xnj.
    by rewrite /sigma E insert_max_perm_lift.
- have Rfalse : (h \in [set lift h x | x in descent_set t :|: [set j]]) = false.
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

(* ========================================================================= *)
(* §D. Sub-permutation lift infrastructure                                   *)
(* ========================================================================= *)

(* Setup for the André reflection bijection.  Given a perm                    *)
(*    σ : 'I_{n.+1} → 'I_{n.+1}                                               *)
(* and a "split point" j : 'I_{n.+2} (with j ≤ n.+1), we want to view the     *)
(* left subword σ(0), ..., σ(j-1) as a permutation of its image set L ⊂ 'I_n.+1*)
(* canonically isomorphic to {perm 'I_j} via "rank in sorted order of L".     *)
(*                                                                            *)
(* The basic ingredients (mathcomp's enum_val/enum_rank_in) give an           *)
(* `'I_(#|L|) ↔ L` bijection.  We need to pre-compose with widening           *)
(* `'I_j ↪ 'I_(n.+1)`, then with σ, then with the rank into L.                *)

(* Generic widening injectivity. *)
Lemma widen_inj n m (h : n <= m) : injective (widen_ord h).
Proof. by move=> i j /(congr1 val) /=; exact: val_inj. Qed.

Section ImageLeft.

Variables (n : nat) (t : {perm 'I_n.+1}) (j : 'I_n.+2).

(* Coercion j : 'I_n.+2 → j ≤ n.+1 (the slot count for the left subword). *)
Definition leqj_n1 : (j : nat) <= n.+1 := ltnSE (ltn_ord j).

(* Embed positions 0..j-1 into 'I_n.+1. *)
Definition embed_left (i : 'I_j) : 'I_n.+1 := widen_ord leqj_n1 i.

Lemma embed_left_inj : injective embed_left.
Proof. exact: widen_inj. Qed.

(* The image set: { t(i) | i ∈ [0..j-1] }, as a {set 'I_n.+1}. *)
Definition image_left : {set 'I_n.+1} :=
  [set t (embed_left i) | i : 'I_j].

Lemma t_embed_inj : injective (fun i : 'I_j => t (embed_left i)).
Proof. by apply: inj_comp; [exact: perm_inj | exact: embed_left_inj]. Qed.

Lemma card_image_left : #|image_left| = j.
Proof.
by rewrite /image_left -[RHS](card_ord j) -(card_imset _ t_embed_inj).
Qed.

(* Each left-image of t lies in image_left.  Useful for enum_rank_in. *)
Lemma mem_image_left (i : 'I_j) : t (embed_left i) \in image_left.
Proof. by apply/imsetP; exists i. Qed.

End ImageLeft.

(* ------------------------------------------------------------------------- *)
(* The lifted left sub-permutation                                          *)
(* ------------------------------------------------------------------------- *)

(* Given a default witness `x0 ∈ S`, the rank function `enum_rank_in Hx0`     *)
(* sends elements of `S ⊂ 'I_n.+1` bijectively onto `'I_(#|S|)`.              *)
(*                                                                            *)
(* For our use case `S = image_left t j`, we have `#|S| = j` and a            *)
(* witness `t (embed_left i)` for any `i : 'I_j` (provided j > 0).            *)
(*                                                                            *)
(* The composition                                                            *)
(*    'I_j  --embed_left-->  'I_n.+1  --t-->  image_left  --enum_rank_in-->  'I_(#|image_left|) *)
(* gives, after transporting along card_image_left : #|image_left| = j,       *)
(* a function 'I_j → 'I_j which is a bijection (i.e. a permutation).         *)

Section PermOfLeft.

Variables (n : nat) (t : {perm 'I_n.+1}) (j : 'I_n.+2).

(* The rank-into-L map, parameterized by a witness. *)
Definition rank_left (x0 : 'I_n.+1)
    (Hx0 : x0 \in image_left t j) (y : 'I_n.+1) : 'I_(#|image_left t j|) :=
  enum_rank_in Hx0 y.

(* Cast to 'I_j using card_image_left. *)
Definition cast_to_j (k : 'I_(#|image_left t j|)) : 'I_j :=
  cast_ord (card_image_left t j) k.

Lemma cast_to_j_inj : injective cast_to_j.
Proof. by move=> a b /cast_ord_inj. Qed.

(* The full forward map 'I_j → 'I_j (parameterized by a witness). *)
Definition perm_left_fun (x0 : 'I_n.+1)
    (Hx0 : x0 \in image_left t j) (i : 'I_j) : 'I_j :=
  cast_to_j (enum_rank_in Hx0 (t (embed_left i))).

Lemma perm_left_fun_inj (x0 : 'I_n.+1) (Hx0 : x0 \in image_left t j) :
  injective (perm_left_fun Hx0).
Proof.
move=> i1 i2; rewrite /perm_left_fun => /cast_to_j_inj.
move=> /(congr1 (@enum_val _ _)).
rewrite !enum_rankK_in; try exact: mem_image_left.
by move/perm_inj/embed_left_inj.
Qed.

Definition perm_left (x0 : 'I_n.+1) (Hx0 : x0 \in image_left t j)
  : {perm 'I_j} := perm (@perm_left_fun_inj x0 Hx0).

Lemma perm_leftE (x0 : 'I_n.+1) (Hx0 : x0 \in image_left t j) (i : 'I_j) :
  perm_left Hx0 i = cast_to_j (enum_rank_in Hx0 (t (embed_left i))).
Proof. by rewrite permE. Qed.

(* The key identity: applying enum_val recovers t(embed_left i). *)
Lemma enum_val_perm_left (x0 : 'I_n.+1) (Hx0 : x0 \in image_left t j) (i : 'I_j) :
  enum_val (cast_ord (esym (card_image_left t j)) (perm_left Hx0 i))
  = t (embed_left i).
Proof.
rewrite perm_leftE /cast_to_j cast_ordK.
by rewrite enum_rankK_in //; exact: mem_image_left.
Qed.

End PermOfLeft.

(* ------------------------------------------------------------------------- *)
(* Independence of the witness x0                                            *)
(* ------------------------------------------------------------------------- *)

(* enum_rank_in does not depend on the witness when both witnesses are in S. *)
Lemma perm_left_witness_indep n (t : {perm 'I_n.+1}) (j : 'I_n.+2)
    (x0 y0 : 'I_n.+1)
    (Hx0 : x0 \in image_left t j) (Hy0 : y0 \in image_left t j) :
  perm_left Hx0 = perm_left Hy0.
Proof.
apply/permP => i; rewrite !perm_leftE /cast_to_j; congr cast_ord.
by apply: eq_enum_rank_in (mem_image_left t i).
Qed.

(* ------------------------------------------------------------------------- *)
(* Default-witness packaging: when j > 0 we always have a witness.          *)
(* ------------------------------------------------------------------------- *)

(* When j > 0, position 0 : 'I_j gives us a canonical element of image_left. *)
Lemma image_left_witness_pos n (t : {perm 'I_n.+1}) (j : 'I_n.+2) (Hj : 0 < j) :
  t (embed_left (j := j) (Ordinal Hj)) \in image_left t j.
Proof. exact: mem_image_left. Qed.

(* ------------------------------------------------------------------------- *)
(* Right side: image_right and corresponding sub-perm                         *)
(* ------------------------------------------------------------------------- *)

(* For a perm t : {perm 'I_n.+1} and slot j : 'I_n.+2, the right subword     *)
(* covers positions [j .. n] (length n.+1 - j).  We embed via rshift         *)
(* j + i and a cast.                                                         *)

Section ImageRight.

Variables (n : nat) (t : {perm 'I_n.+1}) (j : 'I_n.+2).

Definition embed_right (i : 'I_(n.+1 - j)) : 'I_n.+1 :=
  cast_ord (subnKC (leqj_n1 j)) (rshift j i).

Lemma embed_right_inj : injective embed_right.
Proof.
move=> i1 i2 /(congr1 (cast_ord (esym (subnKC (leqj_n1 j))))).
rewrite !cast_ordK; exact: rshift_inj.
Qed.

Definition image_right : {set 'I_n.+1} :=
  [set t (embed_right i) | i : 'I_(n.+1 - j)].

Lemma t_embed_right_inj : injective (fun i : 'I_(n.+1 - j) => t (embed_right i)).
Proof. by apply: inj_comp; [exact: perm_inj | exact: embed_right_inj]. Qed.

Lemma card_image_right : #|image_right| = n.+1 - j.
Proof.
by rewrite /image_right -[RHS](card_ord (n.+1 - j)) -(card_imset _ t_embed_right_inj).
Qed.

Lemma mem_image_right (i : 'I_(n.+1 - j)) : t (embed_right i) \in image_right.
Proof. by apply/imsetP; exists i. Qed.

End ImageRight.

(* ------------------------------------------------------------------------- *)
(* The lifted right sub-permutation                                          *)
(* ------------------------------------------------------------------------- *)

Section PermOfRight.

Variables (n : nat) (t : {perm 'I_n.+1}) (j : 'I_n.+2).

Definition cast_to_subj (k : 'I_(#|image_right t j|)) : 'I_(n.+1 - j) :=
  cast_ord (card_image_right t j) k.

Lemma cast_to_subj_inj : injective cast_to_subj.
Proof. by move=> a b /cast_ord_inj. Qed.

Definition perm_right_fun (x0 : 'I_n.+1)
    (Hx0 : x0 \in image_right t j) (i : 'I_(n.+1 - j)) : 'I_(n.+1 - j) :=
  cast_to_subj (enum_rank_in Hx0 (t (embed_right i))).

Lemma perm_right_fun_inj (x0 : 'I_n.+1) (Hx0 : x0 \in image_right t j) :
  injective (perm_right_fun Hx0).
Proof.
move=> i1 i2; rewrite /perm_right_fun => /cast_to_subj_inj.
move=> /(congr1 (@enum_val _ _)).
rewrite !enum_rankK_in; try exact: mem_image_right.
by move/perm_inj/embed_right_inj.
Qed.

Definition perm_right (x0 : 'I_n.+1) (Hx0 : x0 \in image_right t j)
  : {perm 'I_(n.+1 - j)} := perm (@perm_right_fun_inj x0 Hx0).

Lemma perm_rightE (x0 : 'I_n.+1) (Hx0 : x0 \in image_right t j)
    (i : 'I_(n.+1 - j)) :
  perm_right Hx0 i = cast_to_subj (enum_rank_in Hx0 (t (embed_right i))).
Proof. by rewrite permE. Qed.

Lemma enum_val_perm_right (x0 : 'I_n.+1) (Hx0 : x0 \in image_right t j)
    (i : 'I_(n.+1 - j)) :
  enum_val (cast_ord (esym (card_image_right t j)) (perm_right Hx0 i))
  = t (embed_right i).
Proof.
rewrite perm_rightE /cast_to_subj cast_ordK.
by rewrite enum_rankK_in //; exact: mem_image_right.
Qed.

End PermOfRight.

Lemma perm_right_witness_indep n (t : {perm 'I_n.+1}) (j : 'I_n.+2)
    (x0 y0 : 'I_n.+1)
    (Hx0 : x0 \in image_right t j) (Hy0 : y0 \in image_right t j) :
  perm_right Hx0 = perm_right Hy0.
Proof.
apply/permP => i; rewrite !perm_rightE /cast_to_subj; congr cast_ord.
by apply: eq_enum_rank_in (mem_image_right t i).
Qed.


