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

(* ========================================================================= *)
(* §E. Rank preservation                                                     *)
(* ========================================================================= *)

(* Helper: the val-image of [enum A] for A : {pred 'I_n} is strictly sorted.
   This holds because [enum 'I_n] is strictly sorted by val (= [iota 0 n]),
   and filtering preserves sortedness; map val on a uniq filter gives a
   uniq, leq-sorted, hence ltn-sorted, list.                                  *)
Lemma sorted_ltn_val_enum n (A : {pred 'I_n}) :
  sorted ltn [seq \val i | i <- enum A].
Proof.
rewrite ltn_sorted_uniq_leq.
apply/andP; split.
- by rewrite map_inj_uniq ?enum_uniq //; exact: val_inj.
- rewrite sorted_map.
  apply: (sorted_filter (leT := relpre val (@leq))); first by move=> a b c; apply: leq_trans.
  have ->: Finite.enum (fintype_ordinal__canonical__fintype_Finite n) = enum 'I_n by rewrite enumT.
  by rewrite -sorted_map val_enum_ord; exact: iota_sorted.
Qed.

(* Key monotonicity: enum_val on 'I_n preserves the strict order (via val).  *)
Lemma enum_val_ltn n (A : {pred 'I_n}) (i j : 'I_(#|A|)) :
  ((val (enum_val i)) < (val (enum_val j)))%N = ((i : nat) < (j : nat))%N.
Proof.
have Hlt := sorted_ltn_val_enum A.
have Hsz : size [seq \val k | k <- enum A] = #|A| by rewrite size_map -cardE.
have Hi : (i : nat) < size [seq \val k | k <- enum A] by rewrite Hsz; exact: ltn_ord.
have Hj : (j : nat) < size [seq \val k | k <- enum A] by rewrite Hsz; exact: ltn_ord.
have Henum : forall (k : 'I_(#|A|)),
    \val (enum_val k) = nth 0%N [seq \val k | k <- enum A] k.
  move=> k.
  rewrite /enum_val (nth_map (enum_default k)) //.
  by rewrite -cardE; exact: ltn_ord.
rewrite !Henum.
have Hleq : sorted leq [seq \val k | k <- enum A].
  by move: Hlt; rewrite ltn_sorted_uniq_leq => /andP[].
apply/idP/idP.
- move=> Hlt12.
  rewrite ltnNge; apply/negP => Hge.
  have Hge_app : nth 0%N [seq \val k | k <- enum A] j
                <= nth 0%N [seq \val k | k <- enum A] i.
    apply: (sorted_leq_nth (leT := leq) leq_trans leqnn 0%N Hleq);
      try by [rewrite inE | exact Hge].
  by rewrite leqNgt Hlt12 in Hge_app.
- move=> Hij.
  apply: (sorted_ltn_nth (leT := ltn) ltn_trans 0%N Hlt);
    by [rewrite inE | exact Hij].
Qed.

(* Specialized to ordinals: enum_rank_in is monotonic w.r.t. val.            *)
Lemma enum_rank_in_val_ltn n (A : {pred 'I_n}) (x0 : 'I_n) (Ax0 : x0 \in A)
    (a b : 'I_n) (Ha : a \in A) (Hb : b \in A) :
  ((enum_rank_in Ax0 a : nat) < (enum_rank_in Ax0 b : nat))%N
  = ((val a) < (val b))%N.
Proof.
have Ea : enum_val (enum_rank_in Ax0 a) = a by rewrite enum_rankK_in.
have Eb : enum_val (enum_rank_in Ax0 b) = b by rewrite enum_rankK_in.
have := enum_val_ltn (A := [eta A])
   (enum_rank_in Ax0 a) (enum_rank_in Ax0 b).
by rewrite Ea Eb.
Qed.

(* ------------------------------------------------------------------------- *)
(* Rank preservation for perm_left                                           *)
(* ------------------------------------------------------------------------- *)

Lemma perm_left_lt_iff n (t : {perm 'I_n.+1}) (j : 'I_n.+2)
    (x0 : 'I_n.+1) (Hx0 : x0 \in image_left t j) (i i' : 'I_j) :
  ((perm_left Hx0 i : nat) < (perm_left Hx0 i' : nat))%N
  = ((val (t (embed_left i))) < (val (t (embed_left i'))))%N.
Proof.
rewrite !perm_leftE /cast_to_j /=.
exact: (enum_rank_in_val_ltn Hx0 (mem_image_left t i) (mem_image_left t i')).
Qed.

(* ------------------------------------------------------------------------- *)
(* Rank preservation for perm_right                                          *)
(* ------------------------------------------------------------------------- *)

Lemma perm_right_lt_iff n (t : {perm 'I_n.+1}) (j : 'I_n.+2)
    (x0 : 'I_n.+1) (Hx0 : x0 \in image_right t j) (i i' : 'I_(n.+1 - j)) :
  ((perm_right Hx0 i : nat) < (perm_right Hx0 i' : nat))%N
  = ((val (t (embed_right i))) < (val (t (embed_right i'))))%N.
Proof.
rewrite !perm_rightE /cast_to_subj /=.
exact: (enum_rank_in_val_ltn Hx0 (mem_image_right t i) (mem_image_right t i')).
Qed.

(* ========================================================================= *)
(* §F. Descent-set translation                                               *)
(* ========================================================================= *)

(* For `j : 'I_n.+2` with `0 < j`, we have `j.-1 <= n`.                       *)
Lemma leqj_pred_n n (j : 'I_n.+2) : j.-1 <= n.
Proof.
have := ltn_ord j; rewrite ltnS => Hj.
by case: (j : nat) Hj => [|j'] /=.
Qed.

(* Specialized to `j = k.+1` with positive size, descent positions of         *)
(* perm_left live in 'I_k (since {perm 'I_(k.+1)}, descents in 'I_k).         *)
(* Map a descent position i : 'I_k of the left perm to position i : 'I_n     *)
(* in t (since k.+1 ≤ n.+1, hence k ≤ n).                                     *)

(* For j : 'I_n.+2 of the form Ordinal (m := k.+1) Hk, descents of perm_left  *)
(* are at positions i : 'I_k.  Equivalent statement uses the fact `k <= n`   *)
(* (from j : 'I_n.+2, k.+1 ≤ n.+1 so k ≤ n).                                  *)

Section DescentTranslate.

Variables (n : nat) (t : {perm 'I_n.+1}).

(* Left-side translation: take j of the form k.+1 ≤ n.+1.                     *)
Variables (k : nat) (Hk : k.+1 < n.+2).

Let j : 'I_n.+2 := Ordinal Hk.
Let Hkn : k <= n := Hk.

(* Embed a descent position i : 'I_k into 'I_n. *)
Definition embed_desc_left (i : 'I_k) : 'I_n := widen_ord Hkn i.

Lemma is_descent_perm_left
    (x0 : 'I_n.+1) (Hx0 : x0 \in image_left t j) (i : 'I_k) :
  is_descent (perm_left Hx0) i
  = is_descent t (embed_desc_left i).
Proof.
rewrite /is_descent.
rewrite (perm_left_lt_iff Hx0).
have E1 : embed_left (j := j) (widen_ord (leqnSn k) i)
        = widen_ord (leqnSn n) (embed_desc_left i) :> 'I_n.+1.
  by apply/val_inj.
have E2 : embed_left (j := j) (lift ord0 i)
        = lift ord0 (embed_desc_left i) :> 'I_n.+1.
  by apply/val_inj => /=; rewrite /bump leq0n.
by rewrite E1 E2.
Qed.

End DescentTranslate.

(* Right-side translation. *)
Section DescentTranslateRight.

Variables (n : nat) (t : {perm 'I_n.+1}).
Variables (j : 'I_n.+2) (Hj : j < n.+1).

(* `n.+1 - j = (n - j).+1` since j ≤ n. *)
Lemma sub_succ : (n - j).+1 = n.+1 - j.
Proof. by rewrite subSn. Qed.

(* Descent positions of perm_right live in 'I_(n.+1 - j).-1 = 'I_(n - j).
   Map via shifting and casting to 'I_n. *)

(* For i : 'I_(n - j), the descent slot in t lives at position
   `j + i` in 'I_n (since n - j ≤ n - j ... actually j + i < n since i < n-j). *)
Lemma j_plus_lt_n (i : 'I_(n - j)) : j + i < n.
Proof.
have Hi := ltn_ord i.
by rewrite -ltn_subRL.
Qed.

Definition embed_desc_right (i : 'I_(n - j)) : 'I_n := Ordinal (j_plus_lt_n i).

Lemma is_descent_perm_right
    (x0 : 'I_n.+1) (Hx0 : x0 \in image_right t j) (i : 'I_(n - j)) :
  is_descent (cast_perm (esym sub_succ) (perm_right Hx0)) i
  = is_descent t (embed_desc_right i).
Proof.
rewrite /is_descent !cast_permE.
rewrite (perm_right_lt_iff Hx0).
set ci_w : 'I_(n.+1 - j) := cast_ord _ (widen_ord _ i).
set ci_l : 'I_(n.+1 - j) := cast_ord _ (lift _ _).
have E1 : embed_right (j := j) ci_w
        = widen_ord (leqnSn n) (embed_desc_right i) :> 'I_n.+1.
  by apply/val_inj.
have E2 : embed_right (j := j) ci_l
        = lift ord0 (embed_desc_right i) :> 'I_n.+1.
  by apply/val_inj => /=; rewrite /bump leq0n /= addnS.
by rewrite E1 E2.
Qed.

End DescentTranslateRight.

(* ========================================================================= *)
(* §G. Disjointness and cover                                                *)
(* ========================================================================= *)

(* image_left and image_right are disjoint (positions are disjoint, t inj).  *)
Lemma image_left_right_disjoint n (t : {perm 'I_n.+1}) (j : 'I_n.+2) :
  [disjoint image_left t j & image_right t j].
Proof.
rewrite -setI_eq0; apply/eqP/setP => x; rewrite !inE.
apply/negbTE; apply/negP => /andP[/imsetP[il _ Hl_eq] /imsetP[ir _ Hr_eq]].
have Hl := ltn_ord il.
have Hr : (j : nat) <= j + ir by exact: leq_addr.
have Heq : embed_left il = embed_right ir.
  by apply: (@perm_inj _ t); rewrite -Hl_eq Hr_eq.
have := congr1 \val Heq => /=.
by move=> Hv; move: Hl; rewrite Hv ltnNge Hr.
Qed.

(* Their union covers everything. *)
Lemma image_left_right_cover n (t : {perm 'I_n.+1}) (j : 'I_n.+2) :
  image_left t j :|: image_right t j = [set: 'I_n.+1].
Proof.
apply/eqP; rewrite eqEcard; apply/andP; split; first by apply/subsetP => x _; rewrite inE.
rewrite cardsT card_ord cardsU.
rewrite (eqP (_ : (image_left t j :&: image_right t j == set0))).
- rewrite cards0 subn0 card_image_left card_image_right.
  by rewrite addnC subnK //; exact: leqj_n1.
- by have := image_left_right_disjoint t j; rewrite -setI_eq0.
Qed.

(* Cardinality consequence: |L| + |R| = n+1. *)
Lemma image_left_card_plus_right n (t : {perm 'I_n.+1}) (j : 'I_n.+2) :
  #|image_left t j| + #|image_right t j| = n.+1.
Proof.
by rewrite card_image_left card_image_right addnC subnK //; exact: leqj_n1.
Qed.

(* ========================================================================= *)
(* §H. Notes on Target 4 (per-position interior count) for Session C-5       *)
(* ========================================================================= *)

(* The structural infrastructure (sections D-G) provides:                    *)
(*                                                                            *)
(*   - perm_left t j Hx0 : {perm 'I_j}                                        *)
(*   - perm_right t j Hx0 : {perm 'I_(n.+1 - j)}                              *)
(*   - rank-preservation: (perm_left .. i < perm_left .. i')                 *)
(*       <-> t(embed_left i) < t(embed_left i')                              *)
(*   - is_descent_perm_left/right: descents of the sub-perms correspond      *)
(*       slot-by-slot to descents of t at the corresponding positions.       *)
(*   - image_left_right_disjoint/cover: L and R partition 'I_n.+1.           *)
(*                                                                            *)
(* What's MISSING for Target 4 (the per-position interior count):             *)
(*                                                                            *)
(* (A) A descent_set DECOMPOSITION lemma:                                     *)
(*     For interior splits (1 <= j <= n), descent_set t : {set 'I_n.+1}      *)
(*     decomposes into:                                                       *)
(*       - "left" part: descents at positions i < j-1                         *)
(*         (in bijection with descent_set (perm_left t j))                    *)
(*       - "boundary" position j-1 (where the split happens)                  *)
(*       - "right" part: descents at positions i >= j                         *)
(*         (in bijection with descent_set (perm_right t j))                   *)
(*                                                                            *)
(* (B) An INVERSE construction: given                                          *)
(*       sL : {perm 'I_j}, sR : {perm 'I_(n.+1 - j)}, and a partition         *)
(*       L ⊔ R = 'I_n.+1 with #L = j,                                         *)
(*     reconstruct a unique t : {perm 'I_n.+1} such that                       *)
(*       perm_left t j = sL  and  perm_right t j = sR  and                    *)
(*       image_left t j = L.                                                  *)
(*     Combined with (A), this gives a bijection                              *)
(*       {t | descent constraint} ≃                                           *)
(*       {(L, sL, sR) | constraints on sL and sR}                             *)
(*     which sums to a binomial * eulerA k * eulerA (n.+1 - j) closed form.   *)
(*                                                                            *)
(* (C) Then summing over j (positions of ord_max) and applying                *)
(*     descent_set_insert_max_* (from §C) gives the recurrence:               *)
(*       2 * eulerA n.+2 = sum_p binom(n.+1, p) * eulerA p * eulerA (n.+1-p) *)
(*                                                                            *)
(* ESTIMATED EFFORT for (A): 50-80 LOC.                                       *)
(* ESTIMATED EFFORT for (B): 100-150 LOC (the trickiest part - need to        *)
(*   construct t from (L, sL, sR) by setting t(i) = enum_val_of L (sL i) for  *)
(*   i < j and t(j+i) = enum_val_of R (sR i) for i >= j, then prove this is  *)
(*   the inverse of the (perm_left, perm_right, image_left) decomposition).   *)
(* ESTIMATED EFFORT for (C): 80-100 LOC.                                      *)
(*                                                                            *)
(* TOTAL Session C-5 estimate: 230-330 LOC.                                   *)
(*                                                                            *)
(* The bijection (B) is the heart of the André recurrence.  It's standard    *)
(* in Stanley but the formalization in mathcomp requires care with the       *)
(* enum_val/enum_rank machinery (which is what §E sets up).                   *)

(* ------------------------------------------------------------------------- *)
(* §H.1.  A first piece of (A): is_descent t splits by position relative j.  *)
(* ------------------------------------------------------------------------- *)

(* For positions strictly before j-1, descent of t = descent of perm_left.   *)
(* Conversely, every descent of perm_left lies in this region.               *)
(* This is just the closure-of-§F-results, packaged for Session C-5 use.    *)

(* For an interior split j = k.+1 (where k.+1 < n.+2), positions of          *)
(* descent_set t : {set 'I_n.+1} that are < k correspond to descents of      *)
(* perm_left (as widen_ord), and positions > k correspond to descents of     *)
(* perm_right (as shifted index).  Position k itself is the boundary.        *)

Section DescentSplit.

Variables (n : nat) (t : {perm 'I_n.+1}).
Variables (k : nat) (Hk : k.+1 < n.+2).

Let j : 'I_n.+2 := Ordinal Hk.
Let Hkn : k <= n := Hk.

(* "Left part" of descent_set t: positions i : 'I_n with i < k.              *)
(* These correspond bijectively (via widen_ord) to descents of perm_left.    *)
Lemma descent_left_of_t (x0 : 'I_n.+1) (Hx0 : x0 \in image_left t j)
    (i : 'I_k) :
  (widen_ord Hkn i \in descent_set t) = (i \in descent_set (perm_left Hx0)).
Proof.
rewrite !mem_descent_set.
have := is_descent_perm_left Hx0 i.
by rewrite /embed_desc_left => ->.
Qed.

End DescentSplit.

(* Right side: "Right part" of descent_set t: positions i : 'I_n with j <= i. *)
Section DescentSplitRight.

Variables (n : nat) (t : {perm 'I_n.+1}).
Variables (j : 'I_n.+2) (Hjn : j < n.+1).

Lemma descent_right_of_t (x0 : 'I_n.+1) (Hx0 : x0 \in image_right t j)
    (i : 'I_(n - j)) :
  (Ordinal (j_plus_lt_n i) \in descent_set t)
  = (i \in descent_set (cast_perm (esym (sub_succ Hjn)) (perm_right Hx0))).
Proof.
rewrite !mem_descent_set.
have := is_descent_perm_right Hjn Hx0 i.
by rewrite /embed_desc_right => ->.
Qed.

End DescentSplitRight.

(* ========================================================================= *)
(* §I.  PHASE A — descent-set decomposition (Session C-5)                    *)
(* ========================================================================= *)

(* For an interior split index `j = k.+1 : 'I_n.+2` (with `k.+1 ≤ n.+1`),    *)
(* we partition the descent set of `t : {perm 'I_n.+1}` into three pieces:   *)
(*   - left  : descents at positions < k                                     *)
(*   - boundary : the single descent at position k (if any)                  *)
(*   - right : descents at positions > k                                     *)
(* The left  piece is the widen_ord-image of `descent_set (perm_left t j)`. *)
(* The right piece is in bijection with `descent_set (perm_right t j)`.      *)

Section PhaseA.

Variables (n : nat) (t : {perm 'I_n.+1}) (k : nat) (Hk : k.+1 < n.+2).

Let j : 'I_n.+2 := Ordinal Hk.
Let Hkn : k <= n := Hk.

Definition descent_left_part : {set 'I_n} :=
  [set i : 'I_n | (val i < k) && is_descent t i].

Definition descent_boundary_part : {set 'I_n} :=
  [set i : 'I_n | (val i == k) && is_descent t i].

Definition descent_right_part : {set 'I_n} :=
  [set i : 'I_n | (val i > k) && is_descent t i].

Lemma descent_set_decomp_partition :
  descent_set t = descent_left_part :|: descent_boundary_part :|: descent_right_part.
Proof.
apply/setP => i; rewrite mem_descent_set !inE.
case Hi : (is_descent t i); rewrite ?andbT ?andbF /=.
- by case: (ltngtP (val i) k).
- by [].
Qed.

Lemma descent_left_boundary_disjoint :
  [disjoint descent_left_part & descent_boundary_part].
Proof.
rewrite -setI_eq0; apply/eqP/setP => i; rewrite !inE.
apply/negbTE/negP => /andP[/andP[Hl _] /andP[/eqP Hb _]].
by rewrite Hb ltnn in Hl.
Qed.

Lemma descent_left_right_disjoint :
  [disjoint descent_left_part & descent_right_part].
Proof.
rewrite -setI_eq0; apply/eqP/setP => i; rewrite !inE.
apply/negbTE/negP => /andP[/andP[Hl _] /andP[Hr _]].
by have := ltn_trans Hl Hr; rewrite ltnn.
Qed.

Lemma descent_boundary_right_disjoint :
  [disjoint descent_boundary_part & descent_right_part].
Proof.
rewrite -setI_eq0; apply/eqP/setP => i; rewrite !inE.
apply/negbTE/negP => /andP[/andP[/eqP Hb _] /andP[Hr _]].
by rewrite Hb ltnn in Hr.
Qed.

(* Left part = widen_ord-image of descent_set perm_left. *)
Lemma descent_left_part_image (x0 : 'I_n.+1) (Hx0 : x0 \in image_left t j) :
  descent_left_part = [set widen_ord Hkn i | i in descent_set (perm_left Hx0)].
Proof.
apply/setP => i; rewrite inE.
apply/idP/imsetP.
- case/andP => Hi_lt Hd.
  exists (Ordinal Hi_lt); last by apply/val_inj.
  rewrite mem_descent_set.
  have := is_descent_perm_left (k := k) (Hk := Hk) Hx0 (Ordinal Hi_lt).
  rewrite /embed_desc_left => ->.
  by suff -> : widen_ord (Hk : k <= n) (Ordinal Hi_lt) = i by []; apply/val_inj.
- case=> i' Hi' ->.
  have Hlt : (val (widen_ord Hkn i') < k)%N = true by rewrite /= ltn_ord.
  rewrite Hlt /=.
  rewrite mem_descent_set in Hi'.
  have Heq : widen_ord Hkn i' = embed_desc_left Hk i' :> 'I_n by apply: val_inj.
  rewrite Heq.
  by have := is_descent_perm_left (k := k) (Hk := Hk) Hx0 i'; move=> <-.
Qed.

End PhaseA.

(* Right-side analog. *)

Section PhaseARight.

Variables (n : nat) (t : {perm 'I_n.+1}) (j : 'I_n.+2) (Hjn : j < n.+1).

Definition descent_right_part_R : {set 'I_n} :=
  [set i : 'I_n | (val j <= val i) && is_descent t i].

Lemma descent_right_part_R_image (x0 : 'I_n.+1) (Hx0 : x0 \in image_right t j) :
  descent_right_part_R =
  [set Ordinal (@j_plus_lt_n n j i) |
       i in descent_set (cast_perm (esym (sub_succ Hjn)) (perm_right Hx0))].
Proof.
apply/setP => i; rewrite inE.
apply/idP/imsetP.
- case/andP => Hji Hd.
  have Hi_lt_n : val i < n by exact: ltn_ord.
  have Hr_lt : val i - val j < n - val j.
    by rewrite ltn_sub2r //; exact: leq_ltn_trans Hji Hi_lt_n.
  pose r : 'I_(n - val j) := Ordinal Hr_lt.
  exists r.
  + rewrite mem_descent_set.
    have := @is_descent_perm_right n t j Hjn x0 Hx0 r.
    rewrite /embed_desc_right => ->.
    suff -> : Ordinal (@j_plus_lt_n n j r) = i :> 'I_n by [].
    by apply: val_inj => /=; rewrite addnC subnK.
  + by apply: val_inj => /=; rewrite addnC subnK.
- case=> r Hr ->.
  have Hge : val j <= val (Ordinal (@j_plus_lt_n n j r)) by rewrite /= leq_addr.
  rewrite Hge /=.
  rewrite mem_descent_set in Hr.
  have := @is_descent_perm_right n t j Hjn x0 Hx0 r.
  move=> Heq.
  rewrite /embed_desc_right in Heq.
  by rewrite -Heq.
Qed.

End PhaseARight.

(* ========================================================================= *)
(* §J.  PHASE B — inverse construction (Session C-5)                         *)
(* ========================================================================= *)

(* Given:                                                                    *)
(*   - L : {set 'I_n.+1} with #|L| = j (a chosen "left" subset of values),   *)
(*   - sL : {perm 'I_j} (the left sub-permutation),                           *)
(*   - sR : {perm 'I_(n.+1 - j)} (the right sub-permutation),                 *)
(* construct  assemble_perm L sL sR : {perm 'I_n.+1}  whose left subword      *)
(* (positions 0..j-1) lists the elements of L according to sL's order, and    *)
(* right subword (positions j..n) lists the elements of ~:L according to sR. *)

Section PhaseB.

Variables (n : nat) (j : 'I_n.+2) (L : {set 'I_n.+1}) (HL : #|L| = j).

Lemma cardCL_eq : #|~: L| = n.+1 - j.
Proof. by rewrite cardsCs setCK card_ord HL. Qed.

Variables (sL : {perm 'I_j}) (sR : {perm 'I_(n.+1 - j)}).

Definition castL (i : 'I_j) : 'I_(#|L|) := cast_ord (esym HL) i.
Definition castR (i : 'I_(n.+1 - j)) : 'I_(#|~: L|) :=
  cast_ord (esym cardCL_eq) i.
Definition leqj : (j : nat) <= n.+1 := ltnSE (ltn_ord j).

(* Split a position i : 'I_n.+1 into a left or right index. *)
Definition split_pos (i : 'I_n.+1) : ('I_j + 'I_(n.+1 - j))%type :=
  match split (cast_ord (esym (subnKC leqj)) i) with
  | inl ileft => inl ileft
  | inr iright => inr iright
  end.

Definition assemble_fun (i : 'I_n.+1) : 'I_n.+1 :=
  match split_pos i with
  | inl iL => enum_val (castL (sL iL))
  | inr iR => enum_val (castR (sR iR))
  end.

Lemma split_pos_inj : injective split_pos.
Proof.
move=> i1 i2; rewrite /split_pos.
case: splitP => [u1 Hu1|u1 Hu1]; case: splitP => [u2 Hu2|u2 Hu2] //=.
- case=> Heq.
  apply: val_inj => /=.
  move: Hu1 Hu2 => /=.
  by move=> H1 H2; rewrite H1 H2 Heq.
- case=> Heq.
  move: Hu1 Hu2 => /= H1 H2.
  apply: val_inj => /=.
  by rewrite H1 H2 Heq.
Qed.

Lemma assemble_fun_inj : injective assemble_fun.
Proof.
move=> i1 i2; rewrite /assemble_fun.
case E1: (split_pos i1) => [u1|u1]; case E2: (split_pos i2) => [u2|u2].
- move/enum_val_inj/cast_ord_inj/perm_inj => Hu.
  apply: split_pos_inj.
  by rewrite E1 E2 Hu.
- move=> Hcontra.
  have HinL : enum_val (castL (sL u1)) \in L by exact: enum_valP.
  have HinR : enum_val (castR (sR u2)) \in ~: L by exact: enum_valP.
  rewrite Hcontra in HinL.
  by rewrite inE HinL in HinR.
- move=> Hcontra.
  have HinR : enum_val (castR (sR u1)) \in ~: L by exact: enum_valP.
  have HinL : enum_val (castL (sL u2)) \in L by exact: enum_valP.
  rewrite Hcontra in HinR.
  by rewrite inE HinL in HinR.
- move/enum_val_inj/cast_ord_inj/perm_inj => Hu.
  apply: split_pos_inj.
  by rewrite E1 E2 Hu.
Qed.

Definition assemble_perm : {perm 'I_n.+1} := perm assemble_fun_inj.

Lemma assemble_permE i : assemble_perm i = assemble_fun i.
Proof. by rewrite permE. Qed.

End PhaseB.

(* ------------------------------------------------------------------------- *)
(* §J.1.  Round-trip lemmas for assemble_perm                                *)
(* ------------------------------------------------------------------------- *)

Section AssembleRoundTrip.

Variables (n : nat) (j : 'I_n.+2) (L : {set 'I_n.+1}) (HL : #|L| = j).
Variables (sL : {perm 'I_j}) (sR : {perm 'I_(n.+1 - j)}).

Let t := assemble_perm HL sL sR.

(* Action on left positions. *)
Lemma assemble_left (i : 'I_j) :
  t (embed_left (j := j) i) = enum_val (castL HL (sL i)).
Proof.
rewrite /t assemble_permE /assemble_fun /split_pos.
case: splitP => [u Hu|u Hu] /=.
- congr enum_val; congr castL; congr (sL _).
  apply: val_inj => /=.
  by move: Hu => /= ->.
- exfalso.
  move: Hu => /=.
  rewrite /embed_left /=.
  move=> Heq.
  have Hi : (i : nat) < j by exact: ltn_ord.
  have : j <= i by rewrite Heq leq_addr.
  by rewrite leqNgt Hi.
Qed.

(* Action on right positions. *)
Lemma assemble_right (i : 'I_(n.+1 - j)) :
  t (embed_right (j := j) i) = enum_val (castR HL (sR i)).
Proof.
rewrite /t assemble_permE /assemble_fun /split_pos.
case: splitP => [u Hu|u Hu] /=.
- exfalso.
  move: Hu => /=.
  rewrite /embed_right /=.
  move=> Heq.
  have Hu' : (u : nat) < j by exact: ltn_ord.
  have : j <= u by rewrite -Heq leq_addr.
  by rewrite leqNgt Hu'.
- congr enum_val; congr castR; congr (sR _).
  apply: val_inj => /=.
  move: Hu => /=.
  rewrite /embed_right /= => Heq.
  by have := addnI Heq.
Qed.

(* image_left of the assembled perm equals the chosen subset L. *)
Lemma assemble_image_left : image_left t j = L.
Proof.
apply/setP => x.
apply/imsetP/idP.
- case=> i _ ->.
  rewrite assemble_left.
  exact: enum_valP.
- move=> HxL.
  pose i_card : 'I_(#|L|) := enum_rank_in HxL x.
  pose i_jj : 'I_j := cast_ord HL i_card.
  pose i_pre : 'I_j := (sL^-1)%g i_jj.
  exists i_pre => //.
  rewrite assemble_left.
  by rewrite /castL /i_pre permKV /i_jj cast_ordK enum_rankK_in.
Qed.

(* Symmetric: image_right of the assembled perm equals ~: L. *)
Lemma assemble_image_right : image_right t j = ~: L.
Proof.
apply/setP => x.
apply/imsetP/idP.
- case=> i _ ->.
  rewrite assemble_right.
  exact: enum_valP.
- move=> HxNL.
  pose i_card : 'I_(#|~: L|) := enum_rank_in HxNL x.
  pose i_jj : 'I_(n.+1 - j) := cast_ord (cardCL_eq HL) i_card.
  pose i_pre : 'I_(n.+1 - j) := (sR^-1)%g i_jj.
  exists i_pre => //.
  rewrite assemble_right.
  by rewrite /castR /i_pre permKV /i_jj cast_ordK enum_rankK_in.
Qed.

End AssembleRoundTrip.

(* ------------------------------------------------------------------------- *)
(* §J.2.  perm_left / perm_right round-trip                                  *)
(* ------------------------------------------------------------------------- *)

Section AssemblePermLeftRT.

Variables (n : nat) (j : 'I_n.+2) (L : {set 'I_n.+1}) (HL : #|L| = j).
Variables (sL : {perm 'I_j}) (sR : {perm 'I_(n.+1 - j)}).
Let t := assemble_perm HL sL sR.

(* Round-trip: perm_left of the assembled perm recovers sL. *)
Lemma assemble_perm_left (x0 : 'I_n.+1) (Hx0 : x0 \in image_left t j) :
  perm_left Hx0 = sL.
Proof.
apply/permP => i.
rewrite perm_leftE.
rewrite assemble_left.
have HL' : image_left t j = L := assemble_image_left HL sL sR.
have HmemImg : enum_val (castL HL (sL i)) \in image_left t j
  by rewrite HL'; exact: enum_valP.
apply: val_inj => /=.
have Henum : enum (image_left t j) = enum L by rewrite HL'.
have HuniqL : uniq (enum L) by exact: enum_uniq.
pose v := enum_val (castL HL (sL i)).
have Hv_in : v \in enum L by rewrite mem_enum; exact: enum_valP.
have Hidx : index v (enum L) = sL i.
  have Hv_nth : v = nth (enum_default (castL HL (sL i))) (enum L) (sL i).
    by rewrite /v (enum_val_nth (enum_default (castL HL (sL i)))).
  rewrite Hv_nth index_uniq //.
  have : (sL i : nat) < #|L| by rewrite HL; exact: ltn_ord.
  by rewrite cardE.
rewrite (unlock unlockable_enum_rank_in) /=.
rewrite Henum Hidx.
have HsL_card : (sL i : nat) < #|image_left t j|
  by rewrite card_image_left; exact: ltn_ord.
rewrite insubdK; first by [].
exact: HsL_card.
Qed.

(* Round-trip: perm_right of the assembled perm recovers sR. *)
Lemma assemble_perm_right (x0 : 'I_n.+1) (Hx0 : x0 \in image_right t j) :
  perm_right Hx0 = sR.
Proof.
apply/permP => i.
rewrite perm_rightE.
rewrite assemble_right.
have HR' : image_right t j = ~: L := assemble_image_right HL sL sR.
have HmemImg : enum_val (castR HL (sR i)) \in image_right t j
  by rewrite HR'; exact: enum_valP.
apply: val_inj => /=.
have Henum : enum (image_right t j) = enum (~: L) by rewrite HR'.
have HuniqR : uniq (enum (~: L)) by exact: enum_uniq.
pose v := enum_val (castR HL (sR i)).
have Hv_in : v \in enum (~: L) by rewrite mem_enum; exact: enum_valP.
have Hidx : index v (enum (~: L)) = sR i.
  have Hv_nth : v = nth (enum_default (castR HL (sR i))) (enum (~: L)) (sR i).
    by rewrite /v (enum_val_nth (enum_default (castR HL (sR i)))).
  rewrite Hv_nth index_uniq //.
  have : (sR i : nat) < #|~: L| by rewrite (cardCL_eq HL); exact: ltn_ord.
  by rewrite cardE.
rewrite (unlock unlockable_enum_rank_in) /=.
rewrite Henum Hidx.
have HsR_card : (sR i : nat) < #|image_right t j|
  by rewrite card_image_right; exact: ltn_ord.
rewrite insubdK; first by [].
exact: HsR_card.
Qed.

End AssemblePermLeftRT.

(* ------------------------------------------------------------------------- *)
(* §J.3.  Forward round-trip: assemble ∘ decompose = id                       *)
(* ------------------------------------------------------------------------- *)

(* For the full bijection, we also need: starting from any t : {perm 'I_n.+1} *)
(* and j : 'I_n.+2, decomposing into (image_left t j, perm_left t, perm_right *)
(* t) and re-assembling recovers t.                                           *)
(* The LEFT half of this is straightforward.  The RIGHT half requires showing *)
(* image_right t j = ~: image_left t j (an obvious consequence of the         *)
(* disjoint/cover lemmas) and then chasing casts between the two              *)
(* cardinalities (n.+1 - j and #|~: image_left t j|).                         *)

(* The cardinality of image_left t j is j (already proven).  Repackaged here  *)
(* as the HL hypothesis assemble_perm needs:                                  *)
Section AssembleForwardLeft.
Variables (n : nat) (t : {perm 'I_n.+1}) (j : 'I_n.+2).

Definition card_image_left_eq : #|image_left t j| = j := card_image_left t j.

Variables (x0L : 'I_n.+1) (Hx0L : x0L \in image_left t j).
Variables (x0R : 'I_n.+1) (Hx0R : x0R \in image_right t j).

(* On left positions, the assembled perm reproduces t. *)
Lemma assemble_decomp_inverse_left (i : 'I_j) :
  assemble_perm card_image_left_eq (perm_left Hx0L) (perm_right Hx0R)
                (embed_left i) = t (embed_left i).
Proof.
rewrite assemble_left perm_leftE /cast_to_j /castL.
rewrite cast_ord_comp.
have Hetrans : etrans (card_image_left t j)
                (esym card_image_left_eq) = erefl _.
  exact: eq_irrelevance.
rewrite Hetrans cast_ord_id.
by rewrite enum_rankK_in //; exact: mem_image_left.
Qed.

End AssembleForwardLeft.

(* ========================================================================= *)
(* §K.  STATUS NOTE — what remains for euler_rec (Session C-6+)              *)
(* ========================================================================= *)

(* Phase A (descent-set decomposition): COMPLETE.                            *)
(*   - descent_set_decomp_partition: descent_set t = L ∪ B ∪ R               *)
(*   - descent_left/boundary/right_disjoint: pieces are pairwise disjoint    *)
(*   - descent_left_part_image: L is widen_ord-image of descent_set perm_left *)
(*   - descent_right_part_R_image: R is shifted-image of descent_set         *)
(*       perm_right                                                          *)
(*                                                                            *)
(* Phase B (inverse construction): MOSTLY COMPLETE.                          *)
(*   - assemble_perm L sL sR : {perm 'I_n.+1} defined and is a permutation.  *)
(*   - assemble_left/right: action on left/right positions characterized.     *)
(*   - assemble_image_left/right: image_left/right of assembled perm = L/~:L. *)
(*   - assemble_perm_left/right: perm_left/right of assembled perm = sL/sR.   *)
(*   - assemble_decomp_inverse_left: forward round-trip on left positions.    *)
(*                                                                            *)
(* MISSING for Phase B:                                                      *)
(*   - assemble_decomp_inverse (full): assemble (image_left t j)              *)
(*       (perm_left t j) (perm_right t j) = t.                                *)
(*     The right-side case needs to chase a cast between #|image_right t j|   *)
(*     and #|~: image_left t j| (these are equal but require image_right t j  *)
(*     = ~: image_left t j to identify).  Estimated ~30 LOC.                  *)
(*                                                                            *)
(* Phase C (assembly into euler_rec): NOT STARTED.                            *)
(*   The recurrence statement                                                 *)
(*     2 * eulerA n.+2 = \sum_(k < n.+2)                                      *)
(*                          'C(n.+1, k) * eulerA k * eulerA (n.+1 - k)        *)
(*   requires:                                                                *)
(*   (a) Express beta (alt_desc_set n.+2) as a sum over j of inserting        *)
(*       ord_max at position j (using insert_max_perm_bij from eulerian.v).   *)
(*   (b) Use descent_set_insert_max_* (from §C) to translate the alt_desc_set *)
(*       n.+2 condition into conditions on the smaller perm t.                *)
(*   (c) Use descent_set_decomp_partition (Phase A) and assemble_decomp       *)
(*       (Phase B) to express the per-j count as a sum over (L, sL, sR).      *)
(*   (d) Compute: choices for L are 'C(n.+1, k); valid sL are eulerA k;       *)
(*       valid sR are eulerA (n.+1 - k); product gives the recurrence summand. *)
(*   (e) The factor of 2 on LHS comes from beta_compl: beta (alt) =           *)
(*       beta (~: alt), summing the two flavours.                             *)
(*   Estimated 150-200 LOC.                                                   *)


