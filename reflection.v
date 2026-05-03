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


