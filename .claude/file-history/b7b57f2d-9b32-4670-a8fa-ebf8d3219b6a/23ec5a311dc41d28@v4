(* Layer 2: descent set, descent number, ascent number. *)
From mathcomp Require Import all_ssreflect fingroup perm.
From mathcomp_eulerian Require Import ordinal_reindex perm_compress.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* ========================================================================= *)
(* Descent predicate and descent set                                         *)
(* ========================================================================= *)

Section Descent.
Variable n : nat.
Implicit Types (s : {perm 'I_n.+1}) (i : 'I_n).

(* A position i : 'I_n is a descent of s : {perm 'I_n.+1} if               *)
(*   s(i) > s(i+1)                                                         *)
(* (positions of s are in 'I_n.+1 = {0,...,n}; descents are between         *)
(* consecutive positions so i ranges over 'I_n).                           *)

Definition is_descent s i : bool :=
  s (widen_ord (leqnSn n) i) > s (lift ord0 i).

Definition descent_set s : {set 'I_n} := [set i | is_descent s i].

Definition des s : nat := #|descent_set s|.

Definition asc s : nat := n - des s.

Lemma is_descentE s i :
  is_descent s i = (s (widen_ord (leqnSn n) i) > s (lift ord0 i)).
Proof. by []. Qed.

Lemma mem_descent_set s i : (i \in descent_set s) = is_descent s i.
Proof. by rewrite inE. Qed.

Lemma des_le s : des s <= n.
Proof. by rewrite /des (leq_trans (max_card _)) // card_ord. Qed.

Lemma des_add_asc s : des s + asc s = n.
Proof. by rewrite /asc subnKC // des_le. Qed.

Lemma des_id : des (1 : {perm 'I_n.+1}) = 0.
Proof.
apply/eqP; rewrite cards_eq0; apply/eqP/setP => i; rewrite !inE.
by rewrite /is_descent !perm1 ltnNge /= leqW.
Qed.

End Descent.

(* ========================================================================= *)
(* Interaction with Layer 1: descents and drop_perm                          *)
(* ========================================================================= *)

Section DescentDrop.
Variable n : nat.

(* Descents at interior positions are preserved by drop_perm.                *)
(* More precisely: for σ : {perm 'I_n.+2} and i : 'I_n, the descent of       *)
(* drop_perm σ at i corresponds to the descent of σ at widen_ord i.           *)

Lemma is_descent_drop (s : {perm 'I_n.+2}) (i : 'I_n) :
  is_descent (drop_perm s) i = is_descent s (widen_ord (leqnSn _) i).
Proof.
rewrite /is_descent -(ltn_lift (s ord_max)) !lift_drop_permE.
congr (s _ < s _); apply: val_inj; exact: lift_max.
Qed.

End DescentDrop.

(* ========================================================================= *)
(* Reversal-complement symmetry                                              *)
(* ========================================================================= *)

Section DescentReverse.
Variable n : nat.
Implicit Types (s : {perm 'I_n.+1}).

Definition rev_perm_ord : {perm 'I_n.+1} := perm (@rev_ord_inj n.+1).

Lemma rev_perm_ordE (j : 'I_n.+1) : rev_perm_ord j = rev_ord j.
Proof. by rewrite permE. Qed.

Definition rev_perm s : {perm 'I_n.+1} := rev_perm_ord * s.

Lemma rev_permE s (j : 'I_n.+1) : rev_perm s j = s (rev_ord j).
Proof. by rewrite permM rev_perm_ordE. Qed.

Lemma is_descent_rev s (i : 'I_n) :
  is_descent (rev_perm s) i = ~~ is_descent s (rev_ord i).
Proof.
rewrite /is_descent !rev_permE.
have E1 : rev_ord (widen_ord (leqnSn n) i) = lift ord0 (rev_ord i).
  by apply/val_inj; rewrite /= /bump /= add1n subSn // ltn_ord.
have E2 : rev_ord (lift ord0 i) = widen_ord (leqnSn n) (rev_ord i).
  by apply/val_inj; rewrite /= /bump /= add1n.
rewrite E1 E2.
set a := widen_ord _ _; set b := lift ord0 _.
have ab_ne : a != b by rewrite -val_eqE /= /bump /= add1n neq_ltn ltnSn.
have sab : s a != s b by apply: contra ab_ne => /eqP /perm_inj ->.
by rewrite ltn_neqAle leqNgt sab /=.
Qed.

Lemma des_rev_perm s : des (rev_perm s) = n - des s.
Proof.
rewrite /des /descent_set.
have revK : involutive (@rev_ord n) by move=> x; exact: rev_ordK.
rewrite -(card_imset _ (can_inj revK)).
have -> : [set rev_ord x | x in [set i | is_descent (rev_perm s) i]]
       = ~: [set i | is_descent s i].
  apply/setP => j; rewrite !inE; apply/imsetP/idP.
  + by case=> x; rewrite inE is_descent_rev => Hx ->.
  + move=> Hj; exists (rev_ord j); first by rewrite inE is_descent_rev rev_ordK.
    by rewrite rev_ordK.
by rewrite cardsCs setCK card_ord.
Qed.

Lemma des_rev_perm_ord : des rev_perm_ord = n.
Proof. by rewrite -[rev_perm_ord]mulg1 -/(rev_perm 1) des_rev_perm des_id subn0. Qed.

End DescentReverse.
