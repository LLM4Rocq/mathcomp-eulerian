(* The q-Eulerian (maj, des) insertion recurrence (Carlitz):                 *)
(*                                                                            *)
(*   B(n+1, k+1) = [k+2]_q B(n, k+1) + q^(k+1) [n+1-k]_q B(n, k)              *)
(*                                                                            *)
(* where B(n, k) = q_eulerian n k = \sum_(des sigma = k) q^(maj sigma) over   *)
(* sigma in S_{n+1}.  This is the numerator engine of Carlitz's q-analogue    *)
(* of Stanley §1.4 (phase 4 part 2 of docs/plans/FPS_PLAN.md).                *)
(*                                                                            *)
(* Method: the insert-max bijection (eulerian.v).  The descent-SET lemmas     *)
(* descent_set_insert_max_{ord0, interior, ord_max} (reflection.v) determine  *)
(* maj of an insertion exactly (maj is the sum of descent positions):         *)
(*   - at the front: maj increases by des + 1;                                *)
(*   - at the end: maj unchanged;                                             *)
(*   - in the gap after slot j: maj increases by c_j + 1 (+ j+1 if the gap    *)
(*     is an ascent), where c_j counts descents above j.                      *)
(* Summing q^increment over the descent gaps (resp. ascent gaps) produces     *)
(* the q-integers via the rank bijection [sum_rank_lt / sum_rank_gt]:         *)
(* ranking a subset of 'I_n by its order gives exponents 0, ..., #|E|-1.      *)
(*                                                                            *)
(* This file is AXIOM-FREE (combinatorial core).                              *)

From mathcomp Require Import all_ssreflect all_algebra fingroup perm.
From mathcomp_eulerian Require Import ordinal_reindex perm_compress descent.
From mathcomp_eulerian Require Import eulerian beta beta_omega beta_swap.
From mathcomp_eulerian Require Import reflection inversions qfact qeul.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.

(* ========================================================================= *)
(* §A. Rank sums: ordering a subset of 'I_m yields q-integers                 *)
(* ========================================================================= *)

Lemma card_ord_ltb (m b : nat) : (b <= m)%N ->
  #|[set x : 'I_m | (x < b)%N]| = b.
Proof.
move=> le_bm.
rewrite -[RHS](card_ord b) -(card_imset _ (@widen_inj b m le_bm)).
congr #|pred_of_set _|; apply/setP => x; rewrite !inE.
apply/idP/imsetP.
- by move=> lt_xb; exists (Ordinal lt_xb) => //; apply/val_inj.
- by case=> i _ ->; rewrite /= ltn_ord.
Qed.

(** The rank from below of the i-th element of E is i. *)
Lemma card_rank_lt (m : nat) (E : {set 'I_m}) (i : 'I_#|E|) :
  #|[set x in E | (x < enum_val i)%N]| = i.
Proof.
have -> : [set x in E | (x < enum_val i)%N]
        = [set enum_val i' | i' : 'I_#|E| & (i' < i)%N].
  apply/setP => x; rewrite !inE.
  apply/andP/imsetP.
  - case=> xE lt_x; exists (enum_rank_in xE x); last first.
      by rewrite enum_rankK_in.
    rewrite inE -(enum_val_ltn (A := mem E)) enum_rankK_in //.
  - case=> i' lt_i' ->; split; first exact: enum_valP.
    by rewrite (enum_val_ltn (A := mem E)); move: lt_i'; rewrite inE.
rewrite card_imset; last exact: enum_val_inj.
have -> : [set i' : 'I_#|E| | (i' < i)%N]
        = [set x : 'I_#|E| | (x < val i)%N].
  by apply/setP => i'; rewrite !inE.
by rewrite card_ord_ltb // ltnW // ltn_ord.
Qed.

(** The rank from above of the i-th element of E is #|E| - i - 1. *)
Lemma card_rank_gt (m : nat) (E : {set 'I_m}) (i : 'I_#|E|) :
  #|[set x in E | (enum_val i < x)%N]| = (#|E| - i.+1)%N.
Proof.
have -> : [set x in E | (enum_val i < x)%N]
        = [set enum_val i' | i' : 'I_#|E| & (i < i')%N].
  apply/setP => x; rewrite !inE.
  apply/andP/imsetP.
  - case=> xE lt_x; exists (enum_rank_in xE x); last first.
      by rewrite enum_rankK_in.
    rewrite inE -(enum_val_ltn (A := mem E)) enum_rankK_in //.
  - case=> i' lt_i' ->; split; first exact: enum_valP.
    by rewrite (enum_val_ltn (A := mem E)); move: lt_i'; rewrite inE.
rewrite card_imset; last exact: enum_val_inj.
have -> : [set i' : 'I_#|E| | (i < i')%N]
        = ~: [set x : 'I_#|E| | (x < i.+1)%N].
  by apply/setP => i'; rewrite !inE ltnS ltnNge.
by rewrite cardsCs setCK card_ord card_ord_ltb // ltn_ord.
Qed.

Lemma sum_rank_lt (m : nat) (E : {set 'I_m}) :
  \sum_(j in E) ('X^(#|[set x in E | (x < j)%N]|) : {poly int})
  = q_int #|E|.
Proof.
rewrite big_enum_val /=.
under eq_bigr => i _ do rewrite card_rank_lt.
by rewrite /q_int.
Qed.

Lemma sum_rank_gt (m : nat) (E : {set 'I_m}) :
  \sum_(j in E) ('X^(#|[set x in E | (j < x)%N]|) : {poly int})
  = q_int #|E|.
Proof.
rewrite big_enum_val /=.
under eq_bigr => i _ do rewrite card_rank_gt.
by rewrite /q_int [RHS](reindex_inj rev_ord_inj) /=.
Qed.

(* ========================================================================= *)
(* §B. The major index of an insertion                                        *)
(* ========================================================================= *)

Lemma sum_in_nat_of_bool (m : nat) (S : {set 'I_m}) (P : pred 'I_m) :
  (\sum_(x in S) (P x : nat))%N = #|[set x in S | P x]|.
Proof.
rewrite -sum1dep_card big_mkcond [RHS]big_mkcond /=.
by apply: eq_bigr => x _; case: (x \in S); case: (P x).
Qed.

(** Front insertion: every old descent shifts up one slot and slot 0 is a    *)
(* new descent: maj increases by des + 1.                                     *)
Lemma maj_insert_max_ord0 (n : nat) (t : {perm 'I_n.+1}) :
  maj (insert_max_perm t (ord0 : 'I_n.+2)) = (maj t + des t + 1)%N.
Proof.
rewrite /maj descent_set_insert_max_ord0.
rewrite big_setU1 /=; last first.
  by apply/imsetP => -[j _ /esym Hj]; have := neq_lift ord0 j; rewrite Hj eqxx.
rewrite big_imset /=; last by move=> ? ? ? ?; exact: lift_inj.
rewrite (eq_bigr (fun j : 'I_n => (val j).+2)); last first.
  by move=> j _; rewrite /= /bump leq0n add1n.
rewrite (eq_bigr (fun i : 'I_n => ((val i).+1 + 1)%N)); last first.
  by move=> i _; rewrite addn1.
rewrite big_split /= sum1_card -/(des t).
by rewrite addnC.
Qed.

(** End insertion: maj is unchanged. *)
Lemma maj_insert_max_ord_max (n : nat) (t : {perm 'I_n.+1}) :
  maj (insert_max_perm t (ord_max : 'I_n.+2)) = maj t.
Proof.
rewrite /maj descent_set_insert_max_ord_max.
rewrite big_imset /=; last by move=> ? ? ? ?; exact: lift_inj.
apply: eq_bigr => j _.
by rewrite /= /bump leqNgt ltn_ord.
Qed.

(** Interior insertion in the gap after slot j: maj increases by             *)
(* (number of descents above j) + 1, plus j+1 more if the gap is an ascent.  *)
Lemma maj_insert_max_interior (n : nat) (t : {perm 'I_n.+1}) (j : 'I_n) :
  maj (insert_max_perm t (lift ord0 (widen_ord (leqnSn n) j)))
  = (maj t + #|[set x in descent_set t | (j < x)%N]| + 1
     + (if is_descent t j then 0 else j.+1))%N.
Proof.
rewrite /maj descent_set_insert_max_interior.
rewrite big_imset /=; last by move=> ? ? ? ?; exact: lift_inj.
rewrite (eq_bigr (fun x : 'I_n => ((val x).+1 + (j <= x))%N)); last first.
  by move=> x _; rewrite /= /bump addnC addSn.
rewrite big_split /=.
rewrite sum_in_nat_of_bool.
have -> : [set x in descent_set t :|: [set j] | (j <= x)%N]
        = j |: [set x in descent_set t | (j < x)%N].
  apply/setP => x; rewrite !inE.
  case: (eqVneq x j) => [-> | neq_xj] /=; first by rewrite leqnn orbT.
  by rewrite orbF ltn_neqAle val_eqE eq_sym neq_xj.
rewrite cardsU1 inE /= ltnn andbF /=.
case Hd: (is_descent t j).
  have -> : descent_set t :|: [set j] = descent_set t.
    by apply/setUidPl; rewrite sub1set mem_descent_set Hd.
  by rewrite addn0 [(1 + _)%N]addnC addnA.
rewrite setUC big_setU1 ?mem_descent_set ?Hd //=.
rewrite addnC !addnA.
rewrite addnAC [(1 + _ + _)%N]addnAC [(1 + _)%N]addnC.
by rewrite [(_ + 1 + _)%N]addnAC.
Qed.

(* ========================================================================= *)
(* §C. The q-Eulerian numbers and their recurrence                            *)
(* ========================================================================= *)

(** B(n,k) = sum of q^(maj sigma) over sigma in S_{n+1} with k descents.     *)
Definition q_eulerian (n k : nat) : {poly int} :=
  \sum_(s : {perm 'I_n.+1} | des s == k) 'X^(maj s).

Lemma q_eulerian_n_0 n : q_eulerian n 0 = 1.
Proof.
rewrite /q_eulerian (big_pred1 (1%g : {perm 'I_n.+1})); last first.
  by move=> s /=; apply/eqP/eqP => [/des0_id //|->]; exact: des_id.
by rewrite maj_id.
Qed.

Lemma q_eulerian_out_of_range n k :
  (n < k)%N -> q_eulerian n k = 0.
Proof.
move=> lt_nk; rewrite /q_eulerian big_pred0 // => s /=.
apply/negbTE/eqP => Hk.
by have := des_le s; rewrite Hk leqNgt lt_nk.
Qed.

(* ----------------------------------------------------------------------- *)
(* Gap sums: q-integers from the two families of insertion slots             *)
(* ----------------------------------------------------------------------- *)

Lemma q_intS m : q_int m.+1 = 1 + 'X * q_int m.
Proof.
rewrite /q_int big_ord_recl /= expr0 big_distrr /=.
by congr (_ + _); apply: eq_bigr => i _; rewrite /bump /= add1n exprS.
Qed.

Lemma card_split_lt_gt (m : nat) (E : {set 'I_m}) (j : 'I_m) :
  j \notin E ->
  (#|[set x in E | (x < j)%N]| + #|[set x in E | (j < x)%N]|)%N = #|E|.
Proof.
move=> jE; rewrite -[RHS](cardsID [set x : 'I_m | (x < j)%N]).
congr (_ + _)%N; congr #|pred_of_set _|.
  by apply/setP => x; rewrite !inE andbC.
apply/setP => x; rewrite !inE -leqNgt andbC.
case xE: (x \in E) => //=.
rewrite !andbT ltn_neqAle.
case: (eqVneq j x) => [eq_jx|//=].
  by rewrite eq_jx xE in jE.
  by move=> neq; rewrite neq.
by rewrite !andbF.
Qed.

Lemma if_sum_const (I : finType) (P : pred I) (b : bool)
    (F : I -> {poly int}) :
  \sum_(i | P i) (if b then F i else 0) = if b then \sum_(i | P i) F i else 0.
Proof. by case: b => //; rewrite big1. Qed.

(** Inserting into the descent gaps: increments 1, ..., des t. *)
Lemma sum_desc_gaps (n : nat) (t : {perm 'I_n.+1}) :
  \sum_(j : 'I_n | is_descent t j)
      ('X^(maj t + #|[set x in descent_set t | (j < x)%N]| + 1) : {poly int})
  = 'X^(maj t) * ('X * q_int (des t)).
Proof.
rewrite (eq_bigl (fun j : 'I_n => j \in descent_set t)); last first.
  by move=> j; rewrite mem_descent_set.
rewrite -sum_rank_gt big_distrr /= big_distrr /=.
apply: eq_bigr => j _.
by rewrite -['X in RHS]expr1 -!exprD addnCA [in RHS]addnC.
Qed.

(** Inserting into the ascent gaps (and counting from the front):            *)
(* increments des t + 2, ..., n + 1.                                         *)
Lemma sum_asc_gaps (n : nat) (t : {perm 'I_n.+1}) :
  \sum_(j : 'I_n | ~~ is_descent t j)
      ('X^(maj t + #|[set x in descent_set t | (j < x)%N]| + 1 + j.+1)
       : {poly int})
  = 'X^(maj t + des t + 2) * q_int (n - des t).
Proof.
rewrite (eq_bigl (fun j : 'I_n => j \in ~: descent_set t)); last first.
  by move=> j; rewrite inE mem_descent_set.
have expE (j : 'I_n) : j \in ~: descent_set t ->
    (maj t + #|[set x in descent_set t | (j < x)%N]| + 1 + j.+1)%N
    = ((maj t + des t + 2)
       + #|[set x in ~: descent_set t | (x < j)%N]|)%N.
  move=> jND.
  have jD : j \notin descent_set t by move: jND; rewrite inE.
  set a := #|[set x in descent_set t | (x < j)%N]|.
  set b := #|[set x in descent_set t | (j < x)%N]|.
  set c := #|[set x in ~: descent_set t | (x < j)%N]|.
  have Hab : (a + b)%N = des t by exact: card_split_lt_gt.
  have Hac : (a + c)%N = j.
    rewrite /a /c.
    rewrite (_ : [set x in descent_set t | (x < j)%N]
                 = [set x : 'I_n | (x < j)%N] :&: descent_set t);
      last by apply/setP => x; rewrite !inE andbC.
    rewrite (_ : [set x in ~: descent_set t | (x < j)%N]
                 = [set x : 'I_n | (x < j)%N] :\: descent_set t);
      last by apply/setP => x; rewrite !inE andbC.
    by rewrite cardsID card_ord_ltb // ltnW // ltn_ord.
  rewrite -Hab -Hac -[(a + c).+1]addn1 !addnA.
  rewrite [(maj t + b + 1 + a)%N]addnAC [(maj t + b + a)%N]addnAC.
  rewrite -!addnA; congr (_ + _)%N; congr (_ + _)%N; congr (_ + _)%N.
  by rewrite [(c + 1)%N]addnC addnA.
rewrite (eq_bigr (fun j : 'I_n =>
    ('X^(maj t + des t + 2)
     * 'X^(#|[set x in ~: descent_set t | (x < j)%N]|) : {poly int})));
  last first.
  by move=> j jND; rewrite (expE j jND) exprD.
rewrite -big_distrr /=.
congr (_ * _).
have -> : (n - des t)%N = #|~: descent_set t|.
  by rewrite cardsCs setCK card_ord.
exact: sum_rank_lt.
Qed.

(* ----------------------------------------------------------------------- *)
(* The recurrence                                                            *)
(* ----------------------------------------------------------------------- *)

(** Carlitz's q-Eulerian recurrence. *)
Theorem q_eulerian_rec n k :
  q_eulerian n.+1 k.+1
  = q_int k.+2 * q_eulerian n k.+1
    + 'X^(k.+1) * (q_int (n.+1 - k) * q_eulerian n k).
Proof.
have lom : lift ord0 (ord_max : 'I_n.+1) = (ord_max : 'I_n.+2).
  by apply/val_inj.
(* the inner sum over the n+2 insertion slots of a fixed t *)
have inner (t : {perm 'I_n.+1}) :
    \sum_(p : 'I_n.+2 | des (insert_max_perm t p) == k.+1)
        ('X^(maj (insert_max_perm t p)) : {poly int})
  = (if des t == k.+1 then 'X^(maj t) * q_int k.+2 else 0)
    + (if des t == k
       then 'X^(maj t) * ('X^(k.+1) * q_int (n.+1 - k)) else 0).
  rewrite big_mkcond big_ord_recl big_ord_recr /= lom.
  rewrite des_insert_max_ord0 maj_insert_max_ord0.
  rewrite des_insert_max_ord_max maj_insert_max_ord_max.
  rewrite (bigID (fun j : 'I_n => is_descent t j)) /=.
  under [X in _ + (X + _ + _)]eq_bigr => j Hj do
    rewrite des_insert_max_interior maj_insert_max_interior Hj addn0 addn0.
  under [X in _ + (_ + X + _)]eq_bigr => j Hj do
    rewrite des_insert_max_interior maj_insert_max_interior
            (negbTE Hj) [(des t + ~~ false)%N]addn1 eqSS.
  rewrite !if_sum_const sum_desc_gaps sum_asc_gaps eqSS.
  have [Hk1 | Hk1] := eqVneq (des t) k.+1.
  - rewrite Hk1 !(gtn_eqF (ltnSn k)) /= add0r !addr0.
    by rewrite [in RHS]q_intS mulrDr mulr1 addrC.
  - have [Hk | Hk] := eqVneq (des t) k; last first.
      by rewrite !addr0.
    have le_kn : (k <= n)%N by rewrite -Hk des_le.
    rewrite Hk /= !add0r addr0 (subSn le_kn) [in RHS]q_intS.
    rewrite mulrDr mulr1 mulrDr.
    congr (_ + _).
      by rewrite -exprD addn1 addnS.
    by rewrite [in X in _ = _ * X]mulrA -exprSr mulrA -exprD addn2 !addnS.
rewrite /q_eulerian.
rewrite (reindex _ (onW_bij _ (insert_max_perm_bij n))) /=.
rewrite -(pair_big_dep xpredT
            (fun t p => des (insert_max_perm t p) == k.+1)
            (fun t p => 'X^(maj (insert_max_perm t p)) : {poly int})) /=.
under eq_bigr => t _ do rewrite inner.
rewrite big_split /=.
congr (_ + _).
- by rewrite -big_mkcond /= -big_distrl /= mulrC.
- by rewrite -big_mkcond /= -big_distrl /= mulrC -mulrA.
Qed.
