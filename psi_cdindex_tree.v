(* psi_cdindex_tree.v — Tree-shape structural proofs (part 2)                *)
(*                                                                           *)
(* Split from original psi_cdindex_tree.v to reduce -vo compilation memory.  *)
(* Contains: endpoint_implies_next_has_left_child, window_size_last_fuel,    *)
(* window_size_last, LR_pred_is_endpoint, and related Examples.              *)
(* Heavy proofs (has_left_child) live in psi_cdindex_tree_hlc.v.             *)

From mathcomp Require Import all_ssreflect.
Require Import mmtree psi_core psi_comm psi_descent_v2 psi_descent_thms.
Require Import psi_cdindex_defs psi_cdindex_tree_hlc.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* ----- M5.2 Examples -------------------------------------------------------- *)

(* Non-triviality: various j,i pairs on running example. *)
Example window_size_psi_ex1 :
  window_size 2 (psi 5 [:: 3; 1; 4; 7; 5; 9; 2; 6]) =
  window_size 2 [:: 3; 1; 4; 7; 5; 9; 2; 6].
Proof. by vm_compute. Qed.

Example window_size_psi_ex2 :
  window_size 5 (psi 2 [:: 3; 1; 4; 7; 5; 9; 2; 6]) =
  window_size 5 [:: 3; 1; 4; 7; 5; 9; 2; 6].
Proof. by vm_compute. Qed.

Example window_size_psi_ex3 :
  window_size 1 (psi 5 [:: 3; 1; 4; 7; 5; 9; 2; 6]) =
  window_size 1 [:: 3; 1; 4; 7; 5; 9; 2; 6].
Proof. by vm_compute. Qed.

Example has_left_child_psi_ex :
  has_left_child 5 (psi 2 [:: 3; 1; 4; 7; 5; 9; 2; 6]) =
  has_left_child 5 [:: 3; 1; 4; 7; 5; 9; 2; 6].
Proof. by vm_compute. Qed.

(* ----- M5.3 Free-endpoint lemma --------------------------------------------- *)

Lemma endpoint_implies_next_has_left_child :
  forall (k : nat) (w : seq nat),
    uniq w -> k.+1 < size w -> ~~ is_internal k w ->
    has_left_child k.+1 w.
Proof.
move=> k w; move: w k.
suff Hind : forall n k w, size w <= n ->
  uniq w -> k.+1 < size w -> ~~ is_internal k w ->
  has_left_child k.+1 w by move=> k w; apply: Hind.
elim => [|n IH]; first by move=> k [].
move=> k [//|a s0] Hsz Huniq Hk1 Hep.
set j := mm_pos (a :: s0).
have Hj : j < (size s0).+1 by apply: mm_pos_lt.
have Hk_lt : k < (size s0).+1 :=
  ltn_trans (ltnSn k) Hk1.
have Hws_k : window_size k (a :: s0) <= 1.
  move: Hep; rewrite /is_internal Hk_lt /=.
  by rewrite -leqNgt.
case: (ltngtP k j) => [Hkj | Hjk | Hkj].
- (* k < j *)
  case: (ltngtP k.+1 j) => [Hk1j | Hk1j | Hk1j].
  + abstract (
    rewrite (has_left_child_cons k.+1 a s0) /= -/j
      Hk1j;
    apply: IH;
    [ rewrite size_take Hj -ltnS;
      exact: leq_trans Hj Hsz
    | have : uniq (take j (a :: s0) ++
               drop j (a :: s0))
        by rewrite cat_take_drop;
      by rewrite cat_uniq => /andP [? _]
    | by rewrite size_take Hj
    | rewrite /is_internal size_take Hj Hkj /=;
      rewrite -leqNgt;
      have H := window_size_cons k a s0;
      rewrite /= -/j Hkj in H;
      by rewrite -H ]).
  + abstract
      (by rewrite ltnS in Hk1j;
       move: (leq_gtF Hk1j); rewrite Hkj).
  + abstract
      (rewrite (has_left_child_cons k.+1 a s0) /= -/j;
      by rewrite Hk1j ltnn eqxx -Hk1j).
- (* j < k *)
  abstract (
  have Hjk1 : j < k.+1 := ltn_trans Hjk (ltnSn k);
  rewrite (has_left_child_cons k.+1 a s0) /= -/j;
  have -> : k.+1 < j = false
    by apply/negbTE; rewrite -leqNgt ltnW;
  have -> : (k.+1 == j) = false by apply: gtn_eqF;
  have Hk1_shift : k.+1 - j - 1 = (k - j - 1).+1
    by rewrite -!addn1 -!addnBAC ?(ltnW Hjk);
  rewrite Hk1_shift;
  apply: IH;
  [ rewrite size_drop /= -ltnS;
    exact: leq_ltn_trans (leq_subr _ _) Hsz
  | move: Huniq;
    rewrite -{1}(cat_take_drop j.+1 (a :: s0))
      cat_uniq;
    by move=> /andP [_ /andP [_ ->]]
  | rewrite size_drop -Hk1_shift;
    exact: ltn_sub2r (ltnW Hjk1) Hk1
  | have Hk_dw : k - j - 1 <
      size (drop j.+1 (a :: s0))
      by apply: ltn_trans (ltnSn _);
      rewrite size_drop -Hk1_shift;
      exact: ltn_sub2r (ltnW Hjk1) Hk1;
    rewrite /is_internal Hk_dw /=;
    rewrite -leqNgt;
    have H := window_size_cons k a s0;
    rewrite /= -/j (ltn_eqF Hjk) in H;
    rewrite ifN in H;
      last by rewrite -leqNgt ltnW;
    by rewrite -H ]).
- (* k = j: impossible *)
  abstract (
  exfalso;
  have Hws_root := window_size_cons j a s0;
  rewrite /= -/j ltnn eqxx in Hws_root;
  have : 1 < (size s0).+1 - j
    by rewrite -Hkj ltn_subRL addnC /=;
       rewrite Hkj;
  by rewrite -Hws_root =>
     /(leq_ltn_trans Hws_k); rewrite ltnn).
Qed.

Example endpoint_next_has_left_child_ex :
  has_left_child 1 [:: 3; 1; 5; 4; 2; 6].
Proof. by vm_compute. Qed.

Example endpoint_next_has_left_child_ex2 :
  has_left_child 4 [:: 3; 1; 5; 4; 2; 6].
Proof. by vm_compute. Qed.

(* ----- M5.4 Disjointness of affected position sets ------------------------ *)

Lemma window_size_last_fuel :
  forall fuel w, size w <= fuel -> 0 < size w ->
  window_size_fuel fuel (size w).-1 w = 1.
Proof.
elim=> [w Hsz Hne|fuel IH [|a s0] Hsz Hne] //.
  by move: Hsz Hne; case: w.
set s := a :: s0. set j := mm_pos s.
have Hj : j < size s by apply: mm_pos_lt.
have Hj2 : j <= size s0 by rewrite -ltnS.
rewrite /= -/s -/j.
have Hjn : (size s0 < j) = false
  by apply/negbTE; rewrite -leqNgt.
rewrite Hjn.
case Hjq: (size s0 == j).
  abstract (by move/eqP: Hjq => <-;
     rewrite /s /= subSn // subnn).
abstract (
have Hjl : j < size s0
  by rewrite ltn_neqAle eq_sym Hjq /=
     leqNgt Hjn;
change (window_size_fuel fuel
  (size s0 - j - 1) (drop j s0) = 1);
have Hsz_ds : size (drop j s0) = size s0 - j
  by rewrite size_drop;
have H0ds : 0 < size (drop j s0)
  by rewrite Hsz_ds subn_gt0;
have Hfuel_ok : size (drop j s0) <= fuel
  by rewrite Hsz_ds;
  apply: leq_trans (leq_subr _ _) _;
  rewrite ltnS in Hsz;
have -> : size s0 - j - 1 =
  (size (drop j s0)).-1
  by rewrite Hsz_ds subn1;
exact: IH Hfuel_ok H0ds).
Qed.

Lemma window_size_last w :
  0 < size w ->
  window_size (size w).-1 w = 1.
Proof.
move=> Hne; rewrite /window_size.
exact: window_size_last_fuel (leqnn _) Hne.
Qed.

Lemma LR_pred_is_endpoint :
  forall (i : nat) (w : seq nat),
  uniq w -> 0 < i -> is_internal i w ->
  has_left_child i w ->
  ~~ is_internal i.-1 w.
Proof.
suff H : forall n i w, size w <= n ->
  uniq w -> 0 < i -> is_internal i w ->
  has_left_child i w ->
  ~~ is_internal i.-1 w.
  by move=> i w; exact: H (leqnn _).
elim=> [i w Hsz _ _ Hint _|
  n IH i [|a s0] Hsz Huniq Hi0 Hint Hlc] //.
  move: Hint; rewrite /is_internal =>
    /andP [Hi _].
  by move: (leq_trans Hi Hsz); rewrite ltn0.
set s := a :: s0. set j := mm_pos s.
have Hj : j < size s by apply: mm_pos_lt.
have Hj2 : j <= size s0 by rewrite -ltnS.
have Hiw : i < size s
  by move: Hint; rewrite /is_internal =>
     /andP [].
have Hws : 1 < window_size i s
  by move: Hint; rewrite /is_internal =>
     /andP [].
rewrite has_left_child_cons -/s -/j in Hlc.
rewrite window_size_cons -/s -/j in Hws.
case: (ltngtP i j) => [Hij | Hji | Heq].
- (* i < j: both i and i-1 in left subtree *)
  abstract (
  rewrite Hij in Hlc Hws;
  have Hi1j : i.-1 < j
    by exact:
       leq_ltn_trans (leq_pred _) Hij;
  rewrite /is_internal window_size_cons
    -/s -/j Hi1j;
  have Htake_sz : size (take j s) = j
    by rewrite size_take Hj;
  have Huniq_t : uniq (take j s)
    by exact:
       subseq_uniq (take_subseq _ _) Huniq;
  case E:
    (1 < window_size i.-1 (take j s));
    last by rewrite andbF;
  have Hint_t : is_internal i (take j s)
    by rewrite /is_internal Htake_sz Hij Hws;
  have Hsz_t : size (take j s) <= n
    by rewrite Htake_sz;
    apply: leq_trans Hj2 _;
    rewrite /s /= ltnS in Hsz;
  have := IH i (take j s) Hsz_t Huniq_t
    Hi0 Hint_t Hlc;
  by rewrite /is_internal
     Htake_sz Hi1j /= E).
- (* j < i: right subtree *)
  abstract (
  have Hlti : ~~ (i < j)
    by rewrite -leqNgt ltnW;
  have Hi_ne_j : (i == j) = false
    by rewrite gtn_eqF;
  rewrite (negbTE Hlti) Hi_ne_j in Hlc Hws;
  case Ei1j : (i.-1 == j);
  [ move/eqP: Ei1j => Ei1j;
    have Ei : i = j.+1
      by rewrite -(prednK Hi0) Ei1j;
    by rewrite Ei subSn // subnn
       has_left_child_0 in Hlc
  | have Hi1j : j < i.-1
      by rewrite ltn_neqAle eq_sym Ei1j /=;
      rewrite -ltnS (prednK Hi0);
    have Huniq_d : uniq (drop j.+1 s)
      by exact:
         subseq_uniq (drop_subseq _ _) Huniq;
    have Hi0' : 0 < i - j - 1
      by rewrite ltn_predRL in Hi1j;
      rewrite -subnDA addn1 subn_gt0;
    have Hpred :
      (i - j - 1).-1 = i.-1 - j - 1
      by rewrite !predn_sub;
    have Hsz_d : size (drop j.+1 s) <= n
      by rewrite /s /= size_drop;
      apply: leq_trans (leq_subr _ _) _;
      rewrite /s /= ltnS in Hsz;
    have Hi_ds :
      i - j - 1 < size (drop j.+1 s)
      by rewrite /s /= size_drop;
      have Hisz : i <= size s0
        by rewrite -ltnS;
      have H3 : 0 < i - j
        by rewrite subn_gt0;
      have H4 : i - j <= size s0 - j :=
        leq_sub2r j Hisz;
      have H5 : i - j - 1 < i - j
        by case: (i - j) H3 => [//|k _] /=;
        rewrite subSS; exact: leq_subr;
      exact: leq_trans H5 H4;
    have Hint_d :
      is_internal (i - j - 1) (drop j.+1 s)
      by rewrite /is_internal Hi_ds Hws;
    have Hih :=
      IH _ _ Hsz_d Huniq_d Hi0' Hint_d Hlc;
    move: Hih; rewrite /is_internal Hpred;
    set ds := drop j.+1 s;
    rewrite negb_and => /orP [Hoor | Hws1];
    [ rewrite /is_internal window_size_cons
        -/s -/j;
      have Hi1ltj : (i.-1 < j) = false
        by rewrite ltnNge ltnW;
      rewrite Hi1ltj Ei1j -/ds;
      rewrite negb_and; apply/orP; right;
      move: Hoor; rewrite -leqNgt => Hoor;
      by rewrite -leqNgt
         (window_size_oor Hoor)
    | rewrite /is_internal window_size_cons
        -/s -/j;
      have Hi1ltj : (i.-1 < j) = false
        by rewrite ltnNge ltnW;
      rewrite Hi1ltj Ei1j -/ds;
      by rewrite negb_and -leqNgt
         (negbTE Hws1) orbT ] ]).
- (* i = j: root, i-1 last of left subtree *)
  abstract (
  rewrite -Heq eqxx in Hlc Hws;
  have Hj0 : 0 < j by rewrite -Heq;
  rewrite /is_internal window_size_cons
    -/s -/j;
  rewrite Heq ltn_predL Hj0;
  have Htake_sz : size (take j s) = j
    by rewrite size_take Hj;
  rewrite negb_and; apply/orP; right;
  rewrite -leqNgt;
  have -> : j.-1 = (size (take j s)).-1
    by rewrite Htake_sz;
  have H0t : 0 < size (take j s)
    by rewrite Htake_sz;
  by rewrite (window_size_last H0t)).
Qed.

Example LR_pred_is_endpoint_ex :
  ~~ is_internal 0 [:: 3; 1; 5; 4; 2; 6].
Proof. by vm_compute. Qed.

Example LR_pred_is_endpoint_ex2 :
  ~~ is_internal 3 [:: 3; 1; 5; 4; 2; 6].
Proof. by vm_compute. Qed.

Example LR_pred_is_endpoint_ex3 :
  ~~ is_internal 4 [:: 3; 1; 4; 7; 5; 9; 2; 6].
Proof. by vm_compute. Qed.
