(* psi_cdindex_tree.v — Heavy tree-shape structural proofs                    *)
(*                                                                           *)
(* Split from psi_cdindex_core.v to reduce -vo compilation memory.           *)
(* Contains: has_left_child_order_iso, has_left_child_psi,                   *)
(* endpoint_implies_next_has_left_child, window_size_last_fuel/last,         *)
(* LR_pred_is_endpoint, and related Examples.                                *)

From mathcomp Require Import all_ssreflect.
Require Import mmtree psi_core psi_comm psi_descent_v2 psi_descent_thms.
Require Import psi_cdindex_defs.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* ----- M5.2 Tree-shape invariance under psi -------------------------------- *)

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

Lemma has_left_child_order_iso (s1 s2 : seq nat) i :
  size s1 = size s2 -> uniq s1 -> uniq s2 ->
  (forall p q, p < size s1 -> q < size s1 ->
    (nth 0 s1 p < nth 0 s1 q) =
    (nth 0 s2 p < nth 0 s2 q)) ->
  has_left_child i s1 = has_left_child i s2.
Proof.
move: s1 s2 i.
suff Hgen : forall n s1 s2 i, size s1 <= n ->
  size s1 = size s2 -> uniq s1 -> uniq s2 ->
  (forall p q, p < size s1 -> q < size s1 ->
    (nth 0 s1 p < nth 0 s1 q) =
    (nth 0 s2 p < nth 0 s2 q)) ->
  has_left_child i s1 = has_left_child i s2.
  by move=> s1 s2 i; apply: (Hgen (size s1));
     rewrite ?leqnn.
elim=> [|n IH] s1 s2 i Hsz1 Hszeq Hu1 Hu2 Hord.
  have Hsz0 : size s1 = 0.
    by apply/eqP; rewrite -leqn0.
  by rewrite (size0nil Hsz0); rewrite Hsz0 in Hszeq;
     rewrite (size0nil (esym Hszeq)).
case Hs1 : s1 => [|a1 t1]; first
  by move: Hszeq; rewrite Hs1 /= => Hsz2;
     have -> : s2 = [::] by apply/eqP;
     rewrite -size_eq0 -Hsz2.
case Hs2 : s2 => [|a2 t2]; first
  by move: Hszeq; rewrite Hs1 Hs2 /=.
have Hne1 : a1 :: t1 <> [::] by [].
have Hne2 : a2 :: t2 <> [::] by [].
have Hszeq' : size (a1 :: t1) = size (a2 :: t2)
  by rewrite -Hs1 -Hs2.
subst s1 s2.
have Hmm := mm_pos_order_iso Hszeq' Hu1 Hu2 Hne1 Hord.
set m := mm_pos (a1 :: t1).
rewrite (has_left_child_cons i a1 t1) -/m.
rewrite (has_left_child_cons i a2 t2) -Hmm -/m.
have Hm1 : m < size (a1 :: t1) by apply: mm_pos_lt.
case: (ltngtP i m) => [Him | Hmi | _].
- apply: IH.
  + rewrite size_takel ?ltnW //.
    exact: leq_trans (ltnW Hm1) Hsz1.
  + by rewrite !size_takel // ?ltnW //
       -(mm_pos_order_iso Hszeq' Hu1 Hu2 Hne1 Hord).
  + by move: Hu1; rewrite -{1}(cat_take_drop m (a1 :: t1))
       cat_uniq => /andP [].
  + by move: Hu2; rewrite -{1}(cat_take_drop m (a2 :: t2))
       cat_uniq => /andP [].
  + move=> p q Hp Hq.
    rewrite !nth_take //.
    apply: Hord;
      apply: ltn_trans _ Hm1; rewrite size_takel ?ltnW //
      in Hp Hq; done.
- apply: IH.
  + rewrite size_drop.
    by apply: leq_trans (leq_subr _ _);
       rewrite /= ltnS in Hsz1;
       exact: (leq_trans (leqnSn _) Hsz1).
  + by rewrite !size_drop Hszeq'.
  + by move: Hu1;
       rewrite -{1}(cat_take_drop m.+1 (a1 :: t1))
       cat_uniq => /andP [_ /andP [_ ?]].
  + by move: Hu2;
       rewrite -{1}(cat_take_drop m.+1 (a2 :: t2))
       cat_uniq => /andP [_ /andP [_ ?]].
  + move=> p q Hp Hq.
    rewrite !nth_drop; apply: Hord;
      rewrite /= ltnS size_drop /= in Hp Hq;
      rewrite /= ltnS;
      by apply: leq_trans _ (leq_subr _ _) => //;
         exact: leq_add.
- by [].
Qed.

Lemma has_left_child_psi :
  forall (j i : nat) (w : seq nat),
  uniq w ->
  has_left_child i (psi j w) = has_left_child i w.
Proof.
suff Hgen : forall n j i w, size w <= n ->
  uniq w -> has_left_child i (psi j w) = has_left_child i w.
  by move=> j i w Hu; apply: (Hgen (size w));
     rewrite ?leqnn.
elim=> [|n IH] j i w Hsz Huniq.
  by move: Hsz; rewrite leqn0 => /eqP/size0nil ->.
have [Htriv | Hws_gt1] := leqP (window_size j w) 1.
  by rewrite (psi_id_trivial Htriv).
have Hjw := ws_lt_size Hws_gt1.
have Hw_ne : w <> [::] by case: (w) Hjw.
case: (w) Hw_ne Huniq Hws_gt1 Hjw Hsz =>
  [//|a s0] _ Huniq Hws_gt1 Hjw Hsz.
set s := a :: s0.
set m := mm_pos s.
have Hm : m < size s by apply: mm_pos_lt.
have Hs_ne : s <> [::] by discriminate.
have Hm' : mm_pos (psi j s) = m by apply: mm_pos_psi_eq.
have Hpsi_ne : psi j s <> [::].
  by move=> E; move: Hjw; rewrite -(size_psi j) E.
have [a' [s0' Hpsi_eq]] : exists a' s0', psi j s =
  a' :: s0'.
  by case: (psi j s) Hpsi_ne => [//|x y] _; exists x, y.
have Hm'c : mm_pos (a' :: s0') = m
  by rewrite -Hpsi_eq.
rewrite Hpsi_eq (has_left_child_cons i a' s0') Hm'c.
rewrite (has_left_child_cons i a s0) -/m.
case: (ltngtP i m) => [Him | Hmi | Hieqm].
- (* i < m *)
  case: (ltngtP j m) => [Hjm | Hmj | Hjeqm].
  + (* j < m *)
    rewrite -Hpsi_eq (take_mm_psi Hs_ne Huniq Hws_gt1 Hjm).
    apply: IH.
    * rewrite size_take Hm.
      exact: leq_trans (ltnW Hm) Hsz.
    * have : uniq (take m s ++ drop m s)
        by rewrite cat_take_drop.
      by rewrite cat_uniq => /andP [? /andP [? ?]].
  + by rewrite -Hpsi_eq (@take_psi m j s (ltnW Hmj)).
  + by rewrite -Hpsi_eq Hjeqm
       (@take_psi m m s (leqnn m)).
- (* i > m *)
  case: (ltngtP j m) => [Hjm | Hmj | Hjeqm].
  + (* j < m *)
    suff -> : drop m.+1 (a' :: s0') =
      drop m.+1 (a :: s0) by [].
    rewrite -Hpsi_eq.
    apply: drop_psi_above.
    apply: leq_trans (window_fits_left Hs_ne Hjm) _.
    exact: leqnSn.
  + (* j > m *)
    suff -> : drop m.+1 (a' :: s0') =
      psi (j - m - 1) (drop m.+1 (a :: s0)).
      apply: IH.
      * rewrite /s /= size_drop.
        exact: leq_trans (leq_subr _ _) (ltnW Hsz).
      * have : uniq (take m.+1 s ++ drop m.+1 s)
          by rewrite cat_take_drop.
        by rewrite cat_uniq => /andP [_ /andP [_ ?]].
    by rewrite -Hpsi_eq
       (drop_mm_psi Hs_ne Huniq Hws_gt1 Hmj).
  + (* j = m: use has_left_child_order_iso *)
    subst j.
    have Hws_m : window_size m s = size s - m.
      by rewrite (window_size_cons m a s0) -/m ltnn eqxx.
    have Hws_drop : 1 < size (drop m s).
      by rewrite size_drop -Hws_m.
    have Hdm_ne : drop m s <> [::].
      by case: (drop m s) Hws_drop.
    have Huniq_dm : uniq (drop m s).
      have : uniq (take m s ++ drop m s)
        by rewrite cat_take_drop.
      by rewrite cat_uniq => /andP [_ /andP [_ ?]].
    have Hmm_drop : mm_pos (drop m s) = 0
      by exact: mm_pos_drop_mm.
    (* psi m s = take m s ++ rank_shift_seq (drop m s) *)
    have Hpsi_m_eq : psi m s =
      take m s ++ rank_shift_seq (drop m s).
      rewrite /psi.
      have Hwa_m : window_at m s = drop m s.
        rewrite (window_at_cons m a s0) -/m ltnn eqxx //.
      rewrite Hwa_m Hws_m.
      by rewrite subnKC ?drop_size ?cats0 // ltnW.
    (* Use has_left_child_order_iso *)
    have Him' : 0 < i - m by rewrite subn_gt0.
    (* drop m.+1 (psi m s) = behead (rank_shift_seq (drop m s)) *)
    have Hdrop_psi : drop m.+1 (a' :: s0') =
      behead (rank_shift_seq (drop m s)).
      rewrite -Hpsi_eq Hpsi_m_eq.
      rewrite drop_cat size_take Hm.
      have -> : m.+1 < m = false by rewrite ltnNge leqnSn.
      by rewrite /= subSn // subnn drop0.
    have Hdrop_orig : drop m.+1 (a :: s0) =
      behead (drop m s).
      by rewrite /s /= drop0.
    rewrite Hdrop_psi Hdrop_orig.
    apply: has_left_child_order_iso.
    * by rewrite !size_behead size_rank_shift_seq2.
    * apply: (subseq_uniq (suffix_subseq 1 _)).
      by rewrite (perm_uniq (rank_shift_perm_eq _)).
    * exact: (subseq_uniq (suffix_subseq 1 _)).
    * move=> p q Hp Hq.
      have Hsz_bh : size (behead (drop m s)) =
        (size (drop m s)).-1
        by rewrite size_behead.
      have Hp1 : p.+1 < size (drop m s).
        by rewrite -ltnS prednK //;
           rewrite Hsz_bh in Hp; apply: ltnW.
      have Hq1 : q.+1 < size (drop m s).
        by rewrite -ltnS prednK //;
           rewrite Hsz_bh in Hq; apply: ltnW.
      rewrite -[behead (rank_shift_seq _)]
        (drop1 (rank_shift_seq (drop m s))).
      rewrite -[behead (drop m s)](drop1 (drop m s)).
      rewrite !nth_drop.
      rewrite [1 + p]addnC [1 + q]addnC.
      have Hrsz : size (rank_shift_seq (drop m s)) =
        size (drop m s)
        by rewrite size_rank_shift_seq2.
      have Hp1' : p.+1 < size s.
        rewrite /s /= ltnS.
        by rewrite size_drop /= in Hp1;
           apply: leq_trans (leq_subr _ _) (ltnW Hsz).
      have Hq1' : q.+1 < size s.
        rewrite /s /= ltnS.
        by rewrite size_drop /= in Hq1;
           apply: leq_trans (leq_subr _ _) (ltnW Hsz).
      (* Use rank_shift_preserves_interior_order *)
      have Hhead_ext : (head 0 (drop m s) ==
        nth 0 (sort leq (drop m s)) 0) ||
        (head 0 (drop m s) == nth 0 (sort leq (drop m s))
        (size (drop m s)).-1).
        apply: window_head_extremum => //.
        rewrite (window_size_cons m a s0) -/m ltnn eqxx //.
      symmetry.
      exact: rank_shift_preserves_interior_order
        Huniq_dm Hws_drop Hhead_ext
        (ltnW (ltn0Sn _)) (ltnW (ltn0Sn _)) Hp1 Hq1.
- (* i = m *)
  by [].
Qed.


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
  + rewrite (has_left_child_cons k.+1 a s0) /= -/j
      Hk1j.
    apply: IH.
    * rewrite size_take Hj -ltnS.
      exact: leq_trans Hj Hsz.
    * have : uniq (take j (a :: s0) ++
               drop j (a :: s0))
        by rewrite cat_take_drop.
      by rewrite cat_uniq => /andP [? _].
    * by rewrite size_take Hj.
    * rewrite /is_internal size_take Hj Hkj /=.
      rewrite -leqNgt.
      have H := window_size_cons k a s0.
      rewrite /= -/j Hkj in H.
      by rewrite -H.
  + by rewrite ltnS in Hk1j;
       move: (leq_gtF Hk1j); rewrite Hkj.
  + rewrite (has_left_child_cons k.+1 a s0) /= -/j.
    by rewrite Hk1j ltnn eqxx -Hk1j.
- (* j < k *)
  have Hjk1 : j < k.+1 := ltn_trans Hjk (ltnSn k).
  rewrite (has_left_child_cons k.+1 a s0) /= -/j.
  have -> : k.+1 < j = false.
    by apply/negbTE; rewrite -leqNgt ltnW.
  have -> : (k.+1 == j) = false by apply: gtn_eqF.
  have Hk1_shift : k.+1 - j - 1 = (k - j - 1).+1.
    by rewrite -!addn1 -!addnBAC ?(ltnW Hjk).
  rewrite Hk1_shift.
  apply: IH.
  * rewrite size_drop /= -ltnS.
    exact: leq_ltn_trans (leq_subr _ _) Hsz.
  * move: Huniq.
    rewrite -{1}(cat_take_drop j.+1 (a :: s0))
      cat_uniq.
    by move=> /andP [_ /andP [_ ->]].
  * rewrite size_drop -Hk1_shift.
    exact: ltn_sub2r (ltnW Hjk1) Hk1.
  * have Hk_dw : k - j - 1 <
      size (drop j.+1 (a :: s0)).
      apply: ltn_trans (ltnSn _).
      rewrite size_drop -Hk1_shift.
      exact: ltn_sub2r (ltnW Hjk1) Hk1.
    rewrite /is_internal Hk_dw /=.
    rewrite -leqNgt.
    have H := window_size_cons k a s0.
    rewrite /= -/j (ltn_eqF Hjk) in H.
    rewrite ifN in H;
      last by rewrite -leqNgt ltnW.
    by rewrite -H.
- (* k = j: impossible *)
  exfalso.
  have Hws_root := window_size_cons j a s0.
  rewrite /= -/j ltnn eqxx in Hws_root.
  have : 1 < (size s0).+1 - j.
    by rewrite -Hkj ltn_subRL addnC /=;
       rewrite Hkj.
  by rewrite -Hws_root =>
     /(leq_ltn_trans Hws_k); rewrite ltnn.
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
  by move/eqP: Hjq => <-;
     rewrite /s /= subSn // subnn.
have Hjl : j < size s0
  by rewrite ltn_neqAle eq_sym Hjq /=
     leqNgt Hjn.
change (window_size_fuel fuel
  (size s0 - j - 1) (drop j s0) = 1).
have Hsz_ds : size (drop j s0) = size s0 - j
  by rewrite size_drop.
have H0ds : 0 < size (drop j s0)
  by rewrite Hsz_ds subn_gt0.
have Hfuel_ok : size (drop j s0) <= fuel.
  rewrite Hsz_ds.
  apply: leq_trans (leq_subr _ _) _.
  by rewrite ltnS in Hsz.
have -> : size s0 - j - 1 =
  (size (drop j s0)).-1
  by rewrite Hsz_ds subn1.
exact: IH Hfuel_ok H0ds.
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
  rewrite Hij in Hlc Hws.
  have Hi1j : i.-1 < j
    by exact:
       leq_ltn_trans (leq_pred _) Hij.
  rewrite /is_internal window_size_cons
    -/s -/j Hi1j.
  have Htake_sz : size (take j s) = j
    by rewrite size_take Hj.
  have Huniq_t : uniq (take j s)
    by exact:
       subseq_uniq (take_subseq _ _) Huniq.
  case E:
    (1 < window_size i.-1 (take j s)); last
    by rewrite andbF.
  have Hint_t : is_internal i (take j s)
    by rewrite /is_internal Htake_sz Hij Hws.
  have Hsz_t : size (take j s) <= n.
    rewrite Htake_sz.
    apply: leq_trans Hj2 _.
    by rewrite /s /= ltnS in Hsz.
  have := IH i (take j s) Hsz_t Huniq_t
    Hi0 Hint_t Hlc.
  by rewrite /is_internal
     Htake_sz Hi1j /= E.
- (* j < i: right subtree *)
  have Hlti : ~~ (i < j)
    by rewrite -leqNgt ltnW.
  have Hi_ne_j : (i == j) = false
    by rewrite gtn_eqF.
  rewrite (negbTE Hlti) Hi_ne_j in Hlc Hws.
  case Ei1j : (i.-1 == j).
    move/eqP: Ei1j => Ei1j.
    have Ei : i = j.+1
      by rewrite -(prednK Hi0) Ei1j.
    by rewrite Ei subSn // subnn
       has_left_child_0 in Hlc.
  have Hi1j : j < i.-1.
    rewrite ltn_neqAle eq_sym Ei1j /=.
    by rewrite -ltnS (prednK Hi0).
  have Huniq_d : uniq (drop j.+1 s)
    by exact:
       subseq_uniq (drop_subseq _ _) Huniq.
  have Hi0' : 0 < i - j - 1.
    rewrite ltn_predRL in Hi1j.
    by rewrite -subnDA addn1 subn_gt0.
  have Hpred :
    (i - j - 1).-1 = i.-1 - j - 1
    by rewrite !predn_sub.
  have Hsz_d : size (drop j.+1 s) <= n.
    rewrite /s /= size_drop.
    apply: leq_trans (leq_subr _ _) _.
    by rewrite /s /= ltnS in Hsz.
  have Hi_ds :
    i - j - 1 < size (drop j.+1 s).
    rewrite /s /= size_drop.
    have Hisz : i <= size s0
      by rewrite -ltnS.
    have H3 : 0 < i - j
      by rewrite subn_gt0.
    have H4 : i - j <= size s0 - j :=
      leq_sub2r j Hisz.
    have H5 : i - j - 1 < i - j.
      case: (i - j) H3 => [//|k _] /=.
      by rewrite subSS; exact: leq_subr.
    exact: leq_trans H5 H4.
  have Hint_d :
    is_internal (i - j - 1) (drop j.+1 s)
    by rewrite /is_internal Hi_ds Hws.
  have Hih :=
    IH _ _ Hsz_d Huniq_d Hi0' Hint_d Hlc.
  move: Hih; rewrite /is_internal Hpred.
  set ds := drop j.+1 s.
  rewrite negb_and => /orP [Hoor | Hws1].
    rewrite /is_internal window_size_cons
      -/s -/j.
    have Hi1ltj : (i.-1 < j) = false
      by rewrite ltnNge ltnW.
    rewrite Hi1ltj Ei1j -/ds.
    rewrite negb_and; apply/orP; right.
    move: Hoor; rewrite -leqNgt => Hoor.
    by rewrite -leqNgt
       (window_size_oor Hoor).
  rewrite /is_internal window_size_cons
    -/s -/j.
  have Hi1ltj : (i.-1 < j) = false
    by rewrite ltnNge ltnW.
  rewrite Hi1ltj Ei1j -/ds.
  by rewrite negb_and -leqNgt
     (negbTE Hws1) orbT.
- (* i = j: root, i-1 last of left subtree *)
  rewrite -Heq eqxx in Hlc Hws.
  have Hj0 : 0 < j by rewrite -Heq.
  rewrite /is_internal window_size_cons
    -/s -/j.
  rewrite Heq ltn_predL Hj0.
  have Htake_sz : size (take j s) = j
    by rewrite size_take Hj.
  rewrite negb_and; apply/orP; right.
  rewrite -leqNgt.
  have -> : j.-1 = (size (take j s)).-1
    by rewrite Htake_sz.
  have H0t : 0 < size (take j s)
    by rewrite Htake_sz.
  by rewrite (window_size_last H0t).
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
