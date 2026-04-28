(* psi_comm.v — Milestone 3: Commutativity of psi + supporting helpers       *)

From mathcomp Require Import all_ssreflect.
Require Import mmtree psi_core.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(* ----- M4.3 helpers -------------------------------------------------------- *)

Lemma sorted_uniq_nth_ltn (s : seq nat) (i j : nat) :
  sorted leq s -> uniq s -> i < size s -> j < size s ->
  (nth 0 s i < nth 0 s j) = (i < j).
Proof.
move=> Hs Hu Hi Hj.
apply/idP/idP => [Hlt | Hlt].
- rewrite ltnNge; apply/negP => Hji.
  have : nth 0 s j <= nth 0 s i.
    by apply: (sorted_leq_nth leq_trans leqnn) => //.
  by rewrite leqNgt Hlt.
- have Hle : nth 0 s i <= nth 0 s j.
    by apply: (sorted_leq_nth leq_trans leqnn) => //;
       exact: ltnW.
  have Hne : nth 0 s i != nth 0 s j.
    by rewrite nth_uniq // ltn_eqF.
  by rewrite ltn_neqAle Hne Hle.
Qed.

Lemma shift_preserves_ltn (rp rq k delta : nat) :
  0 < k -> rp < k -> rq < k ->
  ((delta = k.-1 /\ 0 < rp /\ 0 < rq) \/
   (delta = 1 /\ rp < k.-1 /\ rq < k.-1)) ->
  (rq < rp) = ((rq + delta) %% k < (rp + delta) %% k).
Proof.
move=> Hk0 Hrp_k Hrq_k.
have shift_eq : forall n m : nat, 0 < n -> 0 < m ->
  n + m.-1 = n.-1 + m.
  by case=> [|n'] //; case=> [|m'] //= _ _; rewrite addnS.
case => [[Hd [Hrp0 Hrq0]] | [Hd [Hrp_lt Hrq_lt]]].
- rewrite Hd.
  have Hrp_mod : (rp + k.-1) %% k = rp.-1.
    rewrite (shift_eq _ _ Hrp0 Hk0) modnDr modn_small //.
    exact: leq_ltn_trans (leq_pred _) Hrp_k.
  have Hrq_mod : (rq + k.-1) %% k = rq.-1.
    rewrite (shift_eq _ _ Hrq0 Hk0) modnDr modn_small //.
    exact: leq_ltn_trans (leq_pred _) Hrq_k.
  rewrite Hrp_mod Hrq_mod.
  by case: (rp) Hrp0 => [|rp'] //; case: (rq) Hrq0.
- rewrite Hd.
  have Hkm1' : k.-1 < k by rewrite prednK.
  have Hrp_mod : (rp + 1) %% k = rp.+1.
    rewrite modn_small; last first.
      by rewrite addn1; exact: leq_ltn_trans Hrp_lt Hkm1'.
    by rewrite addn1.
  have Hrq_mod : (rq + 1) %% k = rq.+1.
    rewrite modn_small; last first.
      by rewrite addn1; exact: leq_ltn_trans Hrq_lt Hkm1'.
    by rewrite addn1.
  by rewrite Hrp_mod Hrq_mod.
Qed.

(* ----- M4.3 Interior order preservation ----------------------------------- *)
(* For non-head indices p, q >= 1 in a uniq list L of size >= 2 whose head  *)
(* is an extremum, rank_shift preserves relative order. The shift maps       *)
(* rank r to r-1 (if head=min) or r+1 (if head=max), both monotone on the  *)
(* non-head rank range. Proof: modular arithmetic on index in sorted L.     *)
(* Justification: M4_DESCENT_EFFECT_INFORMAL.md section 2 (Case 2).         *)

Lemma rank_shift_preserves_interior_order :
  forall (L : seq nat) (p q : nat),
  uniq L -> 1 < size L ->
  (head 0 L == nth 0 (sort leq L) 0) ||
  (head 0 L == nth 0 (sort leq L) (size L).-1) ->
  0 < p -> 0 < q -> p < size L -> q < size L ->
  (nth 0 L p > nth 0 L q) =
  (nth 0 (rank_shift_seq L) p > nth 0 (rank_shift_seq L) q).
Proof.
move=> L p q Hu Hsz Hhead Hp0 Hq0 Hp Hq.
set srt := sort leq L.  set k := size L.
have Hk0 : 0 < k by exact: ltnW.
have Hu_s : uniq srt by rewrite sort_uniq.
have Hs : sorted leq srt := sort_sorted leq_total L.
have Hsz_s : size srt = k by rewrite size_sort.
have Hp_mem : nth 0 L p \in srt by rewrite mem_sort mem_nth.
have Hq_mem : nth 0 L q \in srt by rewrite mem_sort mem_nth.
set rp := index (nth 0 L p) srt.
set rq := index (nth 0 L q) srt.
have Hip : rp < k by rewrite /rp -Hsz_s index_mem.
have Hiq : rq < k by rewrite /rq -Hsz_s index_mem.
have Ep : nth 0 L p = nth 0 srt rp by rewrite /rp nth_index.
have Eq : nth 0 L q = nth 0 srt rq by rewrite /rq nth_index.
have Hp_ne : nth 0 L p != head 0 L.
  by rewrite -(nth0 0 L) nth_uniq // gtn_eqF.
have Hq_ne : nth 0 L q != head 0 L.
  by rewrite -(nth0 0 L) nth_uniq // gtn_eqF.
have HlhsE : (nth 0 L p > nth 0 L q) = (rq < rp).
  by rewrite Eq Ep sorted_uniq_nth_ltn // Hsz_s.
have HrhsE :
  (nth 0 (rank_shift_seq L) p > nth 0 (rank_shift_seq L) q) =
  ((rq + (if head 0 L == nth 0 srt 0 then k.-1 else 1)) %% k <
   (rp + (if head 0 L == nth 0 srt 0 then k.-1 else 1)) %% k).
  rewrite (nth_rank_shift_seq Hu Hsz Hp)
          (nth_rank_shift_seq Hu Hsz Hq).
  by rewrite -/srt -/k -/rp -/rq
     sorted_uniq_nth_ltn // ?Hsz_s ?ltn_pmod.
rewrite HlhsE HrhsE.
set delta := if head 0 L == nth 0 srt 0 then k.-1 else 1.
apply: shift_preserves_ltn => //.
have Hmin_rank : head 0 L = nth 0 srt 0 ->
  0 < rp /\ 0 < rq.
  move=> Hmin; split; rewrite lt0n; apply/eqP => Heq.
  - by move: Hp_ne; rewrite Ep Heq Hmin eqxx.
  - by move: Hq_ne; rewrite Eq Heq Hmin eqxx.
have Hmax_rank : head 0 L = nth 0 srt k.-1 ->
  rp < k.-1 /\ rq < k.-1.
  move=> Hmax; split; rewrite ltn_neqAle; apply/andP; split;
    try by rewrite -ltnS prednK.
  - by apply/eqP=> Heq; move: Hp_ne; rewrite Ep Heq Hmax eqxx.
  - by apply/eqP=> Heq; move: Hq_ne; rewrite Eq Heq Hmax eqxx.
case/orP: Hhead => [/eqP Hmin | /eqP Hmax].
- left; split; first by rewrite /delta Hmin eqxx.
  exact: Hmin_rank.
- right; split.
  + rewrite /delta; case Heq : (head 0 L == nth 0 srt 0) => //.
    exfalso; move/eqP: Heq => Heq.
    have Hkm1_gt0 : 0 < k.-1 by rewrite -ltnS prednK.
    have Hkm1' : k.-1 < k by rewrite prednK.
    have : nth 0 srt 0 = nth 0 srt k.-1.
      by rewrite -Heq -Hmax.
    move/(f_equal (fun x => index x srt)).
    rewrite !index_uniq // ?Hsz_s // => Habs.
    by move: Hkm1_gt0; rewrite -Habs.
  + exact: Hmax_rank.
Qed.

Opaque sorted_uniq_nth_ltn shift_preserves_ltn.
Opaque rank_shift_preserves_interior_order.
Opaque window_size_cons window_at_cons.
Opaque window_size_order_iso.
Opaque mm_pos_psi_eq mm_pos_lt mm_pos_drop_mm.
Opaque psi_id_trivial ws_lt_size psi_perm_eq.
Opaque take_mm_psi drop_mm_psi take_psi.
Opaque drop_psi_above.
Opaque window_fits_left nth_psi_left nth_psi_right.
Opaque window_head_extremum.
Opaque rank_shift_seqE nth_rank_shift_seq.
Opaque rank_shift_perm_eq size_rank_shift_seq2.
Opaque psi_id_oor size_psi window_size_bound.

Lemma window_size_psi :
  forall (j i : nat) (w : seq nat),
  uniq w ->
  window_size i (psi j w) = window_size i w.
Proof.
suff Hgen : forall n j i w, size w <= n ->
  uniq w ->
  window_size i (psi j w) = window_size i w.
  by move=> j i w Hu;
     apply: (Hgen (size w)); rewrite ?leqnn.
elim=> [|n IH] j i w Hsz Huniq.
  by move: Hsz; rewrite leqn0 =>
     /eqP/size0nil ->.
have [Htriv | Hws_gt1] :=
  leqP (window_size j w) 1.
  by rewrite (psi_id_trivial Htriv).
have Hjw := ws_lt_size Hws_gt1.
have Hw_ne : w <> [::] by case: (w) Hjw.
case: (w) Hw_ne Huniq Hws_gt1 Hjw Hsz =>
  [//|a s0] _ Huniq Hws_gt1 Hjw Hsz.
set s := a :: s0.
set m := mm_pos s.
have Hm : m < size s by apply: mm_pos_lt.
have Hs_ne : s <> [::] by discriminate.
have Hm' : mm_pos (psi j s) = m
  by apply: mm_pos_psi_eq.
have Hpsi_ne : psi j s <> [::].
  by move=> E; move: Hjw;
     rewrite -(size_psi j) E.
have [a' [s0' Hpsi_eq]] :
  exists a' s0', psi j s = a' :: s0'.
  by case: (psi j s) Hpsi_ne =>
     [//|x y] _; exists x, y.
have Hm'c : mm_pos (a' :: s0') = m
  by rewrite -Hpsi_eq.
rewrite Hpsi_eq
  (window_size_cons i a' s0') Hm'c.
rewrite (window_size_cons i a s0) -/m.
case: (ltngtP i m) =>
  [Him | Hmi | Hieqm].
- case: (ltngtP j m) =>
    [Hjm | Hmj | Hjeqm].
  + abstract (
    rewrite -Hpsi_eq
      (take_mm_psi Hs_ne Huniq Hws_gt1 Hjm);
    apply: IH;
    [ rewrite (size_takel (ltnW Hm));
      exact: leq_trans Hm Hsz
    | by apply: (subseq_uniq (s2:=s)); [exact: take_subseq | ]
    ]).
  + by rewrite -Hpsi_eq
       (@take_psi m j s (ltnW Hmj)).
  + by rewrite -Hpsi_eq Hjeqm
       (@take_psi m m s (leqnn m)).
- case: (ltngtP j m) =>
    [Hjm | Hmj | Hjeqm].
  + abstract (
    suff -> : drop m.+1 (a' :: s0') =
      drop m.+1 (a :: s0) by [];
    rewrite -Hpsi_eq;
    apply: drop_psi_above;
    apply: leq_trans
      (window_fits_left Hs_ne Hjm) _;
    exact: leqnSn).
  + abstract (
    suff -> : drop m.+1 (a' :: s0') =
      psi (j - m - 1)
        (drop m.+1 (a :: s0));
    [ apply: IH;
      [ rewrite size_drop;
        apply: (leq_trans (leq_sub2r _ Hsz));
        exact: leq_subr
      | by apply: (subseq_uniq (s2:=s));
           [exact: drop_subseq | ]
      ]
    | by rewrite -Hpsi_eq
       (drop_mm_psi Hs_ne Huniq Hws_gt1 Hmj)
    ]).
  + subst j.
    have Hws_m : window_size m s = size s - m.
      by rewrite (window_size_cons m a s0)
         -/m ltnn eqxx.
    have Hws_drop : 1 < size (drop m s).
      by rewrite size_drop -Hws_m.
    have Hdm_ne : drop m s <> [::].
      by case: (drop m s) Hws_drop.
    have Huniq_dm : uniq (drop m s) by exact: drop_uniq.
    have Hmm_drop : mm_pos (drop m s) = 0
      by exact: mm_pos_drop_mm.
    have Hpsi_m_eq : psi m s =
      take m s ++ rank_shift_seq (drop m s).
      rewrite /psi.
      have Hwa_m : window_at m s = drop m s.
        rewrite (window_at_cons m a s0)
          -/m ltnn eqxx //.
      rewrite Hwa_m Hws_m.
      by rewrite subnKC ?drop_size ?cats0
         // ltnW.
    have Him' : 0 < i - m
      by rewrite subn_gt0.
    have Hdrop_psi :
      drop m.+1 (a' :: s0') =
      behead (rank_shift_seq (drop m s)).
      rewrite -Hpsi_eq Hpsi_m_eq.
      rewrite drop_cat size_take Hm.
      have -> : m.+1 < m = false
        by rewrite ltnNge leqnSn.
      by rewrite /= subSnn drop1.
    have Hdrop_orig :
      drop m.+1 (a :: s0) =
      behead (drop m s).
      by rewrite /s -drop1 drop_drop add1n.
    rewrite Hdrop_psi Hdrop_orig.
    apply: window_size_order_iso.
    * by rewrite !size_behead
         size_rank_shift_seq2.
    * rewrite -drop1;
      apply: (subseq_uniq (drop_subseq _ 1));
      by rewrite (perm_uniq
        (rank_shift_perm_eq _)).
    * rewrite -drop1;
      exact: (subseq_uniq (drop_subseq _ 1)).
    * move: Hdm_ne Hmm_drop Huniq_dm Hws_drop.
      case: (drop m s) => [//|dm_h dm_t] _ Hmm_drop
        Huniq_dm Hws_drop.
      move=> p q Hp Hq.
      have Hws_gt1_dm : 1 < window_size 0 (dm_h :: dm_t)
        by rewrite (window_size_cons 0 dm_h dm_t)
           Hmm_drop ltnn eqxx.
      have Hhead_ext :
        (head 0 (dm_h :: dm_t) ==
        nth 0 (sort leq (dm_h :: dm_t)) 0) ||
        (head 0 (dm_h :: dm_t) ==
        nth 0 (sort leq (dm_h :: dm_t))
        (size (dm_h :: dm_t)).-1).
        have H := window_head_extremum Huniq_dm Hws_gt1_dm.
        have Hwat : window_at 0 (dm_h :: dm_t) = dm_h :: dm_t
          by rewrite (window_at_cons 0 dm_h dm_t) Hmm_drop
             ltnn eqxx drop0.
        move: H; rewrite Hwat => H; exact: H.
      have Hp1 : p.+1 < size (dm_h :: dm_t)
        by move: Hp; rewrite size_behead
           size_rank_shift_seq2 ltn_predRL.
      have Hq1 : q.+1 < size (dm_h :: dm_t)
        by move: Hq; rewrite size_behead
           size_rank_shift_seq2 ltn_predRL.
      rewrite -[behead (rank_shift_seq _)]
        (drop1 (rank_shift_seq (dm_h :: dm_t))).
      rewrite -[behead (dm_h :: dm_t)](drop1 (dm_h :: dm_t)).
      rewrite !nth_drop.
      have H := rank_shift_preserves_interior_order
        Huniq_dm Hws_drop Hhead_ext
        (ltn0Sn q) (ltn0Sn p) Hq1 Hp1.
      by rewrite -H.
- by rewrite -Hpsi_eq size_psi.
Qed.

Opaque window_size_psi.

(* Window-at stability: psi_j preserves window_at at position i              *)
(* when the windows at i and j are disjoint (i + ws_i <= j).                 *)
Lemma window_at_psi_disjoint i j w :
  uniq w ->
  i + window_size i w <= j ->
  window_at i (psi j w) = window_at i w.
Proof.
move=> Hu Hdisj.
have [Hi | Hi] := leqP (size w) i.
  by rewrite /window_at !drop_oversize ?size_psi.
rewrite /window_at (window_size_psi j i Hu).
set ws := window_size i w.
apply: (@eq_from_nth _ 0).
  by rewrite !size_take !size_drop size_psi.
move=> k Hk.
have Hws_le : ws <= size w - i
  by apply: window_size_bound.
have Hksz : k < ws.
  apply: leq_trans Hk _.
  rewrite size_take size_drop size_psi.
  exact: geq_minl.
have Hk_wi : k < size w - i
  by apply: leq_trans Hksz Hws_le.
rewrite !nth_take ?nth_drop //.
  apply: nth_psi_left.
  apply: leq_trans _ Hdisj.
  by rewrite ltn_add2l.
Qed.

(* Disjoint commutativity (WLOG i + ws_i <= j).                              *)
Lemma psi_comm_disjoint_lr i j (w : seq nat) :
  uniq w ->
  i + window_size i w <= j ->
  psi i (psi j w) = psi j (psi i w).
Proof.
move=> Hu Hdisj.
apply: (@eq_from_nth _ 0).
  by rewrite !size_psi.
move=> k Hk; rewrite !size_psi in Hk.
set wsi := window_size i w.
set wsj := window_size j w.
have [Hi | Hi] := leqP (size w) i.
  have Hi' : size (psi j w) <= i by rewrite size_psi.
  by rewrite (psi_id_oor Hi') (psi_id_oor Hi).
have Hwsi_le : i + wsi <= size w.
  have Hbd := window_size_bound i w.
  rewrite -(subnKC (ltnW Hi)).
  by rewrite leq_add2l.
have [Hj | Hj] := leqP (size w) j.
  have Hj' : size (psi i w) <= j by rewrite size_psi.
  by rewrite (psi_id_oor Hj) (psi_id_oor Hj').
have Hwsj_le : j + wsj <= size w.
  have Hbd := window_size_bound j w.
  rewrite -(subnKC (ltnW Hj)).
  by rewrite leq_add2l.
have Hws_ji : window_size j (psi i w) = wsj
  by apply: window_size_psi.
have Hws_ij : window_size i (psi j w) = wsi
  by apply: window_size_psi.
(* 5-region case split *)
have [Hki | Hik] := ltnP k i.
  (* k < i: both sides = nth 0 w k *)
  have Hkj : k < j.
    exact: leq_trans Hki
      (leq_trans (leq_addr wsi i) Hdisj).
  by rewrite !nth_psi_left.
have [Hk_iws | Hk_iws] := ltnP k (i + wsi).
  (* i <= k < i + wsi: inside W_i *)
  have Hkj : k < j by apply: leq_trans Hk_iws Hdisj.
  have Hi' : i < size (psi j w) by rewrite size_psi.
  have Hk2' : k < i + window_size i (psi j w)
    by rewrite Hws_ij.
  rewrite (nth_psi_inside Hi' Hik Hk2').
  rewrite (window_at_psi_disjoint Hu Hdisj).
  rewrite nth_psi_left //.
  by rewrite (nth_psi_inside Hi Hik Hk_iws).
have [Hk3 | Hk3] := ltnP k j.
  (* i + wsi <= k < j: both sides = nth 0 w k *)
  have Hk_iws' : i + window_size i (psi j w) <= k
    by rewrite Hws_ij.
  rewrite (nth_psi_right Hk_iws') nth_psi_left //.
  by rewrite nth_psi_left // nth_psi_right.
have [Hk4 | Hk4] := ltnP k (j + wsj).
  (* j <= k < j + wsj: inside W_j *)
  have Hki : i + wsi <= k
    by apply: leq_trans Hdisj Hk3.
  rewrite nth_psi_right ?Hws_ij //.
  rewrite (@nth_psi_inside j w k) //.
  rewrite (@nth_psi_inside j (psi i w) k)
    ?size_psi ?Hws_ji //.
  congr (nth 0 (rank_shift_seq _) _).
  rewrite /window_at Hws_ji.
  apply: (@eq_from_nth _ 0).
    by rewrite !size_take !size_drop size_psi.
  move=> m' Hm'.
  have Hwsj_le' : wsj <= size w - j
    by apply: window_size_bound.
  have Hm'sz : m' < wsj.
    apply: leq_trans Hm' _.
    rewrite size_take size_drop.
    exact: geq_minl.
  have Hm'wd : m' < size w - j
    by apply: leq_trans Hm'sz Hwsj_le'.
  rewrite !nth_take ?nth_drop //.
  rewrite nth_psi_right //.
  by apply: (leq_trans Hdisj); apply: leq_addr.
(* j + wsj <= k: both sides = nth 0 w k *)
have Hki' : i + wsi <= k.
  have Hjk : j <= k := leq_trans (leq_addr wsj j) Hk4.
  exact: leq_trans Hdisj Hjk.
have Hk_ij : i + window_size i (psi j w) <= k
  by rewrite Hws_ij.
have Hk_ji : j + window_size j (psi i w) <= k
  by rewrite Hws_ji.
by rewrite (nth_psi_right Hk_ij) (nth_psi_right Hk4)
           (nth_psi_right Hk_ji) (nth_psi_right Hki').
Qed.

Opaque psi_comm_disjoint_lr.

Lemma psi_comm_disjoint : forall i j (w : seq nat),
  uniq w ->
  (i + window_size i w <= j \/ j + window_size j w <= i) ->
  psi i (psi j w) = psi j (psi i w).
Proof.
move=> i j w Hu [Hdisj | Hdisj].
  by apply: psi_comm_disjoint_lr.
by symmetry; apply: psi_comm_disjoint_lr.
Qed.

(* Non-triviality: positions 2 and 6 have disjoint windows [2,5) and [6,8). *)
Example psi_comm_disjoint_ex :
  psi 2 (psi 6 [:: 3; 1; 4; 7; 5; 9; 2; 6]) =
  psi 6 (psi 2 [:: 3; 1; 4; 7; 5; 9; 2; 6]).
Proof. by []. Qed.

(* ----- M3.3 Nested case: window stability under ancestor psi ------------- *)
(* When W_j is properly contained in W_i (i.e., vertex j is in the right     *)
(* subtree of vertex i), applying psi_i preserves the window geometry at j:  *)
(* same size, and the window labels are the pointwise rank-shift of the       *)
(* original. This is because psi_i's rank-shift, restricted to W_j's         *)
(* positions, is a monotone map (no rank wrap-around occurs within W_j since  *)
(* the wrap-around element is at position i, outside W_j). Therefore mm_pos  *)
(* is preserved at every recursive level within W_j.                          *)
(*                                                                            *)
(* Justification: M3_COMMUTATIVITY_INFORMAL.md section 3.2 (Claim 3.2).      *)
(* Also depends on M2_SUBTASKS.md T4-T5 (mm_pos stability / window           *)
(* stability), which are the mathematical crux of both M2 and M3.            *)

Lemma window_size_psi_ancestor : forall i j (w : seq nat),
  uniq w ->
  i < j -> j + window_size j w <= i + window_size i w ->
  window_size j (psi i w) = window_size j w.
Proof. move=> i j w Hu _ _; exact: window_size_psi. Qed.

Opaque window_size_psi_ancestor.

Example window_size_psi_ancestor_ex :
  let w := [:: 3; 1; 4; 7; 5; 9; 2; 6] in
  window_size 5 (psi 1 w) = window_size 5 w.
Proof. by []. Qed.

(* ----- M3.4 Nested commutativity ----------------------------------------- *)
(* When W_j is properly contained in W_i, the commutativity                   *)
(* psi_i(psi_j(w)) = psi_j(psi_i(w)) reduces to the algebraic identity      *)
(* RS_i(RS_j(x)) = RS_j(RS_i(x)) for labels x in W_j. This holds because:   *)
(* 1) psi_j only modifies W_j, which is inside W_i, so psi_j preserves the  *)
(*    multiset of W_i (hence sort and shift direction are the same);          *)
(* 2) psi_i's rank-shift is monotone on W_j (no wrap-around), so RS_i        *)
(*    acts as a fixed shift on r_j-ranks within W_j;                          *)
(* 3) RS_i(RS_j(x)) = S_j[(r_j(x) + delta_j + c) mod ws_j]                  *)
(*    RS_j(RS_i(x)) = S_j[(r_j(x) + c + delta_j) mod ws_j]                  *)
(*    which are equal by commutativity of addition mod ws_j.                  *)
(*                                                                            *)
(* Justification: M3_COMMUTATIVITY_INFORMAL.md sections 3.3-3.6.             *)
(* The proof combines window_size_psi_ancestor, the perm_eq preservation     *)
(* of sort order, and modular arithmetic. The assembly is ~25 LOC but needs  *)
(* all the window-stability sub-lemmas.                                       *)

(* Helper: sort commutes with an order-preserving injection.             *)
Lemma sort_map_mono (f : nat -> nat) (L : seq nat) :
  uniq L ->
  (forall x y, x \in L -> y \in L ->
    (x < y) = (f x < f y)) ->
  sort leq (map f L) = map f (sort leq L).
Proof.
move=> Hu Hmon.
have Hperm : perm_eq (map f L)
  (map f (sort leq L)).
  rewrite perm_sym; apply: perm_map;
    by rewrite perm_sort.
suff Hsorted : sorted leq (map f (sort leq L)).
  have Heq : sort leq (map f L) =
    sort leq (map f (sort leq L)).
    apply/perm_sortP => //.
    - by move=> ?; exact: leq_total.
    - exact: leq_trans.
    - exact: anti_leq.
  by rewrite Heq (sorted_sort leq_trans Hsorted).
apply/(sortedP 0) => i Hi.
have Hsz : i.+1 < size (sort leq L).
  by rewrite size_map in Hi.
rewrite (nth_map 0); last exact: ltnW Hsz.
rewrite (nth_map 0) //.
have Hx : nth 0 (sort leq L) i \in L
  by rewrite -(mem_sort leq); apply: mem_nth;
     exact: ltnW Hsz.
have Hy : nth 0 (sort leq L) i.+1 \in L
  by rewrite -(mem_sort leq); apply: mem_nth.
have /sortedP := sort_sorted leq_total L.
move=> /(_ 0 i Hsz).
rewrite leq_eqVlt => /orP [/eqP -> | Hlt].
  by rewrite leqnn.
by apply: ltnW; rewrite -Hmon.
Qed.

(* Helper: index commutes with locally injective maps.                    *)
Lemma index_map_inj_in (f : nat -> nat) (s : seq nat)
    (x : nat) :
  uniq s -> {in s &, injective f} -> x \in s ->
  index (f x) (map f s) = index x s.
Proof.
elim: s => [//|a s IH].
rewrite cons_uniq => /andP [Ha_notin Hu] Hinj.
rewrite in_cons => /orP [/eqP -> | Hx].
  by rewrite /= !eqxx.
have Hax : a != x.
  by apply/eqP => Hax; rewrite Hax Hx in Ha_notin.
have Hfax : f a != f x.
  apply/eqP => Hfax.
  have Hx' : x \in a :: s by rewrite in_cons Hx orbT.
  by move: Hax; rewrite (Hinj a x (mem_head _ _) Hx' Hfax) eqxx.
rewrite /= (negbTE Hfax) (negbTE Hax); congr _.+1.
apply: IH => //.
move=> u v Hu_in Hv_in; apply: Hinj;
  by rewrite in_cons ?Hu_in ?Hv_in orbT.
Qed.

(* Helper: monotonicity implies local injectivity.                       *)
Lemma mono_inj_in (f : nat -> nat) (L : seq nat) :
  uniq L ->
  (forall x y, x \in L -> y \in L ->
    (x < y) = (f x < f y)) ->
  {in L &, injective f}.
Proof.
move=> Hu Hmon x y Hx Hy Hfxy.
case: (ltngtP x y) => // Hlt.
- have : f x < f y by rewrite -Hmon.
  by rewrite Hfxy ltnn.
- have : f y < f x by rewrite -Hmon.
  by rewrite Hfxy ltnn.
Qed.

(* Helper: rank_shift_seq commutes with a monotone injection.             *)
Lemma rank_shift_map_comm (f : nat -> nat) (L : seq nat) :
  uniq L -> 1 < size L ->
  (forall x y, x \in L -> y \in L ->
    (x < y) = (f x < f y)) ->
  rank_shift_seq (map f L) = map f (rank_shift_seq L).
Proof.
move=> Hu Hsz Hmon.
have Hinj_in := mono_inj_in Hu Hmon.
have Hu_fL : uniq (map f L)
  by rewrite map_inj_in_uniq.
have Hsz_fL : 1 < size (map f L) by rewrite size_map.
have Hsort := sort_map_mono Hu Hmon.
have Hhead : head 0 (map f L) = f (head 0 L)
  by case: (L) Hsz => [//|a s] _.
have Hdelta : (head 0 (map f L) ==
  nth 0 (sort leq (map f L)) 0) =
  (head 0 L == nth 0 (sort leq L) 0).
  rewrite Hsort Hhead (nth_map 0);
    last by rewrite size_sort; apply: ltnW.
  apply/eqP/eqP.
  - move/(Hinj_in _ _ _ _) => -> //.
    + case: (L) Hsz => [//|x s0] _; exact: mem_head.
    + rewrite -(mem_sort leq).
      apply: mem_nth; rewrite size_sort; exact: ltnW.
  - by move=> ->.
apply: (@eq_from_nth _ 0).
  by rewrite size_rank_shift_seq2 !size_map size_rank_shift_seq2.
move=> n Hn.
have Hn_L : n < size L.
  move: Hn; rewrite size_rank_shift_seq2 size_map //.
set x := nth 0 L n.
have Hx : x \in L by rewrite /x mem_nth.
rewrite (nth_rank_shift_seq Hu_fL Hsz_fL);
  last by rewrite size_map.
have Hrhs : nth 0 (map f (rank_shift_seq L)) n =
    f (nth 0 (rank_shift_seq L) n).
  apply: nth_map.
  by rewrite size_rank_shift_seq2.
have Hnth_fL : nth 0 (map f L) n = f x
  by rewrite /x (nth_map 0).
rewrite Hrhs (nth_rank_shift_seq Hu Hsz Hn_L) /=.
rewrite Hdelta size_map Hsort Hnth_fL.
have Hx_srt : x \in sort leq L
  by rewrite mem_sort.
have Hidx_srt : index x (sort leq L) < size L
  by rewrite -(size_sort leq) index_mem.
have Hmod : (index x (sort leq L) +
  (if head 0 L == nth 0 (sort leq L) 0
   then (size L).-1 else 1)) %% size L < size L.
  by rewrite ltn_mod; apply: ltnW.
have Hu_srt : uniq (sort leq L) by rewrite sort_uniq.
have Hinj_srt : {in sort leq L &, injective f}.
  move=> u v Hu_in Hv_in.
  apply: Hinj_in;
    by rewrite -(mem_sort leq).
rewrite (index_map_inj_in Hu_srt Hinj_srt Hx_srt).
by rewrite (nth_map 0) // size_sort.
Qed.

Opaque sort_map_mono.
Opaque index_map_inj_in.
Opaque mono_inj_in.
Opaque rank_shift_map_comm.

(* Helper: psi commutes with any comparison-preserving map.               *)
Lemma psi_map_comm (f : nat -> nat) (s : seq nat) k :
  uniq s ->
  (forall x y, x \in s -> y \in s ->
    (x < y) = (f x < f y)) ->
  map f (psi k s) = psi k (map f s).
Proof.
move=> Hu Hmon.
have Hinj_in := mono_inj_in Hu Hmon.
rewrite /psi.
set ws := window_size k s.
set wa := window_at k s.
have Hu_fs : uniq (map f s)
  by rewrite map_inj_in_uniq.
have Hsz_eq : size (map f s) = size s
  by rewrite size_map.
have Hord : forall p q, p < size s -> q < size s ->
  (nth 0 s p < nth 0 s q) =
  (nth 0 (map f s) p < nth 0 (map f s) q).
  move=> p q Hp Hq.
  rewrite (nth_map 0) // (nth_map 0) //.
  apply: Hmon; exact: mem_nth.
have Hws' : window_size k (map f s) = ws.
  apply: window_size_order_iso.
  - by rewrite size_map.
  - exact: Hu_fs.
  - exact: Hu.
  - move=> p q Hp Hq; rewrite size_map in Hp Hq.
    by rewrite -Hord.
have Hwa' : window_at k (map f s) = map f wa.
  by rewrite /window_at /wa Hws' -map_drop -map_take.
have Hrs : rank_shift_seq (map f wa) =
  map f (rank_shift_seq wa).
  have [Htriv | Hnt] := leqP ws 1.
    have Hsz_wa : size wa <= 1.
      rewrite /wa /window_at size_take size_drop.
      exact: leq_trans (geq_minl _ _) Htriv.
    case Hwa0 : wa => [|a [|b t]].
    - by rewrite /rank_shift_seq /=.
    - by rewrite /rank_shift_seq /=.
    - by move: Hsz_wa; rewrite Hwa0 /=.
  have Hu_wa : uniq wa.
    rewrite /wa /window_at.
    exact: take_uniq (drop_uniq _ Hu).
  have Hsz_wa : 1 < size wa.
    rewrite /wa /window_at size_take size_drop.
    rewrite ltn_min.
    apply/andP; split => //.
    exact: leq_trans Hnt (window_size_bound k s).
  apply: rank_shift_map_comm => //.
  move=> x y Hx Hy; apply: Hmon;
    [ rewrite /wa /window_at in Hx;
      exact: mem_drop (mem_take Hx)
    | rewrite /wa /window_at in Hy;
      exact: mem_drop (mem_take Hy) ].
rewrite Hws' Hwa' Hrs.
by rewrite !map_cat -map_take -map_drop.
Qed.

Opaque psi_map_comm.

(* Key commutativity lemma: rank_shift_seq commutes with psi at           *)
(* interior positions. When mm_pos d = 0 and k > 0:                       *)
(*   rank_shift_seq (psi k d) = psi k (rank_shift_seq d).                *)
Lemma rank_shift_psi_comm d k :
  uniq d -> 1 < size d -> mm_pos d = 0 -> 0 < k ->
  rank_shift_seq (psi k d) = psi k (rank_shift_seq d).
Proof.
move=> Hu Hsz Hmm Hk0.
have Hd_ne : d <> [::] by case: (d) Hsz.
have Hperm := psi_perm_eq k d.
have Hsort_psi : sort leq (psi k d) = sort leq d.
  by apply/perm_sortP => //;
     [move=> ?; exact: leq_total | exact: leq_trans
      | exact: anti_leq].
have Hhead_psi : head 0 (psi k d) = head 0 d.
  by rewrite -(@nth0 _ 0) -(@nth0 _ 0 d);
     apply: nth_psi_left.
have [a [t Hd]] : exists a t, d = a :: t.
  by case: (d) Hsz => [|a t] //; exists a, t.
have Ha : a = head 0 d by rewrite Hd.
have Ht : t = behead d by rewrite Hd.
set rs := fun x => nth 0 (sort leq d)
  ((index x (sort leq d) +
    (if head 0 d == nth 0 (sort leq d) 0
     then (size d).-1 else 1)) %% size d).
have Hrs_d : rank_shift_seq d = map rs d
  by rewrite (rank_shift_seqE Hu Hsz).
have Hrs_psi :
  rank_shift_seq (psi k d) = map rs (psi k d).
  have Hu_psi : uniq (psi k d) by rewrite (perm_uniq Hperm).
  have Hsz_psi : 1 < size (psi k d)
    by rewrite (perm_size Hperm).
  rewrite (rank_shift_seqE Hu_psi Hsz_psi).
  by rewrite Hsort_psi Hhead_psi (perm_size Hperm).
have Hhead_ext : (head 0 d ==
  nth 0 (sort leq d) 0) ||
  (head 0 d == nth 0 (sort leq d) (size d).-1).
  have Hmm_at : mm_pos (a :: t) = 0 by rewrite -Hd.
  have Hwsz0 : 1 < window_size 0 d.
    rewrite Hd (window_size_cons 0 a t) Hmm_at ltnn eqxx subn0 /=.
    by rewrite Hd in Hsz.
  have H := window_head_extremum Hu Hwsz0.
  have Hwat0 : window_at 0 d = d.
    rewrite /window_at Hd (window_size_cons 0 a t).
    by rewrite Hmm_at ltnn eqxx subn0 drop0 take_size -Hd.
  move: H; rewrite Hwat0 /=; exact: id.
have Hrs_mono : forall x y,
  x \in t -> y \in t ->
  (x < y) = (rs x < rs y).
  move=> x y Hx Hy.
  have Hx_d : x \in d by rewrite Hd in_cons Hx orbT.
  have Hy_d : y \in d by rewrite Hd in_cons Hy orbT.
  have Hpx : 0 < index x d.
    rewrite Hd /=; case: eqP => [Hax|_] //.
    subst x; move: Hu; rewrite Hd /= => /andP [Hna _].
    by rewrite Hx in Hna.
  have Hpy : 0 < index y d.
    rewrite Hd /=; case: eqP => [Hay|_] //.
    subst y; move: Hu; rewrite Hd /= => /andP [Hna _].
    by rewrite Hy in Hna.
  have Hidx : index x d < size d by rewrite index_mem.
  have Hidy : index y d < size d by rewrite index_mem.
  have Hnthx : nth 0 d (index x d) = x
    by apply: nth_index.
  have Hnthy : nth 0 d (index y d) = y
    by apply: nth_index.
  have Hrio := rank_shift_preserves_interior_order
    Hu Hsz Hhead_ext Hpy Hpx Hidy Hidx.
  rewrite Hnthx Hnthy in Hrio.
  have Hnthrsx :
    nth 0 (rank_shift_seq d) (index x d) = rs x.
    by rewrite (nth_rank_shift_seq Hu Hsz Hidx)
       nth_index.
  have Hnthrsy :
    nth 0 (rank_shift_seq d) (index y d) = rs y.
    by rewrite (nth_rank_shift_seq Hu Hsz Hidy)
       nth_index.
  by rewrite Hnthrsx Hnthrsy in Hrio.
rewrite Hrs_psi Hrs_d.
(* Cannot use psi_map_comm: rs wraps the head, so is NOT monotone on all of d.
   Instead, unfold psi and apply rank_shift_map_comm only on the window,
   where all elements lie in the tail t and rs IS monotone. *)
have Hpsi0_eq : [seq rs i | i <- d] = psi 0 d
  by rewrite -Hrs_d (psi_0_eq Hmm Hsz).
have Hws_eq : window_size k [seq rs i | i <- d] = window_size k d
  by rewrite Hpsi0_eq window_size_psi.
rewrite /psi Hws_eq.
set ws := window_size k d.
set wa := window_at k d.
have Hwa_eq : window_at k [seq rs i | i <- d] = [seq rs i | i <- wa]
  by rewrite /window_at /wa Hws_eq -map_drop -map_take.
rewrite Hwa_eq !map_cat -!map_take -!map_drop.
congr (_ ++ _ ++ _).
have Hwa_sub_t : forall z, z \in wa -> z \in t.
  move=> z; rewrite /wa /window_at => /mem_take.
  by rewrite Hd -(prednK Hk0) /= => /mem_drop.
have [Htriv | Hnt] := leqP ws 1.
  have Hsz_wa : size wa <= 1.
    rewrite /wa /window_at size_take size_drop.
    exact: leq_trans (geq_minl _ _) Htriv.
  by case: (wa) Hsz_wa => [|? [|??]] //=; rewrite /rank_shift_seq.
have Hu_wa : uniq wa by rewrite /wa /window_at; exact: take_uniq (drop_uniq _ Hu).
have Hsz_wa : 1 < size wa.
  rewrite /wa /window_at size_take size_drop ltn_min.
  apply/andP; split => //.
  exact: leq_trans Hnt (window_size_bound k d).
symmetry; apply: rank_shift_map_comm => //.
by move=> x0 y0 Hx0 Hy0; apply: Hrs_mono; apply: Hwa_sub_t.
Qed.

Opaque rank_shift_psi_comm.

Lemma psi_comm_nested :
  forall i j (w : seq nat),
  uniq w ->
  i < j ->
  j + window_size j w <= i + window_size i w ->
  psi i (psi j w) = psi j (psi i w).
Proof.
suff Hgen : forall n i j w, size w <= n ->
  uniq w ->
  i < j ->
  j + window_size j w <= i + window_size i w ->
  psi i (psi j w) = psi j (psi i w).
  by move=> i j w;
     apply: (Hgen (size w)); rewrite ?leqnn.
elim=> [|n IH] i j w Hsz Huniq Hij Hnest.
  by move: Hsz; rewrite leqn0 =>
     /eqP/size0nil ->.
have [Htriv_i | Hws_i_gt1] :=
  leqP (window_size i w) 1.
  have Htriv_ij : window_size i (psi j w) <= 1
    by rewrite window_size_psi.
  by rewrite (psi_id_trivial Htriv_ij) (psi_id_trivial Htriv_i).
have [Htriv_j | Hws_j_gt1] :=
  leqP (window_size j w) 1.
  have Htriv_ji : window_size j (psi i w) <= 1
    by rewrite window_size_psi.
  by rewrite (psi_id_trivial Htriv_ji) (psi_id_trivial Htriv_j).
have Hiw := ws_lt_size Hws_i_gt1.
have Hjw := ws_lt_size Hws_j_gt1.
have Hw_ne : w <> [::] by case: (w) Hiw.
case: (w) Hw_ne Huniq Hws_i_gt1 Hws_j_gt1
  Hiw Hjw Hsz Hij Hnest =>
  [//|a s0] _ Huniq Hws_i Hws_j Hiw Hjw
  Hsz Hij Hnest.
set s := a :: s0.
set m := mm_pos s.
have Hm : m < size s by apply: mm_pos_lt.
have Hs_ne : s <> [::] by discriminate.
have Hm_pi : mm_pos (psi i s) = m
  by apply: mm_pos_psi_eq.
have Hm_pj : mm_pos (psi j s) = m
  by apply: mm_pos_psi_eq.
have Huniq_pi : uniq (psi i s)
  by rewrite (perm_uniq (psi_perm_eq i s)).
have Huniq_pj : uniq (psi j s)
  by rewrite (perm_uniq (psi_perm_eq j s)).
case: (ltngtP i m) => [Him | Hmi | Hieqm].
- (* i < m *)
  have Hjm : j < m.
    have Hfit := window_fits_left Hs_ne Him.
    apply: leq_trans _ (leq_trans Hnest Hfit).
    by rewrite -addn1 leq_add2l ltnW.
  have Htmj : take m (psi j s) =
    psi j (take m s)
    by exact: take_mm_psi.
  have Htmi : take m (psi i s) =
    psi i (take m s)
    by exact: take_mm_psi.
  have Hdj : drop m.+1 (psi j s) = drop m.+1 s.
    apply: drop_psi_above.
    exact: leq_trans
      (window_fits_left Hs_ne Hjm) (leqnSn _).
  have Hdi : drop m.+1 (psi i s) = drop m.+1 s.
    apply: drop_psi_above.
    exact: leq_trans
      (window_fits_left Hs_ne Him) (leqnSn _).
  apply: (@eq_from_nth _ 0);
    first by rewrite !size_psi.
  move=> k Hk; rewrite !size_psi in Hk.
  have [Hkm | Hkm] := ltnP k m.
    have Hpj_ne : psi j s <> [::].
      by move=> E; move: Hk; rewrite -(size_psi j) E.
    have [a' [s0' Hpj_eq]] :
      exists a' s0', psi j s = a' :: s0'.
      by case: (psi j s) Hpj_ne =>
         [//|x y] _; exists x, y.
    have Hm_pj'' : mm_pos (a' :: s0') = m
      by rewrite -Hpj_eq.
    have Hws_i_pj :
      1 < window_size i (psi j s)
      by rewrite window_size_psi.
    have Him' : i < mm_pos (psi j s)
      by rewrite Hm_pj.
    have Hpi_ne : psi i s <> [::].
      by move=> E; move: Hk; rewrite -(size_psi i) E.
    have Hws_j_pi :
      1 < window_size j (psi i s)
      by rewrite window_size_psi.
    have Hjm' : j < mm_pos (psi i s)
      by rewrite Hm_pi.
    have Hlhs_k : nth 0 (psi i (psi j s)) k =
      nth 0 (psi i (psi j (take m s))) k.
      rewrite -(@nth_take m _ 0 k Hkm (psi i (psi j s))).
      rewrite -{1}Hm_pj (take_mm_psi
        Hpj_ne Huniq_pj Hws_i_pj Him').
      by rewrite Hm_pj Htmj.
    have Hrhs_k : nth 0 (psi j (psi i s)) k =
      nth 0 (psi j (psi i (take m s))) k.
      rewrite -(@nth_take m _ 0 k Hkm (psi j (psi i s))).
      rewrite -{1}Hm_pi (take_mm_psi
        Hpi_ne Huniq_pi Hws_j_pi Hjm').
      by rewrite Hm_pi Htmi.
    rewrite Hlhs_k Hrhs_k.
    have Huniq_tm : uniq (take m s) by exact: take_uniq.
    have Hsz_tm : size (take m s) <= n.
      rewrite (size_takel (ltnW Hm)).
      exact: leq_trans Hm Hsz.
    have Hws_i_tm :
      window_size i (take m s) =
      window_size i s.
      by rewrite (window_size_cons i a s0)
         -/m Him.
    have Hws_j_tm :
      window_size j (take m s) =
      window_size j s.
      by rewrite (window_size_cons j a s0)
         -/m Hjm.
    have Hnest_tm :
      j + window_size j (take m s) <=
      i + window_size i (take m s)
      by rewrite Hws_i_tm Hws_j_tm.
    have := IH i j (take m s) Hsz_tm
      Huniq_tm Hij Hnest_tm.
    by move=> ->.
  have [Hkm' | Hkm'] := eqVneq k m.
    subst k.
    have Hfit_i : i + window_size i s <= m
      by exact: window_fits_left Hs_ne Him.
    have Hfit_j : j + window_size j s <= m
      by exact: window_fits_left Hs_ne Hjm.
    rewrite (nth_psi_right (k:=m));
      last by rewrite window_size_psi.
    rewrite (nth_psi_right (k:=m)) //.
    rewrite (nth_psi_right (k:=m));
      last by rewrite window_size_psi.
    by rewrite (nth_psi_right (k:=m)).
  have Hkm'' : m < k
    by rewrite ltn_neqAle eq_sym Hkm' Hkm.
  have Hk_oor_i : i + window_size i s <= k.
    exact: leq_trans
      (window_fits_left Hs_ne Him) Hkm.
  have Hk_oor_j : j + window_size j s <= k.
    exact: leq_trans
      (leq_trans Hnest Hk_oor_i).
  rewrite (nth_psi_right (k:=k));
    last by rewrite window_size_psi.
  rewrite (nth_psi_right (k:=k)) //.
  rewrite (nth_psi_right (k:=k));
    last by rewrite window_size_psi.
  by rewrite (nth_psi_right (k:=k)).
- (* m < i *)
  have Hmj : m < j
    by exact: ltn_trans Hmi Hij.
  apply: (@eq_from_nth _ 0);
    first by rewrite !size_psi.
  move=> k Hk; rewrite !size_psi in Hk.
  have [Hkm | Hkm] := ltnP k m.+1.
    have Hki : k < i
      by exact: leq_trans Hkm Hmi.
    have Hkj : k < j by exact: ltn_trans Hki Hij.
    by rewrite (nth_psi_left _ Hki)
              (nth_psi_left _ Hkj)
              (nth_psi_left _ Hkj)
              (nth_psi_left _ Hki).
  have [Hk_oor | Hk_inr] := leqP (size s) k.
    by rewrite !nth_default ?size_psi.
  have Hpj_ne : psi j s <> [::].
    by move=> E; move: Hjw;
       rewrite -(size_psi j) E.
  have Hws_i_pj :
    1 < window_size i (psi j s)
    by rewrite window_size_psi.
  have Hmi' : mm_pos (psi j s) < i
    by rewrite Hm_pj.
  have Hdpj :
    drop m.+1 (psi i (psi j s)) =
    psi (i - m - 1) (drop m.+1 (psi j s)).
    rewrite -Hm_pj; exact: drop_mm_psi
      Hpj_ne Huniq_pj Hws_i_pj Hmi'.
  have Hdi_pj :
    drop m.+1 (psi j s) =
    psi (j - m - 1) (drop m.+1 s).
    exact: drop_mm_psi
      Hs_ne Huniq Hws_j Hmj.
  have Hpi_ne : psi i s <> [::].
    by move=> E; move: Hiw;
       rewrite -(size_psi i) E.
  have Hws_j_pi :
    1 < window_size j (psi i s)
    by rewrite window_size_psi.
  have Hmj' : mm_pos (psi i s) < j
    by rewrite Hm_pi.
  have Hdpi :
    drop m.+1 (psi j (psi i s)) =
    psi (j - m - 1) (drop m.+1 (psi i s)).
    rewrite -Hm_pi; exact: drop_mm_psi
      Hpi_ne Huniq_pi Hws_j_pi Hmj'.
  have Hdi_pi :
    drop m.+1 (psi i s) =
    psi (i - m - 1) (drop m.+1 s).
    exact: drop_mm_psi
      Hs_ne Huniq Hws_i Hmi.
  have Hlhs :
    nth 0 (psi i (psi j s)) k =
    nth 0 (drop m.+1 (psi i (psi j s)))
      (k - m.+1).
    by rewrite nth_drop addnC subnK.
  have Hrhs :
    nth 0 (psi j (psi i s)) k =
    nth 0 (drop m.+1 (psi j (psi i s)))
      (k - m.+1).
    by rewrite nth_drop addnC subnK.
  rewrite Hlhs Hdpj Hdi_pj
    Hrhs Hdpi Hdi_pi.
  have Huniq_dm : uniq (drop m.+1 s) by exact: drop_uniq.
  have Hsz_dm : size (drop m.+1 s) <= n.
    rewrite size_drop.
    apply: leq_trans (leq_sub2r _ Hsz) _.
    by rewrite subSS; exact: leq_subr.
  set i' := i - m - 1.
  set j' := j - m - 1.
  have Hi'j' : i' < j'.
    rewrite /i' /j' -!subnDA addn1.
    by rewrite (@ltn_sub2rE m.+1 i j Hmi).
  have Hws_i' :
    window_size i' (drop m.+1 s) =
    window_size i s.
    rewrite (window_size_cons i a s0) -/m.
    by rewrite ltnNge (ltnW Hmi) /=
       eq_sym (ltn_eqF Hmi).
  have Hws_j' :
    window_size j' (drop m.+1 s) =
    window_size j s.
    rewrite (window_size_cons j a s0) -/m.
    by rewrite ltnNge (ltnW Hmj) /=
       eq_sym (ltn_eqF Hmj).
  have Hnest' :
    j' + window_size j' (drop m.+1 s) <=
    i' + window_size i' (drop m.+1 s).
    rewrite Hws_i' Hws_j' /i' /j'.
    rewrite -!subnDA !addn1.
    have Hm1_i : m.+1 <= i by exact: Hmi.
    have Hm1_j : m.+1 <= j by exact: Hmj.
    have Hm1_ij : m.+1 <= i + window_size i s.
      exact: leq_trans Hm1_i (leq_addr _ _).
    have Hm1_jj : m.+1 <= j + window_size j s.
      exact: leq_trans Hm1_j (leq_addr _ _).
    rewrite (@addnBAC j m.+1 _ Hm1_j).
    rewrite (@addnBAC i m.+1 _ Hm1_i).
    exact: leq_sub2r _ Hnest.
  have := IH i' j' (drop m.+1 s)
    Hsz_dm Huniq_dm Hi'j' Hnest'.
  move=> ->.
  congr (nth 0 _ _).
- (* i = m *)
  subst i.
  have Hws_m : window_size m s = size s - m
    by rewrite (window_size_cons m a s0)
       -/m ltnn eqxx.
  have Hws_drop : 1 < size (drop m s)
    by rewrite size_drop -Hws_m.
  have Hdm_ne : drop m s <> [::]
    by case: (drop m s) Hws_drop.
  have Huniq_dm : uniq (drop m s) by exact: drop_uniq.
  have Hmm_drop : mm_pos (drop m s) = 0
    by exact: mm_pos_drop_mm.
  have Hpsi_m_eq : psi m s =
    take m s ++ rank_shift_seq (drop m s).
    rewrite /psi.
    have Hwa_m : window_at m s = drop m s.
      rewrite (window_at_cons m a s0)
        -/m ltnn eqxx //.
    rewrite Hwa_m Hws_m.
    by rewrite subnKC ?drop_size ?cats0
       // ltnW.
  have Htm_pj : take m (psi j s) = take m s
    by apply: take_psi; exact: ltnW.
  have Hnth_m_pj :
    nth 0 (psi j s) m = nth 0 s m
    by apply: nth_psi_left.
  have Hdm_pj :
    drop m.+1 (psi j s) =
    psi (j - m - 1) (drop m.+1 s)
    by exact: drop_mm_psi.
  set d := drop m s.
  set j' := j - m - 1.
  have Hdm_pj_full :
    drop m (psi j s) =
    nth 0 s m :: psi j' (behead d).
    have Hm_pj_sz : m < size (psi j s)
      by rewrite size_psi.
    rewrite (drop_nth 0 Hm_pj_sz)
      Hnth_m_pj Hdm_pj.
    congr (_ :: _).
    rewrite /d -drop1 drop_drop add1n.
    done.
  have Hws_m_pj :
    window_size m (psi j s) = size s - m
    by rewrite (window_size_psi _ _ Huniq) Hws_m.
  have Hlhs : psi m (psi j s) =
    take m s ++
    rank_shift_seq (drop m (psi j s)).
    rewrite /psi.
    have Hwa :
      window_at m (psi j s) =
      drop m (psi j s).
      rewrite /window_at Hws_m_pj.
      rewrite take_oversize //
        size_drop size_psi.
      done.
    rewrite Hwa Htm_pj Hws_m_pj.
    rewrite (subnKC (ltnW Hm)).
    by rewrite -(size_psi j s) drop_size cats0.
  have Htm_pm : take m (psi m s) = take m s
    by rewrite Hpsi_m_eq take_cat
       (size_takel (ltnW Hm))
       ltnn subnn take0 cats0.
  have Htm_pj_pm :
    take m (psi j (psi m s)) = take m s.
    by rewrite (@take_psi m j (psi m s)
       (ltnW Hij)) Htm_pm.
  have Hpm_ne : psi m s <> [::].
    by move=> E; move: Hiw;
       rewrite -(size_psi m) E.
  have Hmm_pm : mm_pos (psi m s) = m
    by apply: mm_pos_psi_eq.
  have Hws_j_pm :
    1 < window_size j (psi m s)
    by rewrite (@window_size_psi m j s Huniq).
  have Hmj_pm : mm_pos (psi m s) < j
    by rewrite Hmm_pm.
  have Hdm_pm :
    drop m.+1 (psi j (psi m s)) =
    psi j' (drop m.+1 (psi m s)).
    have Hraw := drop_mm_psi
      Hpm_ne Huniq_pi Hws_j_pm Hmj_pm.
    rewrite Hmm_pm in Hraw.
    rewrite /j'; exact: Hraw.
  have Hdm1_pm :
    drop m.+1 (psi m s) =
    behead (rank_shift_seq d).
    rewrite Hpsi_m_eq drop_cat
      (size_takel (ltnW Hm)).
    have -> : m.+1 < m = false
      by rewrite ltnNge leqnSn.
    by rewrite (subSn (leqnn m)) subnn drop1.
  have Hnth_m_pm :
    nth 0 (psi m s) m =
    head 0 (rank_shift_seq d).
    rewrite Hpsi_m_eq nth_cat
      (size_takel (ltnW Hm)) ltnn.
    by rewrite subnn -nth0.
  have Hnth_m_pj_pm :
    nth 0 (psi j (psi m s)) m =
    nth 0 (psi m s) m.
    by apply: nth_psi_left.
  have Hrhs : psi j (psi m s) =
    take m s ++
    (head 0 (rank_shift_seq d) ::
      psi j' (behead (rank_shift_seq d))).
    apply: (@eq_from_nth _ 0).
      rewrite !size_psi size_cat /=
        size_psi size_behead
        size_rank_shift_seq2 size_drop.
      rewrite (size_takel (ltnW Hm)).
      rewrite prednK; last by rewrite subn_gt0.
      by rewrite subnKC // ltnW.
    move=> k Hk.
    rewrite !size_psi in Hk.
    have Hsz_tm : size (take m s) = m
      by rewrite size_takel // ltnW.
    have [Hkm | Hkm] := ltnP k m.
      have HLk : nth 0 (psi j (psi m s)) k =
          nth 0 (take m s) k
        by rewrite -Htm_pj_pm nth_take.
      rewrite HLk nth_cat Hsz_tm Hkm.
      done.
    have [Hkeqm | Hkgtm] := eqVneq k m.
      subst k.
      rewrite Hnth_m_pj_pm Hnth_m_pm.
      rewrite nth_cat Hsz_tm ltnn subnn /=.
      done.
    have Hkm' : m < k
      by rewrite ltn_neqAle eq_sym
         Hkgtm Hkm.
    have Hrhs_k :
      nth 0 (take m s ++ head 0 (rank_shift_seq d) ::
        psi j' (behead (rank_shift_seq d))) k =
      nth 0 (psi j' (behead (rank_shift_seq d))) (k - m.+1).
      rewrite nth_cat Hsz_tm.
      have -> : k < m = false by rewrite ltnNge Hkm.
      have Hkm_pos : 0 < k - m by rewrite subn_gt0.
      rewrite -(prednK Hkm_pos) /= subnS.
      done.
    rewrite Hrhs_k.
    rewrite -(subnKC Hkm') -nth_drop Hdm_pm.
    by rewrite Hdm1_pm (subnKC Hkm').
  rewrite Hlhs Hrhs.
  congr (_ ++ _).
  rewrite Hdm_pj_full.
  have Hd_head : nth 0 s m = head 0 d.
    by rewrite /d -nth0 nth_drop addn0.
  rewrite Hd_head.
  have Hjm_pos : 0 < j - m
    by rewrite subn_gt0.
  have Hws_jm_d : 1 < window_size (j - m) d.
    have Hjm_ne0 : (j - m == 0) = false
      by apply/negbTE; rewrite -lt0n.
    case Hd' : d => [|a' t'];
      first by case: Hdm_ne.
    rewrite (window_size_cons (j - m) a' t')
      -Hd' Hmm_drop ltn0 /= Hjm_ne0 subn0.
    have Hws_j_eq : window_size j s =
        window_size j' (behead d).
      rewrite (window_size_cons j a s0) -/s.
      have Hjm2 : ~~ (j < m)
        by rewrite -leqNgt ltnW // ltnW.
      have Hjmm2 : (j == m) = false
        by rewrite eq_sym ltn_eqF.
      rewrite (negbTE Hjm2) Hjmm2 /j'.
      rewrite /d -drop1 drop_drop add1n.
      done.
    rewrite drop1 /j' -Hws_j_eq.
    done.
  have Hpsi_jm_d :
    psi (j - m) d =
    head 0 d :: psi j' (behead d).
    have Hd_psi_ne : psi (j - m) d <> [::].
      move=> E; move: Hws_drop.
      by rewrite -(size_psi (j - m) d) -/d E.
    have [h0 [t0 Hd_eq]] : exists h0 t0,
        psi (j - m) d = h0 :: t0.
      case: (psi (j - m) d) Hd_psi_ne => [// |h0 t0 _].
      by exists h0, t0.
    have Hh0 : h0 = head 0 d.
      have Hh0_nth : h0 = nth 0 (psi (j - m) d) 0.
        by rewrite Hd_eq.
      rewrite Hh0_nth.
      by apply: nth_psi_left.
    have Hmm0 : mm_pos d < j - m
      by rewrite Hmm_drop.
    have Hraw := drop_mm_psi
      Hdm_ne Huniq_dm Hws_jm_d Hmm0.
    have Ht0 : t0 = psi j' (behead d).
      have Ht0_eq : t0 = drop 1 (psi (j - m) d).
        by rewrite Hd_eq drop1.
      rewrite Ht0_eq.
      rewrite Hmm_drop in Hraw.
      rewrite Hraw subn0 drop1.
      done.
    by rewrite Hd_eq Hh0 Ht0.
  rewrite -Hpsi_jm_d.
  have Hrsk := @rank_shift_psi_comm d (j - m)
    Huniq_dm Hws_drop Hmm_drop Hjm_pos.
  (* Now: Hrsk : rank_shift_seq (psi (j-m) d) = psi (j-m) (rank_shift_seq d) *)
  rewrite Hrsk.
  (* Goal: psi (j-m) (rank_shift_seq d) = head 0 (rank_shift_seq d) :: psi j' (behead (rank_shift_seq d)) *)
  set rd := rank_shift_seq d.
  have Huniq_rd : uniq rd
    by rewrite /rd (perm_uniq (rank_shift_perm_eq d)).
  have Hrd_sz : 1 < size rd
    by rewrite /rd size_rank_shift_seq2.
  have Hrd_ne : rd <> [::]
    by move=> E; rewrite E /= in Hrd_sz.
  have Hrd_psi0 : rd = psi 0 d.
    rewrite /rd; symmetry; apply: psi_0_eq.
    + exact: Hmm_drop.
    + exact: Hws_drop.
  have Hws_0_d : 1 < window_size 0 d.
    case Hd' : d => [|a' t']; first by case: Hdm_ne.
    by rewrite (window_size_cons 0 a' t') -Hd'
               Hmm_drop ltnn eqxx subn0.
  have Hmm_rd0 : mm_pos rd = 0.
    rewrite Hrd_psi0
      (mm_pos_psi_eq Huniq_dm Hws_0_d
        (ltnW Hws_drop)).
    exact: Hmm_drop.
  have Hmm_rd : mm_pos rd < j - m
    by rewrite Hmm_rd0.
  have Hws_jm_rd : 1 < window_size (j - m) rd.
    rewrite Hrd_psi0 (window_size_psi _ _ Huniq_dm).
    exact: Hws_jm_d.
  have Hrd_psi_ne : psi (j - m) rd <> [::].
    by move=> E; move: Hrd_sz;
       rewrite -(size_psi (j - m) rd) E.
  have [h1 [t1 Hrd_eq]] : exists h1 t1,
      psi (j - m) rd = h1 :: t1.
    case: (psi (j - m) rd) Hrd_psi_ne =>
      [//|h1 t1 _].
    by exists h1, t1.
  have Hh1 : h1 = head 0 rd.
    have Hh1_nth : h1 = nth 0 (psi (j - m) rd) 0
      by rewrite Hrd_eq.
    rewrite Hh1_nth; exact: nth_psi_left.
  have Hraw_rd := drop_mm_psi
    Hrd_ne Huniq_rd Hws_jm_rd Hmm_rd.
  rewrite Hmm_rd0 subn0 in Hraw_rd.
  have Ht1 : t1 = psi j' (behead rd).
    have Ht1_eq : t1 = drop 1 (psi (j - m) rd)
      by rewrite Hrd_eq drop1.
    rewrite Ht1_eq Hraw_rd drop1. done.
  by rewrite Hrd_eq Hh1 Ht1.
Qed.

(* Non-triviality: positions 1 and 5 are nested (W_5 inside W_1). *)
Example psi_comm_nested_ex :
  psi 1 (psi 5 [:: 3; 1; 4; 7; 5; 9; 2; 6]) =
  psi 5 (psi 1 [:: 3; 1; 4; 7; 5; 9; 2; 6]).
Proof. by []. Qed.

(* ----- M3.5 Main theorem: commutativity of psi --------------------------- *)

Theorem psi_comm : forall i j (w : seq nat),
  uniq w -> psi i (psi j w) = psi j (psi i w).
Proof.
move=> i j w Hu.
have [Hij | Hij] := eqVneq i j; first by rewrite Hij.
have [Hi | Hi] := leqP (size w) i.
  rewrite psi_id_oor ?size_psi //.
  by rewrite (psi_id_oor Hi).
have [Hj | Hj] := leqP (size w) j.
  have Hj2 : size (psi i w) <= j by rewrite size_psi.
  by rewrite (psi_id_oor Hj) (psi_id_oor Hj2).
move/eqP in Hij; have Hij' : i <> j by [].
case: (window_trichotomy Hi Hj Hij') => [Hdisj | Hdisj | [[Hn1 Hn2] | [Hn1 Hn2]]].
- by apply: psi_comm_disjoint => //; left.
- by apply: psi_comm_disjoint => //; right.
- by apply: psi_comm_nested.
- by symmetry; apply: psi_comm_nested.
Qed.

(* Non-triviality: nested windows with genuinely different results than id. *)
Example psi_comm_ex :
  psi 1 (psi 5 [:: 3; 1; 4; 7; 5; 9; 2; 6]) =
  psi 5 (psi 1 [:: 3; 1; 4; 7; 5; 9; 2; 6]).
Proof. by vm_compute. Qed.

(* The composed result is not the original (psi genuinely acts). *)
Example psi_comm_nontrivial :
  psi 1 (psi 5 [:: 3; 1; 4; 7; 5; 9; 2; 6]) = [:: 3; 9; 2; 6; 4; 1; 5; 7].
Proof. by vm_compute. Qed.

