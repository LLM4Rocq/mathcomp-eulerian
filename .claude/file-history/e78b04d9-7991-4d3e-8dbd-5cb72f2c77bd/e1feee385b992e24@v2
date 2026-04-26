(* psi_descent_thms.v — Descent-effect theorems (Fact #2)                   *)
(* Split from psi_descent_v2.v to keep .vo files manageable.                *)

From mathcomp Require Import all_ssreflect.
Require Import mmtree psi_core psi_comm psi_descent_v2.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* ===== M4.8 Helpers for main descent-effect theorems ====================== *)

Lemma window_at_uniq i w :
  uniq w -> uniq (window_at i w).
Proof.
move=> Hu.
apply: (subseq_uniq (take_subseq _ _)).
by apply: (subseq_uniq (drop_subseq _ _)).
Qed.

Lemma size_window_at i w :
  i < size w -> size (window_at i w) = window_size i w.
Proof.
move=> Hiw.
rewrite /window_at size_take size_drop.
case: ltnP => // Hge.
by apply/eqP; rewrite eqn_leq Hge window_size_bound.
Qed.

(* nth in window_at = nth in w, offset by i. *)
Lemma nth_window_at i w j :
  i < size w -> j < window_size i w ->
  nth 0 (window_at i w) j = nth 0 w (i + j).
Proof.
move=> Hiw Hj.
by rewrite /window_at (nth_take _ Hj) nth_drop
   addnC.
Qed.

(* Element of L is between min(sort L) and max(sort L). *)
Lemma elem_in_range (L : seq nat) (j : nat) :
  j < size L ->
  nth 0 (sort leq L) 0 <= nth 0 L j /\
  nth 0 L j <= nth 0 (sort leq L) (size L).-1.
Proof.
move=> Hj.
have Hs : sorted leq (sort leq L) :=
  sort_sorted leq_total L.
have Hsz_s : size (sort leq L) = size L
  by rewrite size_sort.
have Hj_mem : nth 0 L j \in sort leq L
  by rewrite mem_sort mem_nth.
set rj := index (nth 0 L j) (sort leq L).
have Hrj : rj < size (sort leq L)
  by rewrite index_mem.
have Hnth : nth 0 (sort leq L) rj = nth 0 L j
  by rewrite nth_index.
have Hpos : 0 < size L := leq_ltn_trans (leq0n j) Hj.
split.
- rewrite -Hnth.
  have := @sorted_leq_nth _ leq leq_trans leqnn
    0 (sort leq L) Hs.
  move=> /(_ 0 rj); apply.
  + by rewrite inE Hsz_s.
  + by rewrite inE.
  + done.
- rewrite -Hnth.
  have := @sorted_leq_nth _ leq leq_trans leqnn
    0 (sort leq L) Hs.
  move=> /(_ rj (size L).-1); apply.
  + by rewrite inE.
  + by rewrite inE Hsz_s ltn_predL.
  + have : rj < size L by rewrite -Hsz_s.
    by move=> H; rewrite -ltnS (prednK Hpos).
Qed.

(* When head of window is min, not a descent at i. *)
Lemma head_min_not_descent i w :
  uniq w -> 1 < window_size i w ->
  head 0 (window_at i w) =
    nth 0 (sort leq (window_at i w)) 0 ->
  ~~ is_descent_seq w i.
Proof.
move=> Hu Hws Hmin.
have Hiw := ws_lt_size Hws.
set L := window_at i w.
have HszL : size L = window_size i w
  by exact: size_window_at.
have HszL1 : 1 < size L by rewrite HszL.
rewrite /is_descent_seq -leqNgt.
have -> : nth 0 w i = nth 0 L 0.
  by rewrite (nth_window_at Hiw (ltnW Hws)) addn0.
have -> : nth 0 w i.+1 = nth 0 L 1.
  by rewrite (nth_window_at Hiw Hws) addn1.
rewrite (nth0 0 L) Hmin.
have [Hle _] := elem_in_range (j:=1) HszL1.
by [].
Qed.
#[global] Opaque head_min_not_descent.

(* When head of window is max, descent at i. *)
Lemma head_max_is_descent i w :
  uniq w -> 1 < window_size i w ->
  head 0 (window_at i w) =
    nth 0 (sort leq (window_at i w))
          (window_size i w).-1 ->
  is_descent_seq w i.
Proof.
move=> Hu Hws Hmax.
have Hiw := ws_lt_size Hws.
set L := window_at i w.
have HuL : uniq L by exact: window_at_uniq.
have HszL : size L = window_size i w
  by exact: size_window_at.
have HszL1 : 1 < size L by rewrite HszL.
rewrite /is_descent_seq.
have -> : nth 0 w i = nth 0 L 0.
  by rewrite (nth_window_at Hiw (ltnW Hws)) addn0.
have -> : nth 0 w i.+1 = nth 0 L 1.
  by rewrite (nth_window_at Hiw Hws) addn1.
rewrite (nth0 0 L) Hmax.
have Hu_s : uniq (sort leq L) by rewrite sort_uniq.
have Hs : sorted leq (sort leq L)
  := sort_sorted leq_total L.
have Hsz_s : size (sort leq L) = size L
  by rewrite size_sort.
have H1_mem : nth 0 L 1 \in sort leq L
  by rewrite mem_sort mem_nth.
set r1 := index (nth 0 L 1) (sort leq L).
have Hr1 : r1 < size (sort leq L)
  by rewrite index_mem.
have Hne : nth 0 L 1 != nth 0 L 0.
  by rewrite nth_uniq // HszL; exact: ltnW.
have Hr1_ne : r1 != (size L).-1.
  apply/negP => /eqP Heq.
  move: Hne; rewrite nth0 Hmax.
  by rewrite -(nth_index 0 H1_mem) -/r1 Heq HszL
     eqxx.
have Hr1_lt : r1 < (size L).-1.
  rewrite ltn_neqAle Hr1_ne /=.
  by rewrite -ltnS (prednK (ltnW HszL1)) -Hsz_s.
rewrite -HszL -/L -(nth_index 0 H1_mem) -/r1.
rewrite sorted_uniq_nth_ltn // ?Hsz_s //.
by rewrite ltn_predL ltnW.
Qed.
#[global] Opaque head_max_is_descent.

(* Element of rank_shift_seq L is between min and max of sorted L. *)
Lemma elem_rs_in_range (L : seq nat) (j : nat) :
  j < size L ->
  nth 0 (sort leq L) 0 <=
    nth 0 (rank_shift_seq L) j /\
  nth 0 (rank_shift_seq L) j <=
    nth 0 (sort leq L) (size L).-1.
Proof.
move=> Hj.
have Hsz_rs : size (rank_shift_seq L) = size L
  by exact: size_rank_shift_seq2.
have Hj_rs : j < size (rank_shift_seq L)
  by rewrite Hsz_rs.
have Hmem : nth 0 (rank_shift_seq L) j \in L.
  by rewrite -(perm_mem (rank_shift_perm_eq L))
     mem_nth.
have Hmem_s : nth 0 (rank_shift_seq L) j \in
              sort leq L
  by rewrite mem_sort.
have Hs : sorted leq (sort leq L) :=
  sort_sorted leq_total L.
have Hsz_s : size (sort leq L) = size L
  by rewrite size_sort.
set rj := index (nth 0 (rank_shift_seq L) j)
                (sort leq L).
have Hrj : rj < size (sort leq L)
  by rewrite index_mem.
have Hnth : nth 0 (sort leq L) rj =
            nth 0 (rank_shift_seq L) j
  by rewrite nth_index.
have Hpos : 0 < size L :=
  leq_ltn_trans (leq0n j) Hj.
split.
- rewrite -Hnth.
  have := @sorted_leq_nth _ leq leq_trans leqnn
    0 (sort leq L) Hs.
  move=> /(_ 0 rj); apply.
  + by rewrite inE Hsz_s.
  + by rewrite inE.
  + done.
- rewrite -Hnth.
  have := @sorted_leq_nth _ leq leq_trans leqnn
    0 (sort leq L) Hs.
  move=> /(_ rj (size L).-1); apply.
  + by rewrite inE.
  + by rewrite inE Hsz_s ltn_predL.
  + have : rj < size L by rewrite -Hsz_s.
    by move=> H; rewrite -ltnS (prednK Hpos).
Qed.
#[global] Opaque elem_in_range elem_rs_in_range.

(* When new head = max, descent at position 0 in rank_shift_seq. *)
Lemma rs_head_max_descent (L : seq nat) :
  uniq L -> 1 < size L ->
  head 0 L = nth 0 (sort leq L) 0 ->
  nth 0 (rank_shift_seq L) 0 >
  nth 0 (rank_shift_seq L) 1.
Proof.
move=> Hu Hsz Hmin.
have Hnew := rank_shift_head_min_to_max Hu Hsz Hmin.
rewrite [nth 0 (rank_shift_seq L) 0](nth0 0) Hnew.
have Hu_rs := uniq_rank_shift_seq Hu.
have Hsz_rs : size (rank_shift_seq L) = size L
  by exact: size_rank_shift_seq2.
have H1_lt : 1 < size (rank_shift_seq L)
  by rewrite Hsz_rs.
have Hne : nth 0 (rank_shift_seq L) 1 !=
           nth 0 (sort leq L) (size L).-1.
  apply/negP => /eqP Heq.
  have : nth 0 (rank_shift_seq L) 0 =
         nth 0 (rank_shift_seq L) 1.
    by rewrite [nth 0 _ 0](nth0 0) Hnew Heq.
  move/(congr1 (fun x => index x (rank_shift_seq L))).
  have Hlt0 : 0 < size (rank_shift_seq L) by rewrite Hsz_rs; exact: ltnW.
  rewrite (@index_uniq _ 0 0 _ Hlt0 Hu_rs)
          (@index_uniq _ 0 1 _ H1_lt Hu_rs).
  by [].
have [_ Hle] := elem_rs_in_range (j:=1) Hsz.
rewrite ltn_neqAle; apply/andP; split; last by [].
exact: Hne.
Qed.
#[global] Opaque rs_head_max_descent.

(* When new head = min, no descent at position 0 in rank_shift_seq. *)
Lemma rs_head_min_no_descent (L : seq nat) :
  uniq L -> 1 < size L ->
  head 0 L = nth 0 (sort leq L) (size L).-1 ->
  nth 0 (rank_shift_seq L) 0 <
  nth 0 (rank_shift_seq L) 1.
Proof.
move=> Hu Hsz Hmax.
have Hnew := rank_shift_head_max_to_min Hu Hsz Hmax.
rewrite [nth 0 (rank_shift_seq L) 0](nth0 0) Hnew.
have Hu_rs := uniq_rank_shift_seq Hu.
have Hsz_rs : size (rank_shift_seq L) = size L
  by exact: size_rank_shift_seq2.
have H1_lt : 1 < size (rank_shift_seq L)
  by rewrite Hsz_rs.
have Hne : nth 0 (rank_shift_seq L) 1 !=
           nth 0 (sort leq L) 0.
  apply/negP => /eqP Heq.
  have : nth 0 (rank_shift_seq L) 0 =
         nth 0 (rank_shift_seq L) 1.
    by rewrite [nth 0 _ 0](nth0 0) Hnew Heq.
  move/(congr1 (fun x => index x (rank_shift_seq L))).
  have Hlt0 : 0 < size (rank_shift_seq L) by rewrite Hsz_rs; exact: ltnW.
  rewrite (@index_uniq _ 0 0 _ Hlt0 Hu_rs)
          (@index_uniq _ 0 1 _ H1_lt Hu_rs).
  by [].
have [Hle _] := elem_rs_in_range (j:=1) Hsz.
rewrite ltn_neqAle; apply/andP; split; last by [].
by rewrite eq_sym.
Qed.
#[global] Opaque rs_head_min_no_descent.

(* Comparison with an out-of-range value is the same for any
   element of L or rank_shift_seq L. *)
Lemma cmp_out_of_range (L : seq nat) (v : nat)
    (j j' : nat) :
  j < size L -> j' < size L ->
  (v < nth 0 (sort leq L) 0 \/
   v > nth 0 (sort leq L) (size L).-1) ->
  (nth 0 L j > v) = (nth 0 (rank_shift_seq L) j' > v).
Proof.
move=> Hj Hj' [Hlt | Hgt].
- have [Hmin_j _] := elem_in_range Hj.
  have [Hmin_j' _] := elem_rs_in_range Hj'.
  apply/idP/idP => _.
  + by exact: leq_trans Hlt Hmin_j'.
  + by exact: leq_trans Hlt Hmin_j.
- have [_ Hmax_j] := elem_in_range Hj.
  have [_ Hmax_j'] := elem_rs_in_range Hj'.
  have F1 : ~~ (nth 0 L j > v)
    by rewrite -leqNgt; exact: leq_trans Hmax_j (ltnW Hgt).
  have F2 : ~~ (nth 0 (rank_shift_seq L) j' > v)
    by rewrite -leqNgt; exact: leq_trans Hmax_j' (ltnW Hgt).
  by rewrite (negbTE F1) (negbTE F2).
Qed.

(* Version with v on the left: (v > elem_L) = (v > elem_rs). *)
Lemma cmp_out_of_range_left (L : seq nat) (v : nat)
    (j j' : nat) :
  j < size L -> j' < size L ->
  (v < nth 0 (sort leq L) 0 \/
   v > nth 0 (sort leq L) (size L).-1) ->
  (v > nth 0 L j) = (v > nth 0 (rank_shift_seq L) j').
Proof.
move=> Hj Hj' [Hlt | Hgt].
- have [Hmin_j _] := elem_in_range Hj.
  have [Hmin_j' _] := elem_rs_in_range Hj'.
  have F1 : ~~ (v > nth 0 L j)
    by rewrite -leqNgt; exact: leq_trans (ltnW Hlt) Hmin_j.
  have F2 : ~~ (v > nth 0 (rank_shift_seq L) j')
    by rewrite -leqNgt; exact: leq_trans (ltnW Hlt) Hmin_j'.
  by rewrite (negbTE F1) (negbTE F2).
- have [_ Hmax_j] := elem_in_range Hj.
  have [_ Hmax_j'] := elem_rs_in_range Hj'.
  apply/idP/idP => _.
  + by exact: leq_ltn_trans Hmax_j' Hgt.
  + by exact: leq_ltn_trans Hmax_j Hgt.
Qed.
#[global] Opaque cmp_out_of_range cmp_out_of_range_left.

(* The descent-set effect of psi_i, organized by tree case (R vs LR) and     *)
(* whether i is currently a descent.                                         *)
(* Each lemma describes D(psi_i w) in terms of D(w) for all positions k.     *)
(* Justification: M4_DESCENT_EFFECT_INFORMAL.md sections 2-4.                *)

(* ----- Common proof pattern for descent-effect lemmas ---------------------- *)
(* Each lemma case-splits k relative to window [i, i+ws):                     *)
(*   k+1 < i (prefix), k = i-1 (left boundary), k = i (head),               *)
(*   i < k < i+ws (interior), k = i+ws-1 (right boundary), k >= i+ws (suffix)*)

(* Factored helpers: interior and right-boundary cases are identical across   *)
(* all four descent-effect lemmas. Extracting them avoids quadrupling the     *)
(* proof term and cuts ~60 GB peak memory to ~15-20 GB.                      *)

Lemma descent_psi_interior i w k :
  uniq w -> 1 < window_size i w ->
  i < k -> k.+1 < i + window_size i w ->
  is_descent_seq (psi i w) k = is_descent_seq w k.
Proof.
move=> Hu Hws Hk_gt Hk1_in.
have Hiw := ws_lt_size Hws.
have Hk_lt : k < i + window_size i w :=
  ltn_trans (ltnSn k) Hk1_in.
rewrite /is_descent_seq.
rewrite (nth_psi_inside Hiw (ltnW Hk_gt) Hk_lt)
        (nth_psi_inside Hiw
          (ltnW (ltn_trans Hk_gt (ltnSn k)))
          Hk1_in).
have Hk_off : k - i < window_size i w.
  rewrite -(ltn_add2l i) subnKC //; exact: ltnW.
have Hk1_off : k.+1 - i < window_size i w.
  rewrite -(ltn_add2l i) subnKC //.
  exact: ltnW (ltn_trans Hk_gt (ltnSn k)).
have HszL : size (window_at i w) = window_size i w :=
  size_window_at Hiw.
have HszL1 : 1 < size (window_at i w). by rewrite HszL.
have Hk_lt_L : k - i < size (window_at i w). by rewrite HszL.
have Hk1_lt_L : k.+1 - i < size (window_at i w). by rewrite HszL.
have Hp0 : 0 < k.+1 - i.
  by rewrite subn_gt0; exact: ltn_trans Hk_gt (ltnSn k).
have Hq0 : 0 < k - i. by rewrite subn_gt0.
have Hrio : (nth 0 (window_at i w) (k - i) >
             nth 0 (window_at i w) (k.+1 - i)) =
   (nth 0 (rank_shift_seq (window_at i w)) (k - i) >
    nth 0 (rank_shift_seq (window_at i w)) (k.+1 - i)) :=
  rank_shift_preserves_interior_order
    (window_at_uniq i Hu) HszL1
    (window_head_extremum Hu Hws)
    Hq0 Hp0 Hk_lt_L Hk1_lt_L.
rewrite -Hrio; congr (_ < _).
- have Hi_k1 : i <= k.+1 :=
    ltnW (ltn_trans Hk_gt (ltnSn k)).
  by rewrite (nth_window_at Hiw Hk1_off) (subnKC Hi_k1).
- by rewrite (nth_window_at Hiw Hk_off)
     (subnKC (ltnW Hk_gt)).
Qed.
#[global] Opaque descent_psi_interior.

Lemma descent_psi_rboundary i w k :
  uniq w -> 1 < window_size i w ->
  i < k -> k.+1 = i + window_size i w ->
  k < (size w).-1 ->
  is_descent_seq (psi i w) k = is_descent_seq w k.
Proof.
move=> Hu Hws Hk_gt Hk1_eq Hk.
have Hiw := ws_lt_size Hws.
set ws := window_size i w. set L := window_at i w.
have Hk_lt : k < i + ws.
  by rewrite -Hk1_eq.
rewrite /is_descent_seq Hk1_eq nth_psi_right //.
rewrite /ws in Hk_lt.
rewrite (nth_psi_inside Hiw (ltnW Hk_gt) Hk_lt) -/L.
have HszL : size L = ws := size_window_at Hiw.
have Hk_off_ws : k - i < window_size i w.
  rewrite -(ltn_add2l i) subnKC //; exact: ltnW.
have Hk_off : k - i < size L. by rewrite HszL.
have Hpost : i + ws < size w
  by rewrite -Hk1_eq -ltn_predRL.
have [Hlt|Hgt] := post_window_extremum Hu Hpost.
- have Hlt' : nth 0 w (i + ws) <
    nth 0 (sort leq L) 0 := Hlt.
  rewrite -(cmp_out_of_range Hk_off Hk_off
    (or_introl Hlt')).
  congr (_ > _).
  by rewrite (nth_window_at Hiw Hk_off_ws)
     (subnKC (ltnW Hk_gt)).
- have Hgt' :
    nth 0 (sort leq L) (size L).-1 <
      nth 0 w (i + ws).
    by move: Hgt; rewrite /L /ws HszL.
  rewrite -(cmp_out_of_range Hk_off Hk_off
    (or_intror Hgt')).
  congr (_ > _).
  by rewrite (nth_window_at Hiw Hk_off_ws)
     (subnKC (ltnW Hk_gt)).
Qed.
#[global] Opaque descent_psi_rboundary.

(* Left boundary helper for the R (no left child) case: the comparison
   at position i-1 is preserved by rank_shift because i-1 is outside
   the window and the window extremum separates it from all window values. *)
Lemma descent_psi_lboundary_R i w :
  uniq w -> 1 < window_size i w -> ~~ has_left_child i w ->
  0 < i ->
  is_descent_seq (psi i w) i.-1 = is_descent_seq w i.-1.
Proof.
move=> Hu Hws Hnlc Hi0.
have Hiw := ws_lt_size Hws.
set ws := window_size i w. set L := window_at i w.
have HszL : size L = ws := size_window_at Hiw.
have HszL1 : 1 < size L by rewrite HszL.
rewrite /is_descent_seq (prednK Hi0).
have Hpred : i.-1 < i by rewrite ltn_predL.
rewrite (@nth_psi_left i w i.-1 Hpred).
have Hi0_ws : i < i + window_size i w
  by rewrite -[X in X < _]addn0 ltn_add2l ltnW.
rewrite (nth_psi_inside Hiw (leqnn i) Hi0_ws)
  subnn -/L.
have Hpe := pre_window_extremum_R Hu Hi0 Hnlc Hws.
have Hpe' :
  nth 0 w i.-1 < nth 0 (sort leq L) 0 \/
  nth 0 (sort leq L) (size L).-1 < nth 0 w i.-1
  by rewrite HszL /ws /L.
rewrite -(cmp_out_of_range_left
  (ltnW HszL1) (ltnW HszL1) Hpe').
congr (_ < _).
by rewrite (nth_window_at Hiw (ltnW Hws)) addn0.
Qed.
#[global] Opaque descent_psi_lboundary_R.

(* Case R (right-child only), i not a descent: D(psi_i w) = D(w) u {i}. *)
Lemma descent_psi_R_add i w :
  uniq w -> 1 < window_size i w -> ~~ has_left_child i w ->
  ~~ is_descent_seq w i ->
  forall k, k < (size w).-1 ->
    is_descent_seq (psi i w) k = (k == i) || is_descent_seq w k.
Proof.
move=> Hu Hws Hnlc Hnd k Hk.
have Hiw := ws_lt_size Hws.
set ws := window_size i w. set L := window_at i w.
have HuL := window_at_uniq i Hu.
have HszL : size L = ws := size_window_at Hiw.
have HszL1 : 1 < size L by rewrite HszL.
have Hmin : head 0 L = nth 0 (sort leq L) 0.
  case/orP: (window_head_extremum Hu Hws) =>
    [/eqP //|/eqP Hmax].
  exfalso; apply/negP: Hnd; rewrite negbK.
  by rewrite (size_window_at Hiw) in Hmax;
     exact: (head_max_is_descent Hu Hws Hmax).
have Hi_ws1 : i.+1 < i + ws by rewrite -addn1 ltn_add2l.
have Hi_ws0 : i < i + ws by exact: ltn_trans (ltnSn i) Hi_ws1.
have [->|Hne] := eqVneq k i.
{ rewrite /ws in Hi_ws0 Hi_ws1.
  abstract (rewrite /= /is_descent_seq;
  rewrite (nth_psi_inside Hiw (leqnn i) Hi_ws0)
          (nth_psi_inside Hiw (leqnSn i) Hi_ws1)
          subnn (@subSnn i) -/L;
  by apply: (rs_head_max_descent HuL HszL1 Hmin)). }
rewrite orFb.
case: (ltnP k i) => [Hk_lt_i | Hk_ge_i].
{ case: (ltnP k.+1 i) => [Hk1_lt|Hk1_ge].
  - abstract (by rewrite /is_descent_seq !nth_psi_left //; exact: ltnW).
  - have Hk1_eq : k.+1 = i
      by apply/eqP; rewrite eqn_leq Hk_lt_i Hk1_ge.
    have Hi0 : 0 < i by rewrite -Hk1_eq.
    have -> : k = i.-1 by rewrite -Hk1_eq.
    exact: descent_psi_lboundary_R. }
{ have Hk_gt : i < k
    by rewrite ltn_neqAle eq_sym Hne Hk_ge_i.
  case: (leqP (i + ws) k) => [Hk_ge|Hk_lt].
  - abstract (by rewrite /is_descent_seq !nth_psi_right //;
       exact: leq_trans Hk_ge (leqnSn k)).
  - case: (ltnP k.+1 (i + ws)) => [Hk1_in|Hk1_out].
    + abstract (by rewrite /ws in Hk1_in; exact: descent_psi_interior).
    + have Hk1_eq : k.+1 = i + ws.
        by apply/eqP; rewrite eqn_leq Hk1_out andbT.
      abstract (by exact: descent_psi_rboundary). }
Qed.
#[global] Opaque descent_psi_R_add.

(* Case R, i is a descent: D(psi_i w) = D(w) \ {i}. *)
Lemma descent_psi_R_remove i w :
  uniq w -> 1 < window_size i w -> ~~ has_left_child i w ->
  is_descent_seq w i ->
  forall k, k < (size w).-1 ->
    is_descent_seq (psi i w) k = (k != i) && is_descent_seq w k.
Proof.
move=> Hu Hws Hnlc Hd k Hk.
have Hiw := ws_lt_size Hws.
set ws := window_size i w. set L := window_at i w.
have HuL := window_at_uniq i Hu.
have HszL : size L = ws := size_window_at Hiw.
have HszL1 : 1 < size L by rewrite HszL.
have Hmax : head 0 L = nth 0 (sort leq L) (size L).-1.
  case/orP: (window_head_extremum Hu Hws) =>
    [/eqP Hmin|/eqP //].
  exfalso; move/negP: (head_min_not_descent Hu Hws Hmin).
  by rewrite Hd.
have Hi_ws1 : i.+1 < i + ws by rewrite -addn1 ltn_add2l.
have Hi_ws0 : i < i + ws by exact: ltn_trans (ltnSn i) Hi_ws1.
have [->|Hne] := eqVneq k i.
{ rewrite /ws in Hi_ws0 Hi_ws1.
  rewrite /is_descent_seq.
  rewrite (nth_psi_inside Hiw (leqnn i) Hi_ws0)
          (nth_psi_inside Hiw (leqnSn i) Hi_ws1)
          subnn (@subSnn i) -/L.
  have Hlt := rs_head_min_no_descent HuL HszL1 Hmax.
  apply/negbTE; rewrite -leqNgt; exact: ltnW. }
rewrite /=.
case: (ltnP k i) => [Hk_lt_i | Hk_ge_i].
{ case: (ltnP k.+1 i) => [Hk1_lt|Hk1_ge].
  - abstract (by rewrite /is_descent_seq !nth_psi_left //).
  - have Hk1_eq : k.+1 = i
      by apply/eqP; rewrite eqn_leq Hk_lt_i Hk1_ge.
    have Hi0 : 0 < i by rewrite -Hk1_eq.
    have -> : k = i.-1 by rewrite -Hk1_eq.
    exact: descent_psi_lboundary_R. }
{ have Hk_gt : i < k
    by rewrite ltn_neqAle eq_sym Hne Hk_ge_i.
  case: (leqP (i + ws) k) => [Hk_ge|Hk_lt].
  - abstract (by rewrite /is_descent_seq !nth_psi_right //;
       exact: leq_trans Hk_ge (leqnSn k)).
  - case: (ltnP k.+1 (i + ws)) => [Hk1_in|Hk1_out].
    + abstract (by rewrite /ws in Hk1_in; exact: descent_psi_interior).
    + have Hk1_eq : k.+1 = i + ws.
        by apply/eqP; rewrite eqn_leq Hk1_out andbT.
      abstract (by exact: descent_psi_rboundary). }
Qed.
#[global] Opaque descent_psi_R_remove.

(* Case LR, i not a descent (so i-1 is): D(psi_i w) = (D(w) u {i}) \ {i-1}. *)
Lemma descent_psi_LR_swap1 i w :
  uniq w -> 1 < window_size i w -> has_left_child i w ->
  ~~ is_descent_seq w i ->
  forall k, k < (size w).-1 ->
    is_descent_seq (psi i w) k =
      if k == i then true
      else if k == i.-1 then false
      else is_descent_seq w k.
Proof.
move=> Hu Hws Hlc Hnd k Hk.
have Hiw := ws_lt_size Hws.
set ws := window_size i w. set L := window_at i w.
have HuL := window_at_uniq i Hu.
have HszL : size L = ws := size_window_at Hiw.
have HszL1 : 1 < size L by rewrite HszL.
have Hmin : head 0 L = nth 0 (sort leq L) 0.
  case/orP: (window_head_extremum Hu Hws) =>
    [/eqP //|/eqP Hmax].
  exfalso; apply/negP: Hnd; rewrite negbK.
  by rewrite (size_window_at Hiw) in Hmax;
     exact: (head_max_is_descent Hu Hws Hmax).
have Hi0 : 0 < i.
  case: i ws L Hiw Hws Hlc {Hnd Hk Hmin HszL HszL1 HuL} =>
    [|//] _ _ _ Hws1 Hlc1.
  by rewrite has_left_child_0 in Hlc1.
have Hi1 : i.+1 < i + ws by rewrite -addn1 ltn_add2l.
have Hi0_ws : i < i + ws by exact: ltn_trans (ltnSn i) Hi1.
have [->|Hne] := eqVneq k i.
{ rewrite /ws in Hi0_ws Hi1.
  abstract (rewrite /= /is_descent_seq;
  rewrite (nth_psi_inside Hiw (leqnn i) Hi0_ws)
          (nth_psi_inside Hiw (leqnSn i) Hi1)
          subnn (@subSnn i) -/L;
  by apply: (rs_head_max_descent HuL HszL1 Hmin)). }
case Hki1 : (k == i.-1).
{ move/eqP: Hki1 => ->.
  rewrite /is_descent_seq.
  have Hpred : i.-1 < i by rewrite ltn_predL.
  rewrite (@nth_psi_left i w i.-1 Hpred) (prednK Hi0)
          (nth_psi_inside Hiw (leqnn i) Hi0_ws) subnn -/L.
  have Hmin_eq : head 0 (rank_shift_seq L) =
    nth 0 (sort leq L) (size L).-1
    by exact: rank_shift_head_min_to_max HuL HszL1 Hmin.
  apply: negbTE; rewrite -leqNgt (nth0 0) Hmin_eq HszL.
  have Hmin_bool : head 0 L == nth 0 (sort leq L) 0 by apply/eqP.
  exact: ltnW (pre_window_lt_max_when_min_head
    Hu Hi0 Hlc Hws Hmin_bool). }
case: (ltnP k i) => [Hk_lt_i | Hk_ge_i].
{ case: (ltnP k.+1 i) => [Hk1_lt|Hk1_ge].
  - abstract (by rewrite /is_descent_seq !nth_psi_left //).
  - exfalso; move/eqP: Hki1; apply.
    have : k.+1 = i by apply/eqP; rewrite eqn_leq Hk_lt_i Hk1_ge.
    by move=> <-. }
{ have Hk_gt : i < k
    by rewrite ltn_neqAle eq_sym Hne Hk_ge_i.
  case: (leqP (i + ws) k) => [Hk_ge|Hk_lt].
  - abstract (by rewrite /is_descent_seq !nth_psi_right //;
       exact: leq_trans Hk_ge (leqnSn k)).
  - case: (ltnP k.+1 (i + ws)) => [Hk1_in|Hk1_out].
    + abstract (by rewrite /ws in Hk1_in; exact: descent_psi_interior).
    + have Hk1_eq : k.+1 = i + ws.
        by apply/eqP; rewrite eqn_leq Hk1_out andbT.
      abstract (by exact: descent_psi_rboundary). }
Qed.
#[global] Opaque descent_psi_LR_swap1.

(* Case LR, i is a descent (so i-1 is not): D(psi_i w) = (D(w) u {i-1}) \ {i}. *)
Lemma descent_psi_LR_swap2 i w :
  uniq w -> 1 < window_size i w -> has_left_child i w ->
  is_descent_seq w i ->
  forall k, k < (size w).-1 ->
    is_descent_seq (psi i w) k =
      if k == i then false
      else if k == i.-1 then true
      else is_descent_seq w k.
Proof.
move=> Hu Hws Hlc Hd k Hk.
have Hiw := ws_lt_size Hws.
set ws := window_size i w. set L := window_at i w.
have HuL := window_at_uniq i Hu.
have HszL : size L = ws := size_window_at Hiw.
have HszL1 : 1 < size L by rewrite HszL.
have Hmax : head 0 L = nth 0 (sort leq L) (size L).-1.
  case/orP: (window_head_extremum Hu Hws) =>
    [/eqP Hmin_eq|/eqP //].
  exfalso; move/negP: (head_min_not_descent Hu Hws Hmin_eq).
  by rewrite Hd.
have Hi0 : 0 < i.
  case: i ws L Hiw Hws Hlc {Hd Hk Hmax HszL HszL1 HuL} =>
    [|//] _ _ _ Hws1 Hlc1.
  by rewrite has_left_child_0 in Hlc1.
have Hi1 : i.+1 < i + ws by rewrite -addn1 ltn_add2l.
have Hi0_ws : i < i + ws by exact: ltn_trans (ltnSn i) Hi1.
have [->|Hne] := eqVneq k i.
{ rewrite /ws in Hi0_ws Hi1.
  abstract (rewrite /= /is_descent_seq;
  rewrite (nth_psi_inside Hiw (leqnn i) Hi0_ws)
          (nth_psi_inside Hiw (leqnSn i) Hi1)
          subnn (@subSnn i) -/L;
  apply/negbTE; rewrite -leqNgt;
  exact: ltnW (rs_head_min_no_descent HuL HszL1 Hmax)). }
case Hki1 : (k == i.-1).
{ move/eqP: Hki1 => ->.
  rewrite /is_descent_seq.
  have Hpred : i.-1 < i by rewrite ltn_predL.
  rewrite (@nth_psi_left i w i.-1 Hpred) (prednK Hi0)
          (nth_psi_inside Hiw (leqnn i) Hi0_ws) subnn -/L.
  have Hmax_eq : head 0 (rank_shift_seq L) =
    nth 0 (sort leq L) 0
    by exact: rank_shift_head_max_to_min HuL HszL1 Hmax.
  rewrite (nth0 0) Hmax_eq.
  have Hmax_bool : head 0 (window_at i w) ==
    nth 0 (sort leq (window_at i w)) (window_size i w).-1.
  { rewrite /L in Hmax. rewrite -(size_window_at Hiw).
    apply/eqP; exact: Hmax. }
  exact: pre_window_gt_min_when_max_head
    Hu Hi0 Hlc Hws Hmax_bool. }
case: (ltnP k i) => [Hk_lt_i | Hk_ge_i].
{ case: (ltnP k.+1 i) => [Hk1_lt|Hk1_ge].
  - abstract (by rewrite /is_descent_seq !nth_psi_left //; exact: ltnW).
  - exfalso; move/eqP: Hki1; apply.
    have : k.+1 = i by apply/eqP; rewrite eqn_leq Hk_lt_i Hk1_ge.
    by move=> <-. }
{ have Hk_gt : i < k
    by rewrite ltn_neqAle eq_sym Hne Hk_ge_i.
  case: (leqP (i + ws) k) => [Hk_ge|Hk_lt].
  - abstract (by rewrite /is_descent_seq !nth_psi_right //;
       exact: leq_trans Hk_ge (leqnSn k)).
  - case: (ltnP k.+1 (i + ws)) => [Hk1_in|Hk1_out].
    + abstract (by rewrite /ws in Hk1_in; exact: descent_psi_interior).
    + have Hk1_eq : k.+1 = i + ws.
        by apply/eqP; rewrite eqn_leq Hk1_out andbT.
      abstract (by exact: descent_psi_rboundary). }
Qed.
#[global] Opaque descent_psi_LR_swap2.

(* ----- M4.9 Non-triviality examples for Fact #2 --------------------------- *)

(* Case R, add: w = [3;1;4;7;5;9;2;6], i=2.
   window_size 2 w = 3. has_left_child 2 w = false. ~~ is_descent_seq w 2 (4 < 7).
   psi 2 w = [3;1;7;5;4;9;2;6].
   D(psi 2 w) = {0,2,3,5} = D(w) u {2}. *)
Example descent_psi_R_add_ex :
  let w := [:: 3; 1; 4; 7; 5; 9; 2; 6] in
  [seq k <- iota 0 7 | is_descent_seq (psi 2 w) k] = [:: 0; 2; 3; 5].
Proof. by []. Qed.

(* Case R, remove: psi 2 on the result above gives back w.
   w' = [3;1;7;5;4;9;2;6]. is_descent_seq w' 2 = (7 > 5) = true.
   psi 2 w' = [3;1;4;7;5;9;2;6].
   D(psi 2 w') = {0,3,5} = D(w') \ {2}. *)
Example descent_psi_R_remove_ex :
  let w' := psi 2 [:: 3; 1; 4; 7; 5; 9; 2; 6] in
  [seq k <- iota 0 7 | is_descent_seq (psi 2 w') k] = [:: 0; 3; 5].
Proof. by []. Qed.

(* Case LR, swap2: w = [3;1;4;7;5;9;2;6], i=5.
   has_left_child 5 w = true. is_descent_seq w 5 = (9 > 2) = true.
   psi 5 w = [3;1;4;7;5;2;6;9].
   D(psi 5 w) = {0,3,4} = (D(w) u {4}) \ {5}. *)
Example descent_psi_LR_swap2_ex :
  let w := [:: 3; 1; 4; 7; 5; 9; 2; 6] in
  [seq k <- iota 0 7 | is_descent_seq (psi 5 w) k] = [:: 0; 3; 4].
Proof. by []. Qed.

(* Case LR, swap1: w' = psi 5 w = [3;1;4;7;5;2;6;9], i=5.
   is_descent_seq w' 5 = (2 > 6) = false. ~~ is_descent_seq w' 5 = true.
   psi 5 w' = [3;1;4;7;5;9;2;6].
   D(psi 5 w') = {0,3,5} = (D(w') u {5}) \ {4}. *)
Example descent_psi_LR_swap1_ex :
  let w' := psi 5 [:: 3; 1; 4; 7; 5; 9; 2; 6] in
  [seq k <- iota 0 7 | is_descent_seq (psi 5 w') k] = [:: 0; 3; 5].
Proof. by []. Qed.
