(* psi_cdindex_tree_hlc.v — has_left_child structural proofs                 *)
(*                                                                           *)
(* Split from psi_cdindex_tree.v to reduce -vo compilation memory.           *)
(* Contains: has_left_child_order_iso, behead_rank_shift_order_iso,          *)
(* has_left_child_psi.                                                       *)

From mathcomp Require Import all_ssreflect.
Require Import mmtree psi_core psi_comm psi_descent_v2 psi_descent_thms.
Require Import psi_cdindex_defs.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* ----- M5.2 Tree-shape invariance under psi -------------------------------- *)

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
  abstract (by rewrite (size0nil Hsz0);
     rewrite Hsz0 in Hszeq;
     rewrite (size0nil (esym Hszeq))).
case Hs1 : s1 => [|a1 t1]; first
  abstract (by move: Hszeq; rewrite Hs1 /= => Hsz2;
     have -> : s2 = [::] by apply/eqP;
     rewrite -size_eq0 -Hsz2).
case Hs2 : s2 => [|a2 t2]; first
  abstract (by move: Hszeq; rewrite Hs1 Hs2 /=).
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
- abstract (apply: IH;
  [ rewrite size_takel ?ltnW //;
    exact: leq_trans (ltnW Hm1) Hsz1
  | by rewrite !size_takel // ?ltnW //
       -(mm_pos_order_iso Hszeq' Hu1 Hu2 Hne1 Hord)
  | by move: Hu1;
       rewrite -{1}(cat_take_drop m (a1 :: t1))
       cat_uniq => /andP []
  | by move: Hu2;
       rewrite -{1}(cat_take_drop m (a2 :: t2))
       cat_uniq => /andP []
  | move=> p q Hp Hq;
    rewrite !nth_take //;
    apply: Hord;
      apply: ltn_trans _ Hm1;
      rewrite size_takel ?ltnW //
      in Hp Hq; done ]).
- abstract (apply: IH;
  [ rewrite size_drop;
    by apply: leq_trans (leq_subr _ _);
       rewrite /= ltnS in Hsz1;
       exact: (leq_trans (leqnSn _) Hsz1)
  | by rewrite !size_drop Hszeq'
  | by move: Hu1;
       rewrite -{1}(cat_take_drop m.+1 (a1 :: t1))
       cat_uniq => /andP [_ /andP [_ ?]]
  | by move: Hu2;
       rewrite -{1}(cat_take_drop m.+1 (a2 :: t2))
       cat_uniq => /andP [_ /andP [_ ?]]
  | move=> p q Hp Hq;
    rewrite !nth_drop; apply: Hord;
      rewrite /= ltnS size_drop /= in Hp Hq;
      rewrite /= ltnS;
      by apply: leq_trans _ (leq_subr _ _) => //;
         exact: leq_add ]).
- by [].
Qed.

(* Extracted to avoid exponential proof-term growth when passed as  *)
(* the 4th argument to has_left_child_order_iso (duplicated at     *)
(* every recursive call).                                          *)
Lemma behead_rank_shift_order_iso (L : seq nat) :
  uniq L -> 1 < size L ->
  (head 0 L == nth 0 (sort leq L) 0) ||
  (head 0 L == nth 0 (sort leq L) (size L).-1) ->
  forall p q,
  p < size (behead L) -> q < size (behead L) ->
  (nth 0 (behead L) p < nth 0 (behead L) q) =
  (nth 0 (behead (rank_shift_seq L)) p <
   nth 0 (behead (rank_shift_seq L)) q).
Proof.
move=> Huniq Hsz Hhead p q Hp Hq.
have Hsz_bh : size (behead L) = (size L).-1
  by rewrite size_behead.
have Hp1 : p.+1 < size L.
  by rewrite -ltnS prednK //;
     rewrite Hsz_bh in Hp; apply: ltnW.
have Hq1 : q.+1 < size L.
  by rewrite -ltnS prednK //;
     rewrite Hsz_bh in Hq; apply: ltnW.
rewrite -[behead (rank_shift_seq L)]
  (drop1 (rank_shift_seq L)).
rewrite -[behead L](drop1 L).
rewrite !nth_drop.
rewrite [1 + p]addnC [1 + q]addnC.
symmetry.
exact: rank_shift_preserves_interior_order
  Huniq Hsz Hhead (ltn0Sn _) (ltn0Sn _)
  Hp1 Hq1.
Qed.

Opaque behead_rank_shift_order_iso.

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
    abstract (
    rewrite -Hpsi_eq
      (take_mm_psi Hs_ne Huniq Hws_gt1 Hjm);
    apply: IH;
    [ rewrite size_take Hm;
      exact: leq_trans (ltnW Hm) Hsz
    | have : uniq (take m s ++ drop m s)
        by rewrite cat_take_drop;
      by rewrite cat_uniq => /andP [? /andP [? ?]] ]).
  + abstract
      (by rewrite -Hpsi_eq
         (@take_psi m j s (ltnW Hmj))).
  + abstract
      (by rewrite -Hpsi_eq Hjeqm
         (@take_psi m m s (leqnn m))).
- (* i > m *)
  case: (ltngtP j m) => [Hjm | Hmj | Hjeqm].
  + (* j < m *)
    abstract (
    suff -> : drop m.+1 (a' :: s0') =
      drop m.+1 (a :: s0) by [];
    rewrite -Hpsi_eq;
    apply: drop_psi_above;
    apply: leq_trans (window_fits_left Hs_ne Hjm) _;
    exact: leqnSn).
  + (* j > m *)
    abstract (
    suff -> : drop m.+1 (a' :: s0') =
      psi (j - m - 1) (drop m.+1 (a :: s0));
    [ apply: IH;
      [ rewrite /s /= size_drop;
        exact: leq_trans (leq_subr _ _) (ltnW Hsz)
      | have : uniq (take m.+1 s ++ drop m.+1 s)
          by rewrite cat_take_drop;
        by rewrite cat_uniq => /andP [_ /andP [_ ?]] ]
    | by rewrite -Hpsi_eq
         (drop_mm_psi Hs_ne Huniq Hws_gt1 Hmj) ]).
  + (* j = m: use has_left_child_order_iso *)
    abstract (
    subst j;
    have Hws_m : window_size m s = size s - m
      by rewrite (window_size_cons m a s0) -/m ltnn eqxx;
    have Hws_drop : 1 < size (drop m s)
      by rewrite size_drop -Hws_m;
    have Hdm_ne : drop m s <> [::]
      by case: (drop m s) Hws_drop;
    have Huniq_dm : uniq (drop m s)
      by (have : uniq (take m s ++ drop m s)
        by rewrite cat_take_drop);
      rewrite cat_uniq => /andP [_ /andP [_ ?]];
    have Hmm_drop : mm_pos (drop m s) = 0
      by exact: mm_pos_drop_mm;
    have Hpsi_m_eq : psi m s =
      take m s ++ rank_shift_seq (drop m s)
      by (rewrite /psi;
      have Hwa_m : window_at m s = drop m s
        by rewrite (window_at_cons m a s0)
           -/m ltnn eqxx //;
      rewrite Hwa_m Hws_m;
      by rewrite subnKC ?drop_size ?cats0 // ltnW);
    have Him' : 0 < i - m by rewrite subn_gt0;
    have Hdrop_psi : drop m.+1 (a' :: s0') =
      behead (rank_shift_seq (drop m s))
      by (rewrite -Hpsi_eq Hpsi_m_eq;
      rewrite drop_cat size_take Hm;
      have -> : m.+1 < m = false
        by rewrite ltnNge leqnSn;
      by rewrite /= subSn // subnn drop0);
    have Hdrop_orig : drop m.+1 (a :: s0) =
      behead (drop m s)
      by rewrite /s /= drop0;
    rewrite Hdrop_psi Hdrop_orig;
    apply: has_left_child_order_iso;
    [ by rewrite !size_behead size_rank_shift_seq2
    | apply: (subseq_uniq (suffix_subseq 1 _));
      by rewrite (perm_uniq (rank_shift_perm_eq _))
    | exact: (subseq_uniq (suffix_subseq 1 _))
    | have Hhead_ext : (head 0 (drop m s) ==
        nth 0 (sort leq (drop m s)) 0) ||
        (head 0 (drop m s) ==
         nth 0 (sort leq (drop m s))
         (size (drop m s)).-1)
        by apply: window_head_extremum => //;
        rewrite (window_size_cons m a s0)
          -/m ltnn eqxx //;
      exact: behead_rank_shift_order_iso
        Huniq_dm Hws_drop Hhead_ext ]).
- (* i = m *)
  by [].
Qed.
