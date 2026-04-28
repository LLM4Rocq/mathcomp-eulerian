(* psi_cdindex_tree_shape.v — Tree-shape encoding for ψ-invariance.          *)
(*                                                                            *)
(* Replaces the per-property recursive proofs in psi_cdindex_tree_hlc.v with  *)
(* a single heavy proof on tree shapes plus thin corollaries.  Reduces peak  *)
(* -vo memory below the 128 GB process cap.                                   *)
(*                                                                            *)
(* The shape encoding flattens the min-max tree as: head = mm_pos, tail =     *)
(* shape(left subtree) ++ shape(right subtree).  Two sequences with equal     *)
(* shape produce the same min-max tree (modulo labels), so any property that  *)
(* depends only on the tree structure (has_left_child, window_size, …) is     *)
(* shape-determined.                                                          *)

From mathcomp Require Import all_ssreflect.
Require Import mmtree psi_core psi_comm psi_descent_v2 psi_descent_thms.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* No Opaque declarations here.  mm_pos_order_iso / order_iso_take /        *)
(* order_iso_drop being transparent matches the original tree_hlc.v setup, *)
(* under which psi_cdindex_tree.v's heavy proofs compile to -vo.            *)

(* ===== Tree shape definition ============================================ *)

Fixpoint mmtree_shape_fuel (fuel : nat) (s : seq nat) : seq nat :=
  match fuel with
  | 0 => [::]
  | fuel'.+1 =>
      match s with
      | [::] => [::]
      | _ :: _ =>
          let j := mm_pos s in
          mm_pos s ::
            (mmtree_shape_fuel fuel' (take j s) ++
             mmtree_shape_fuel fuel' (drop j.+1 s))
      end
  end.

Arguments mmtree_shape_fuel : simpl never.

Definition mmtree_shape (s : seq nat) : seq nat :=
  mmtree_shape_fuel (size s) s.

(* ===== Structural lemmas ================================================ *)

Lemma mmtree_shape_fuel_monotone fuel1 fuel2 s :
  size s <= fuel1 -> fuel1 <= fuel2 ->
  mmtree_shape_fuel fuel2 s = mmtree_shape_fuel fuel1 s.
Proof.
elim: fuel1 fuel2 s => [|f1 IH] f2 s Hsz1 Hle.
  move: Hsz1; rewrite leqn0 => /nilP ->.
  by case: f2 Hle => //=; case: f2 => //.
case: f2 Hle => // f2 Hle.
case: s Hsz1 => [//|a s0 Hsz1].
rewrite /mmtree_shape_fuel -/mmtree_shape_fuel.
set s := a :: s0.
have Hj : mm_pos s < size s by apply: mm_pos_lt.
set j := mm_pos s.
have Hj2 : j <= size s0 by rewrite -ltnS.
have Htake_sz : size (take j s) <= f1.
  rewrite size_take Hj.
  by apply: (leq_trans Hj2); rewrite -ltnS.
have Hdrop_sz : size (drop j.+1 s) <= f1.
  rewrite size_drop /= subSS.
  by apply: (leq_trans (leq_subr _ _)); rewrite -ltnS.
have Hle1 : f1 <= f2 by [].
by rewrite (IH f2 _ Htake_sz Hle1) (IH f2 _ Hdrop_sz Hle1).
Qed.

Lemma mmtree_shape_nil : mmtree_shape [::] = [::].
Proof. by rewrite /mmtree_shape /mmtree_shape_fuel. Qed.

Lemma mmtree_shape_cons a s0 :
  let s := a :: s0 in
  let j := mm_pos s in
  mmtree_shape s =
    mm_pos s :: (mmtree_shape (take j s) ++ mmtree_shape (drop j.+1 s)).
Proof.
set s := a :: s0. set j := mm_pos s.
have Hj : j < size s by apply: mm_pos_lt.
have Hj2 : j <= size s0 by rewrite -ltnS.
have Htake_sz : size (take j s) <= size s0.
  by rewrite size_take Hj.
have Hdrop_sz : size (drop j.+1 s) <= size s0.
  by rewrite size_drop /= subSS; apply: leq_subr.
rewrite /mmtree_shape /mmtree_shape_fuel -/mmtree_shape_fuel /=.
congr (_ :: (_ ++ _)); apply: mmtree_shape_fuel_monotone => //.
Qed.

(* Seal the definitions so downstream unification (in psi_cdindex_tree.v's *)
(* heavy abstract-wrapped proofs) doesn't try to unfold them, keeping -vo *)
(* peak memory bounded.                                                    *)
Opaque mmtree_shape_fuel mmtree_shape.

Lemma size_mmtree_shape : forall s, size (mmtree_shape s) = size s.
Proof.
suff H : forall n s, size s <= n -> size (mmtree_shape s) = size s.
  by move=> s; apply: H (leqnn _).
elim=> [|n IH] s Hsz.
  by move: Hsz; rewrite leqn0 => /nilP ->; rewrite mmtree_shape_nil.
case: s Hsz => [|a s0]; first by rewrite mmtree_shape_nil.
move=> Hsz.
rewrite (mmtree_shape_cons a s0).
set s := a :: s0; set j := mm_pos s.
have Hj : j < size s by apply: mm_pos_lt.
have Hj' : j <= size s0 by rewrite -ltnS.
have Hsz_n : size s0 <= n by rewrite -ltnS.
have Htake_sz : size (take j s) <= n.
  by rewrite size_take Hj; apply: leq_trans Hj' Hsz_n.
have Hdrop_sz : size (drop j.+1 s) <= n.
  rewrite size_drop /= subSS.
  by apply: leq_trans (leq_subr _ _) Hsz_n.
rewrite /= size_cat (IH _ Htake_sz) (IH _ Hdrop_sz).
rewrite size_take Hj size_drop /= subSS.
by rewrite (subnKC Hj').
Qed.

(* ===== Order-iso preservation (the ONE heavy proof, ~0.6 GB peak) ======= *)

Lemma mmtree_shape_order_iso (s1 s2 : seq nat) :
  size s1 = size s2 -> uniq s1 -> uniq s2 ->
  (forall p q, p < size s1 -> q < size s1 ->
    (nth 0 s1 p < nth 0 s1 q) =
    (nth 0 s2 p < nth 0 s2 q)) ->
  mmtree_shape s1 = mmtree_shape s2.
Proof.
move: s1 s2.
suff Hgen : forall n s1 s2, size s1 <= n ->
  size s1 = size s2 -> uniq s1 -> uniq s2 ->
  (forall p q, p < size s1 -> q < size s1 ->
    (nth 0 s1 p < nth 0 s1 q) =
    (nth 0 s2 p < nth 0 s2 q)) ->
  mmtree_shape s1 = mmtree_shape s2.
  by move=> s1 s2; apply: (Hgen (size s1)); rewrite ?leqnn.
elim=> [|n IH] s1 s2 Hsz1 Hszeq Hu1 Hu2 Hord.
  have Hsz0 : size s1 = 0 by apply/eqP; rewrite -leqn0.
  by rewrite (size0nil Hsz0); rewrite Hsz0 in Hszeq;
     rewrite (size0nil (esym Hszeq)).
case Hs1 : s1 => [|a1 t1].
  by move: Hszeq; rewrite Hs1 /= => Hsz2;
     have -> : s2 = [::] by apply/eqP; rewrite -size_eq0 -Hsz2.
case Hs2 : s2 => [|a2 t2].
  by move: Hszeq; rewrite Hs1 Hs2 /=.
have Hne1 : a1 :: t1 <> [::] by [].
have Hszeq' : size (a1 :: t1) = size (a2 :: t2) by rewrite -Hs1 -Hs2.
subst s1 s2.
have Hmm := mm_pos_order_iso Hszeq' Hu1 Hu2 Hne1 Hord.
set m := mm_pos (a1 :: t1).
rewrite (mmtree_shape_cons a1 t1) -/m.
rewrite (mmtree_shape_cons a2 t2) -Hmm -/m.
have Hm1 : m < size (a1 :: t1) by apply: mm_pos_lt.
have Hm2 : m < size (a2 :: t2) by rewrite -Hszeq'.
congr (_ :: (_ ++ _)).
- apply: (IH _ _ _ _ _ _).
  + rewrite (size_takel (ltnW Hm1)).
    exact: leq_trans Hm1 Hsz1.
  + by rewrite (size_takel (ltnW Hm1)) (size_takel (ltnW Hm2)).
  + by move: Hu1; rewrite -{1}(cat_take_drop m (a1 :: t1))
       cat_uniq => /andP [].
  + by move: Hu2; rewrite -{1}(cat_take_drop m (a2 :: t2))
       cat_uniq => /andP [].
  + exact: order_iso_take Hm1 Hszeq' Hord.
- apply: (IH _ _ _ _ _ _).
  + rewrite size_drop /=.
    have := @leq_sub2r m.+1 _ _ Hsz1.
    rewrite subSS; move=> H.
    by apply: (leq_trans _ (leq_subr m n)); rewrite -subSS.
  + by rewrite !size_drop Hszeq'.
  + by move: Hu1;
       rewrite -{1}(cat_take_drop m.+1 (a1 :: t1))
       cat_uniq => /andP [_ /andP [_ ?]].
  + by move: Hu2;
       rewrite -{1}(cat_take_drop m.+1 (a2 :: t2))
       cat_uniq => /andP [_ /andP [_ ?]].
  + exact: order_iso_drop Hm1 Hszeq' Hord.
Qed.

Opaque mmtree_shape_order_iso.

(* ===== Decomposition: same shape ⇒ same root + same subtree shapes ====== *)

Lemma seq_cat_left_eq (T : eqType) (s1 s2 t1 t2 : seq T) :
  size s1 = size t1 -> s1 ++ s2 = t1 ++ t2 -> s1 = t1.
Proof.
move=> Hsz Heq.
have Htake : take (size s1) (s1 ++ s2) = take (size s1) (t1 ++ t2)
  by rewrite Heq.
rewrite take_size_cat // in Htake.
by rewrite Htake Hsz take_size_cat.
Qed.

Lemma seq_cat_right_eq (T : eqType) (s1 s2 t1 t2 : seq T) :
  size s1 = size t1 -> s1 ++ s2 = t1 ++ t2 -> s2 = t2.
Proof.
move=> Hsz Heq.
have Hdrop : drop (size s1) (s1 ++ s2) = drop (size s1) (t1 ++ t2)
  by rewrite Heq.
rewrite drop_size_cat // in Hdrop.
by rewrite Hdrop Hsz drop_size_cat.
Qed.

Lemma mmtree_shape_decompose s1 s2 :
  size s1 = size s2 ->
  s1 <> [::] ->
  mmtree_shape s1 = mmtree_shape s2 ->
  [/\ mm_pos s1 = mm_pos s2,
      mmtree_shape (take (mm_pos s1) s1) =
        mmtree_shape (take (mm_pos s2) s2)
    & mmtree_shape (drop (mm_pos s1).+1 s1) =
        mmtree_shape (drop (mm_pos s2).+1 s2)].
Proof.
case: s1 => [|a1 t1]; first by move=> _ /(_ erefl).
case: s2 => [|a2 t2] /=; first by [].
move=> Hszeq _ Hshape.
move: Hshape.
rewrite (mmtree_shape_cons a1 t1) (mmtree_shape_cons a2 t2).
case=> Hhead Htail.
have Hm1lt : mm_pos (a1 :: t1) < size (a1 :: t1) by apply: mm_pos_lt.
have Hm2lt : mm_pos (a2 :: t2) < size (a2 :: t2) by apply: mm_pos_lt.
have Hsz_take :
    size (mmtree_shape (take (mm_pos (a1 :: t1)) (a1 :: t1))) =
    size (mmtree_shape (take (mm_pos (a2 :: t2)) (a2 :: t2))).
  by rewrite !size_mmtree_shape !size_take Hm1lt Hm2lt Hhead.
split.
- exact: Hhead.
- exact: seq_cat_left_eq Hsz_take Htail.
- exact: seq_cat_right_eq Hsz_take Htail.
Qed.

(* ===== Property invariance under shape equality ========================= *)

Lemma has_left_child_of_shape : forall (s1 s2 : seq nat) i,
  size s1 = size s2 ->
  mmtree_shape s1 = mmtree_shape s2 ->
  has_left_child i s1 = has_left_child i s2.
Proof.
suff H : forall n s1 s2 i, size s1 <= n ->
  size s1 = size s2 ->
  mmtree_shape s1 = mmtree_shape s2 ->
  has_left_child i s1 = has_left_child i s2.
  by move=> s1 s2 i; apply: (H (size s1)); rewrite ?leqnn.
elim=> [|n IH] s1 s2 i Hsz1 Hszeq Hshape.
  have Hsz0 : size s1 = 0 by apply/eqP; rewrite -leqn0.
  by rewrite (size0nil Hsz0); rewrite Hsz0 in Hszeq;
     rewrite (size0nil (esym Hszeq)).
case Hs1 : s1 => [|a1 t1].
  by move: Hszeq; rewrite Hs1 /= => Hsz2;
     have -> : s2 = [::] by apply/eqP; rewrite -size_eq0 -Hsz2.
case Hs2 : s2 => [|a2 t2].
  by move: Hszeq; rewrite Hs1 Hs2 /=.
have Hne1 : (a1 :: t1) <> [::] by [].
have Hszeq' : size (a1 :: t1) = size (a2 :: t2) by rewrite -Hs1 -Hs2.
subst s1 s2.
have [Hmm Hltake Hldrop] := mmtree_shape_decompose Hszeq' Hne1 Hshape.
rewrite -Hmm in Hltake Hldrop.
set m := mm_pos (a1 :: t1).
rewrite -/m in Hltake Hldrop.
have Hm1 : m < size (a1 :: t1) by apply: mm_pos_lt.
have Hm2 : m < size (a2 :: t2) by rewrite -Hszeq'.
rewrite (has_left_child_cons i a1 t1) -/m.
rewrite (has_left_child_cons i a2 t2) -Hmm -/m.
case: (ltngtP i m) => Him.
- (* i < m *)
  apply: (IH _ _ _ _ _ Hltake).
  + rewrite size_takel ?(ltnW Hm1) //.
    exact: leq_trans Hm1 Hsz1.
  + by rewrite (size_takel (ltnW Hm1)) (size_takel (ltnW Hm2)).
- (* i > m *)
  apply: (IH _ _ _ _ _ Hldrop).
  + rewrite size_drop /= subSS.
    have Hszt : size t1 <= n by rewrite -ltnS.
    exact: leq_trans (leq_subr _ _) Hszt.
  + by rewrite !size_drop Hszeq'.
- (* i = m *)
  by [].
Qed.

Lemma window_size_of_shape : forall (s1 s2 : seq nat) i,
  size s1 = size s2 ->
  mmtree_shape s1 = mmtree_shape s2 ->
  window_size i s1 = window_size i s2.
Proof.
suff H : forall n s1 s2 i, size s1 <= n ->
  size s1 = size s2 ->
  mmtree_shape s1 = mmtree_shape s2 ->
  window_size i s1 = window_size i s2.
  by move=> s1 s2 i; apply: (H (size s1)); rewrite ?leqnn.
elim=> [|n IH] s1 s2 i Hsz1 Hszeq Hshape.
  have Hsz0 : size s1 = 0 by apply/eqP; rewrite -leqn0.
  by rewrite (size0nil Hsz0); rewrite Hsz0 in Hszeq;
     rewrite (size0nil (esym Hszeq)).
case Hs1 : s1 => [|a1 t1].
  by move: Hszeq; rewrite Hs1 /= => Hsz2;
     have -> : s2 = [::] by apply/eqP; rewrite -size_eq0 -Hsz2.
case Hs2 : s2 => [|a2 t2].
  by move: Hszeq; rewrite Hs1 Hs2 /=.
have Hne1 : (a1 :: t1) <> [::] by [].
have Hszeq' : size (a1 :: t1) = size (a2 :: t2) by rewrite -Hs1 -Hs2.
subst s1 s2.
have [Hmm Hltake Hldrop] := mmtree_shape_decompose Hszeq' Hne1 Hshape.
rewrite -Hmm in Hltake Hldrop.
set m := mm_pos (a1 :: t1).
rewrite -/m in Hltake Hldrop.
have Hm1 : m < size (a1 :: t1) by apply: mm_pos_lt.
have Hm2 : m < size (a2 :: t2) by rewrite -Hszeq'.
rewrite (window_size_cons i a1 t1) -/m.
rewrite (window_size_cons i a2 t2) -Hmm -/m.
case: (ltngtP i m) => Him.
- (* i < m *)
  apply: (IH _ _ _ _ _ Hltake).
  + rewrite size_takel ?(ltnW Hm1) //.
    exact: leq_trans Hm1 Hsz1.
  + by rewrite (size_takel (ltnW Hm1)) (size_takel (ltnW Hm2)).
- (* i > m *)
  apply: (IH _ _ _ _ _ Hldrop).
  + rewrite size_drop /= subSS.
    have Hszt : size t1 <= n by rewrite -ltnS.
    exact: leq_trans (leq_subr _ _) Hszt.
  + by rewrite !size_drop Hszeq'.
- (* i = m: window_size i s = size s - i, both have same size and same i = m *)
  by rewrite Hszeq'.
Qed.

Opaque has_left_child_of_shape window_size_of_shape.

(* ===== Compatibility wrapper: order-iso ⇒ has_left_child equality ====== *)
(* Used by perm_seq_bridge.v and psi_cdindex_witness.v under this name.    *)

Lemma has_left_child_order_iso (s1 s2 : seq nat) i :
  size s1 = size s2 -> uniq s1 -> uniq s2 ->
  (forall p q, p < size s1 -> q < size s1 ->
    (nth 0 s1 p < nth 0 s1 q) =
    (nth 0 s2 p < nth 0 s2 q)) ->
  has_left_child i s1 = has_left_child i s2.
Proof.
move=> Hsz Hu1 Hu2 Hord.
apply: has_left_child_of_shape; first exact: Hsz.
exact: mmtree_shape_order_iso.
Qed.

Opaque has_left_child_order_iso.

(* ===== Tree shape is preserved by ψ (the second heavy proof) =========== *)
(* Same skeleton as window_size_psi (psi_comm.v:152): nested case split    *)
(* on (j vs m), with non-root cases using take_mm_psi/drop_mm_psi and the  *)
(* root case (j = m) using mmtree_shape_order_iso for the rotated tail.   *)

Lemma mmtree_shape_psi : forall (j : nat) (w : seq nat), uniq w ->
  mmtree_shape (psi j w) = mmtree_shape w.
Proof.
suff Hgen : forall n j w, size w <= n -> uniq w ->
  mmtree_shape (psi j w) = mmtree_shape w.
  by move=> j w Hu; apply: (Hgen (size w)); rewrite ?leqnn.
elim=> [|n IH] j w Hsz Huniq.
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
have [a' [s0' Hpsi_eq]] : exists a' s0', psi j s = a' :: s0'.
  by case: (psi j s) Hpsi_ne => [//|x y] _; exists x, y.
have Hm'c : mm_pos (a' :: s0') = m by rewrite -Hpsi_eq.
rewrite Hpsi_eq.
rewrite (mmtree_shape_cons a' s0') Hm'c.
rewrite (mmtree_shape_cons a s0) -/m.
congr (_ :: (_ ++ _)).
- (* take m: shape of left subtree preserved *)
  case: (ltngtP j m) => [Hjm | Hmj | Hjeqm].
  + (* j < m: psi acts inside take m s *)
    rewrite -Hpsi_eq (take_mm_psi Hs_ne Huniq Hws_gt1 Hjm).
    apply: IH.
    * rewrite (size_takel (ltnW Hm)).
      exact: leq_trans Hm Hsz.
    * have : uniq (take m s ++ drop m s) by rewrite cat_take_drop.
      by rewrite cat_uniq => /andP [? _].
  + (* j > m: psi doesn't touch take m s *)
    by rewrite -Hpsi_eq (@take_psi m j s (ltnW Hmj)).
  + (* j = m: psi at root, take m s unchanged *)
    by rewrite -Hpsi_eq Hjeqm (@take_psi m m s (leqnn m)).
- (* drop m.+1: shape of right subtree preserved *)
  case: (ltngtP j m) => [Hjm | Hmj | Hjeqm].
  + (* j < m: psi acts entirely above drop m.+1 *)
    suff -> : drop m.+1 (a' :: s0') = drop m.+1 (a :: s0) by [].
    rewrite -Hpsi_eq.
    apply: drop_psi_above.
    apply: leq_trans (window_fits_left Hs_ne Hjm) _.
    exact: leqnSn.
  + (* j > m: psi acts on shifted index in drop m.+1 *)
    suff -> : drop m.+1 (a' :: s0') = psi (j - m - 1) (drop m.+1 (a :: s0)).
      apply: IH.
      * rewrite size_drop.
        apply: (leq_trans (leq_sub2r _ Hsz)).
        exact: leq_subr.
      * have : uniq (take m.+1 s ++ drop m.+1 s) by rewrite cat_take_drop.
        by rewrite cat_uniq => /andP [_ /andP [_ ?]].
    by rewrite -Hpsi_eq (drop_mm_psi Hs_ne Huniq Hws_gt1 Hmj).
  + (* j = m: heavy case via mmtree_shape_order_iso *)
    subst j.
    have Hws_m : window_size m s = size s - m
      by rewrite (window_size_cons m a s0) -/m ltnn eqxx.
    have Hws_drop : 1 < size (drop m s)
      by rewrite size_drop -Hws_m.
    have Hdm_ne : drop m s <> [::]
      by case: (drop m s) Hws_drop.
    have Huniq_dm : uniq (drop m s).
      have : uniq (take m s ++ drop m s) by rewrite cat_take_drop.
      by rewrite cat_uniq => /andP [_ /andP [_ ?]].
    have Hmm_drop : mm_pos (drop m s) = 0 by exact: mm_pos_drop_mm.
    have Hpsi_m_eq : psi m s = take m s ++ rank_shift_seq (drop m s).
      rewrite /psi.
      have Hwa_m : window_at m s = drop m s
        by rewrite (window_at_cons m a s0) -/m ltnn eqxx //.
      rewrite Hwa_m Hws_m.
      by rewrite subnKC ?drop_size ?cats0 // ltnW.
    have Hdrop_psi : drop m.+1 (a' :: s0') = behead (rank_shift_seq (drop m s)).
      rewrite -Hpsi_eq Hpsi_m_eq.
      rewrite drop_cat size_take Hm.
      have -> : m.+1 < m = false by rewrite ltnNge leqnSn.
      by rewrite /= subSnn drop1.
    have Hdrop_orig : drop m.+1 (a :: s0) = behead (drop m s)
      by rewrite /s -drop1 drop_drop add1n.
    rewrite Hdrop_psi Hdrop_orig.
    apply: mmtree_shape_order_iso.
    * by rewrite !size_behead size_rank_shift_seq2.
    * rewrite -drop1.
      apply: (subseq_uniq (drop_subseq _ 1)).
      by rewrite (perm_uniq (rank_shift_perm_eq _)).
    * rewrite -drop1.
      exact: (subseq_uniq (drop_subseq _ 1)).
    * (* the order-iso forall body *)
      move: Hdm_ne Hmm_drop Huniq_dm Hws_drop.
      case: (drop m s) => [//|dm_h dm_t] _ Hmm_drop Huniq_dm Hws_drop.
      move=> p q Hp Hq.
      have Hws_gt1_dm : 1 < window_size 0 (dm_h :: dm_t)
        by rewrite (window_size_cons 0 dm_h dm_t) Hmm_drop ltnn eqxx.
      have Hhead_ext :
        (head 0 (dm_h :: dm_t) == nth 0 (sort leq (dm_h :: dm_t)) 0) ||
        (head 0 (dm_h :: dm_t) ==
          nth 0 (sort leq (dm_h :: dm_t)) (size (dm_h :: dm_t)).-1).
        have H := window_head_extremum Huniq_dm Hws_gt1_dm.
        have Hwat : window_at 0 (dm_h :: dm_t) = dm_h :: dm_t
          by rewrite (window_at_cons 0 dm_h dm_t) Hmm_drop ltnn eqxx drop0.
        move: H; rewrite Hwat => H; exact: H.
      have Hp1 : p.+1 < size (dm_h :: dm_t)
        by move: Hp; rewrite size_behead size_rank_shift_seq2 ltn_predRL.
      have Hq1 : q.+1 < size (dm_h :: dm_t)
        by move: Hq; rewrite size_behead size_rank_shift_seq2 ltn_predRL.
      rewrite -[behead (rank_shift_seq _)] (drop1 (rank_shift_seq (dm_h :: dm_t))).
      rewrite -[behead (dm_h :: dm_t)](drop1 (dm_h :: dm_t)).
      rewrite !nth_drop.
      have H := rank_shift_preserves_interior_order
        Huniq_dm Hws_drop Hhead_ext (ltn0Sn q) (ltn0Sn p) Hq1 Hp1.
      by rewrite -H.
Qed.

Opaque mmtree_shape_psi.

(* ===== The 5-line corollary the refactor was for ======================= *)

Lemma has_left_child_psi j i w :
  uniq w -> has_left_child i (psi j w) = has_left_child i w.
Proof.
move=> Hu.
apply: has_left_child_of_shape; first exact: size_psi.
exact: mmtree_shape_psi.
Qed.

Opaque has_left_child_psi.
