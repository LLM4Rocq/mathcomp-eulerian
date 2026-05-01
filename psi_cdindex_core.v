(* psi_cdindex_core.v — cd-index core: re-exports defs/tree + remaining      *)
(*                                                                           *)
(* Split into psi_cdindex_defs.v (definitions), psi_cdindex_tree.v (heavy    *)
(* structural proofs), and this file (remaining lemmas + re-export).         *)
(* Downstream files can continue to Require Import psi_cdindex_core.         *)

From mathcomp Require Import all_ssreflect.
Require Import mmtree psi_core psi_comm psi_descent_v2 psi_descent_thms.
Require Export psi_cdindex_defs psi_cdindex_tree_hlc psi_cdindex_tree.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* ----- M5.5 Main theorem: Fact #3 ------------------------------------------ *)

(* -- Tree-shape invariance under apply_psis -------------------------------- *)

Lemma window_size_apply_psis ops i w :
  uniq w ->
  window_size i (apply_psis ops w) = window_size i w.
Proof.
move=> Hu; elim: ops w Hu => [//|j ops IH] w Hu /=.
by rewrite IH ?uniq_psi // window_size_psi.
Qed.

Lemma has_left_child_apply_psis ops i w :
  uniq w ->
  has_left_child i (apply_psis ops w) = has_left_child i w.
Proof.
move=> Hu; elim: ops w Hu => [//|j ops IH] w Hu /=.
by rewrite IH ?uniq_psi // has_left_child_psi.
Qed.

Lemma is_internal_apply_psis ops i w :
  uniq w ->
  is_internal i (apply_psis ops w) = is_internal i w.
Proof.
move=> Hu; rewrite /is_internal size_apply_psis.
by rewrite window_size_apply_psis.
Qed.

Lemma internal_vertices_apply_psis ops w :
  uniq w ->
  internal_vertices (apply_psis ops w) = internal_vertices w.
Proof.
move=> Hu; rewrite /internal_vertices size_apply_psis.
apply: eq_in_filter => i _.
exact: is_internal_apply_psis.
Qed.

Lemma phi_w_apply_psis ops w :
  uniq w -> phi_w (apply_psis ops w) = phi_w w.
Proof.
move=> Hu; rewrite /phi_w /phi'_w size_apply_psis.
congr [seq _ <- _ | _].
apply: eq_map => i; rewrite /classify_vertex_cde.
by rewrite is_internal_apply_psis //
           has_left_child_apply_psis.
Qed.

(* -- phi_w as a map over internal_vertices -------------------------------- *)

Lemma phi_w_as_map w :
  phi_w w =
  [seq (if has_left_child i w then D_letter else C_letter)
  | i <- internal_vertices w].
Proof.
rewrite /phi_w /phi'_w /internal_vertices.
elim: (iota 0 (size w)) => [//|i s IH] /=.
rewrite /classify_vertex_cde /is_internal.
case: (i < size w) => /=;
  case: (1 < window_size i w) => /=;
  case: (has_left_child i w) => /=;
  by rewrite ?IH.
Qed.

(* -- Sorting infrastructure ----------------------------------------------- *)

Lemma leq_seqb_total : total leq_seqb.
Proof.
move=> x y; elim: x y =>
  [|b1 s1 IH] [|b2 s2] //=.
by case: b1; case: b2 => //=.
Qed.

Lemma leq_seqb_trans : transitive leq_seqb.
Proof.
move=> y x z; elim: x y z =>
  [|b1 s1 IH] [|b2 s2] [|b3 s3] //=.
by case: b1; case: b2; case: b3 => //=; exact: IH.
Qed.

Lemma leq_seqb_anti : antisymmetric leq_seqb.
Proof.
move=> x y; elim: x y =>
  [|b1 s1 IH] [|b2 s2] //=.
by case: b1; case: b2 => //= H;
   congr (_ :: _); exact: IH.
Qed.

Lemma sort_perm_eq_leq_seqb (s1 s2 : seq (seq bool)) :
  perm_eq s1 s2 ->
  sort leq_seqb s1 = sort leq_seqb s2.
Proof.
move=> Hp; apply/perm_sort_inP => //.
- by move=> a b _ _; exact: leq_seqb_total.
- by move=> a b c _ _ _; exact: leq_seqb_trans.
- by move=> a b _ _; exact: leq_seqb_anti.
Qed.

(* -- Descent effect of psi ----------------------------------------------- *)

Lemma descent_psi_effect v w k :
  uniq w -> is_internal v w -> k < (size w).-1 ->
  is_descent_seq (psi v w) k =
    if ~~ has_left_child v w then
      if k == v then ~~ is_descent_seq w v
      else is_descent_seq w k
    else
      if k == v then is_descent_seq w v.-1
      else if k == v.-1 then is_descent_seq w v
      else is_descent_seq w k.
Proof.
move=> Hu Hint Hk.
have Hws : 1 < window_size v w
  by move: Hint; rewrite /is_internal => /andP [_ ->].
case Hlc: (has_left_child v w) => /=.
- case Hd: (is_descent_seq w v).
  + (* LR-swap2 case: descent at v moves to v.-1.                          *)
    (* Use exactly_one_descent_LR to derive ~~ is_descent_seq w v.-1.       *)
    have := descent_psi_LR_swap2 Hu Hws Hlc Hd Hk => ->.
    case: (k == v) => //.
    have Hi0 : 0 < v.
      case Hv0: v => [|n0]; last by [].
      by exfalso; rewrite Hv0 has_left_child_0 in Hlc.
    have := exactly_one_descent_LR Hu Hi0 Hlc Hws.
    rewrite Hd addbT.
    by case: (is_descent_seq w v.-1).
  + (* LR-swap1 case: ~ descent at v, so descent at v.-1.                  *)
    have := descent_psi_LR_swap1 Hu Hws Hlc (negbT Hd) Hk => ->.
    have Hi0 : 0 < v.
      case Hv0: v => [|n0]; last by [].
      by exfalso; rewrite Hv0 has_left_child_0 in Hlc.
    have := exactly_one_descent_LR Hu Hi0 Hlc Hws.
    rewrite Hd /= addbF => Hd1.
    case: (k == v); first by rewrite Hd1.
    by case: (k == v.-1).
- case Hd: (is_descent_seq w v).
  + have := descent_psi_R_remove Hu Hws (negbT Hlc) Hd Hk => ->.
    case Hkv: (k == v); first by move/eqP: Hkv => ->; rewrite Hd.
    by [].
  + have := descent_psi_R_add Hu Hws (negbT Hlc) (negbT Hd) Hk => ->.
    case Hkv: (k == v); first by move/eqP: Hkv => ->; rewrite Hd.
    by [].
Qed.

(* -- Char_mono tools ------------------------------------------------------ *)

Lemma nth_char_mono w k :
  k < (size w).-1 ->
  nth false (char_mono w) k = is_descent_seq w k.
Proof.
move=> Hk; rewrite /char_mono (nth_map 0);
  last by rewrite size_iota.
by rewrite nth_iota // add0n.
Qed.

Lemma size_char_mono w :
  size (char_mono w) = (size w).-1.
Proof. by rewrite /char_mono size_map size_iota. Qed.

(* Internal vertices live strictly inside the descent index range. *)
Lemma is_internal_lt v w : is_internal v w -> v < (size w).-1.
Proof.
move=> /andP [Hvlt Hws].
have Hwbd := window_size_bound v w.
have Hsub : 1 < size w - v by exact: leq_trans Hws Hwbd.
rewrite ltn_subRL in Hsub.
case: (size w) Hvlt Hsub => [//|n] Hvlt /=.
by rewrite addnC.
Qed.

(* Bit-level effect of psi on char_mono.                                     *)
(* C-vertex (no left child): toggles bit at position v.                      *)
(* D-vertex (has left child): swaps bits at positions v.-1 and v.            *)
Lemma char_mono_psi_effect v w k :
  uniq w -> is_internal v w -> k < (size w).-1 ->
  nth false (char_mono (psi v w)) k =
    if ~~ has_left_child v w then
      if k == v then ~~ nth false (char_mono w) v
      else nth false (char_mono w) k
    else
      if k == v then nth false (char_mono w) v.-1
      else if k == v.-1 then nth false (char_mono w) v
      else nth false (char_mono w) k.
Proof.
move=> Hu Hint Hk.
have Hvlt := is_internal_lt Hint.
have Hvm1 : v.-1 < (size w).-1 := leq_ltn_trans (leq_pred v) Hvlt.
have HkP : k < (size (psi v w)).-1 by rewrite size_psi.
rewrite (nth_char_mono HkP) (descent_psi_effect Hu Hint Hk).
case: (~~ has_left_child v w); case Hkv: (k == v).
- by rewrite (nth_char_mono Hvlt).
- by rewrite (nth_char_mono Hk).
- by rewrite (nth_char_mono Hvm1).
case Hkv1: (k == v.-1).
  by rewrite (nth_char_mono Hvlt).
by rewrite (nth_char_mono Hk).
Qed.

(* -- The last vertex has no left child ------------------------------------ *)

(* Helper: index of x in rcons s y at position size s implies x not in s. *)
Lemma index_rcons_eq_size (T : eqType) (s : seq T) y x :
  index x (rcons s y) = size s -> x \notin s.
Proof.
elim: s => [|a s IH] //=.
case Hax : (a == x) => /= Hidx; first by [].
injection Hidx => Hidx'.
have Hxn := IH Hidx'.
by rewrite in_cons eq_sym Hax /=; exact: Hxn.
Qed.

(* Helper: mm_pos can never be at the last position when prefix is non-empty. *)
(* Reason: mm_pos = last position requires both min_pos and max_pos at last, *)
(* forcing the last element to be both min and max — contradicting the      *)
(* presence of any other element.                                            *)
Lemma mm_pos_rcons_lt sl x : 0 < size sl ->
  mm_pos (rcons sl x) < size sl.
Proof.
move=> Hsl.
have Hne : rcons sl x <> [::] by case: sl Hsl.
have Hjlt := mm_pos_lt Hne.
rewrite size_rcons ltnS leq_eqVlt in Hjlt.
case/orP: Hjlt => [/eqP Hjeq|//].
exfalso.
move: Hjeq; rewrite /mm_pos.
case Hcmp: (min_pos (rcons sl x) <= max_pos (rcons sl x)) => Hjeq.
- have Hmax_eq : max_pos (rcons sl x) = size sl.
    apply/eqP; rewrite eqn_leq.
    have Hmax_lt := max_pos_lt Hne.
    rewrite size_rcons ltnS in Hmax_lt.
    by rewrite Hmax_lt -Hjeq Hcmp.
  rewrite /min_pos in Hjeq.
  rewrite /max_pos in Hmax_eq.
  set m := foldr minn (head 0 (rcons sl x)) (behead (rcons sl x)).
  set M := foldr maxn (head 0 (rcons sl x)) (behead (rcons sl x)).
  have Hm_nin : foldr minn (head 0 (rcons sl x)) (behead (rcons sl x)) \notin sl
    by apply: index_rcons_eq_size Hjeq.
  have HM_nin : foldr maxn (head 0 (rcons sl x)) (behead (rcons sl x)) \notin sl
    by apply: index_rcons_eq_size Hmax_eq.
  have Hrcons_form : rcons sl x = head 0 (rcons sl x) :: behead (rcons sl x)
    by case: (rcons sl x) Hne.
  have Hm_in : m \in rcons sl x
    by rewrite [in X in _ \in X]Hrcons_form; apply: min_in.
  have HM_in : M \in rcons sl x
    by rewrite [in X in _ \in X]Hrcons_form; apply: max_in.
  have Hm_eq : m = x.
    move: Hm_in; rewrite mem_rcons in_cons.
    case/orP => [/eqP -> //|Hin].
    by rewrite Hin in Hm_nin.
  have HM_eq : M = x.
    move: HM_in; rewrite mem_rcons in_cons.
    case/orP => [/eqP -> //|Hin].
    by rewrite Hin in HM_nin.
  case Hsl_eq : sl Hsl => [//|a sl0] _.
  have Ha_in_sl : a \in sl by rewrite Hsl_eq in_cons eqxx.
  have Ha_in : a \in rcons sl x
    by rewrite mem_rcons in_cons; apply/orP; right.
  have Hm_le_a : m <= a
    by rewrite -/m; apply: foldr_minn_le; rewrite -Hrcons_form.
  have Ha_le_M : a <= M
    by rewrite -/M; apply: foldr_maxn_ge; rewrite -Hrcons_form.
  rewrite Hm_eq in Hm_le_a.
  rewrite HM_eq in Ha_le_M.
  have Ha_eq_x : a = x by apply/eqP; rewrite eqn_leq Ha_le_M Hm_le_a.
  move/negP: Hm_nin; apply.
  by rewrite -/m Hm_eq -Ha_eq_x.
- rewrite /max_pos in Hjeq.
  have Hcmp' : ~~ (min_pos (rcons sl x) <= max_pos (rcons sl x))
    by rewrite Hcmp.
  rewrite -ltnNge in Hcmp'.
  have Hmin_eq : min_pos (rcons sl x) = size sl.
    apply/eqP; rewrite eqn_leq.
    have Hmin_lt := min_pos_lt Hne.
    rewrite size_rcons ltnS in Hmin_lt.
    by rewrite Hmin_lt /max_pos -Hjeq ltnW //.
  rewrite /min_pos in Hmin_eq.
  set m := foldr minn (head 0 (rcons sl x)) (behead (rcons sl x)).
  set M := foldr maxn (head 0 (rcons sl x)) (behead (rcons sl x)).
  have Hm_nin : m \notin sl by apply: index_rcons_eq_size Hmin_eq.
  have HM_nin : M \notin sl by apply: index_rcons_eq_size Hjeq.
  have Hrcons_form : rcons sl x = head 0 (rcons sl x) :: behead (rcons sl x)
    by case: (rcons sl x) Hne.
  have Hm_in : m \in rcons sl x
    by rewrite [in X in _ \in X]Hrcons_form; apply: min_in.
  have HM_in : M \in rcons sl x
    by rewrite [in X in _ \in X]Hrcons_form; apply: max_in.
  have Hm_eq : m = x.
    move: Hm_in; rewrite mem_rcons in_cons.
    case/orP => [/eqP -> //|Hin].
    by rewrite Hin in Hm_nin.
  have HM_eq : M = x.
    move: HM_in; rewrite mem_rcons in_cons.
    case/orP => [/eqP -> //|Hin].
    by rewrite Hin in HM_nin.
  case Hsl_eq : sl Hsl => [//|a sl0] _.
  have Ha_in_sl : a \in sl by rewrite Hsl_eq in_cons eqxx.
  have Ha_in : a \in rcons sl x
    by rewrite mem_rcons in_cons; apply/orP; right.
  have Hm_le_a : m <= a
    by rewrite -/m; apply: foldr_minn_le; rewrite -Hrcons_form.
  have Ha_le_M : a <= M
    by rewrite -/M; apply: foldr_maxn_ge; rewrite -Hrcons_form.
  rewrite Hm_eq in Hm_le_a.
  rewrite HM_eq in Ha_le_M.
  have Ha_eq_x : a = x by apply/eqP; rewrite eqn_leq Ha_le_M Hm_le_a.
  move/negP: Hm_nin; apply.
  by rewrite -/m Hm_eq -Ha_eq_x.
Qed.

(* Tree-level helper: in any valid mmtree, the last in-order position has *)
(* no left child. Proof by structural induction on the tree.              *)

Lemma has_left_child_t_last_valid : forall t : mmtree nat,
  valid_mm t ->
  0 < size (mmtree_to_seq t) ->
  has_left_child_t (size (mmtree_to_seq t)).-1 t = false.
Proof.
elim => [|l IHl x r IHr] //=.
case=> Hmm [Hvl Hvr] _.
rewrite size_cat /= addnS /=.
case Hszr : (size (mmtree_to_seq r)) => [|n].
- (* size sr = 0: by valid_mm + mm_pos_rcons_lt, force size sl = 0. *)
  have Hszl_zero : size (mmtree_to_seq l) = 0.
    have Hszr_nil : mmtree_to_seq r = [::]
      by move: Hszr; case: (mmtree_to_seq r).
    rewrite Hszr_nil cats1 in Hmm.
    case Hszl : (size (mmtree_to_seq l)) Hmm => [//|m] Hmm.
    exfalso.
    have Hsl_pos : 0 < size (mmtree_to_seq l) by rewrite Hszl.
    have Hjlt := mm_pos_rcons_lt x Hsl_pos.
    by rewrite Hmm Hszl ltnn in Hjlt.
  rewrite Hszl_zero /= addn0 /=.
  exact: has_left_child_t_0.
- (* size sr = n.+1: last position is in r *)
  rewrite addnS /=.
  have Hgt2 : size (mmtree_to_seq l) < (size (mmtree_to_seq l) + n).+1
    by rewrite ltnS leq_addr.
  rewrite (@has_left_child_t_Node_gt l x r _ Hgt2).
  rewrite subSS.
  have -> : size (mmtree_to_seq l) + n - size (mmtree_to_seq l) = n
    by rewrite addnC addnK.
  have -> : n = (size (mmtree_to_seq r)).-1 by rewrite Hszr.
  apply: IHr; first exact: Hvr.
  by rewrite Hszr.
Qed.

Lemma has_left_child_last w :
  0 < size w ->
  has_left_child (size w).-1 w = false.
Proof.
move=> Hne.
have Hroundtrip : mmtree_to_seq (mmtree_of_seq_mm w) = w
  by exact: mmtree_of_seq_mmK.
have Hv : valid_mm (mmtree_of_seq_mm w) by exact: valid_mm_build.
rewrite -Hroundtrip (has_left_child_t_eq _ Hv).
apply: has_left_child_t_last_valid; first exact: Hv.
by rewrite Hroundtrip.
Qed.

Lemma has_left_child_last_fuel :
  forall fuel w, size w <= fuel -> 0 < size w ->
  has_left_child_fuel fuel (size w).-1 w = false.
Proof.
move=> fuel w Hsz Hne.
have Heq : has_left_child_fuel fuel (size w).-1 w =
           has_left_child_fuel (size w) (size w).-1 w
  by apply: has_left_child_fuel_monotone Hsz.
rewrite Heq.
exact: (has_left_child_last Hne).
Qed.

(* -- Penultimate vertex is internal --------------------------------------- *)

Lemma last_vertex_internal w :
  uniq w -> 2 <= size w ->
  is_internal (size w).-2 w.
Proof.
move=> Hu Hsz.
apply/negPn/negP => Hep.
have Hk : (size w).-2.+1 < size w
  by case: (size w) Hsz => [|[|n]].
have Hklast : (size w).-2.+1 = (size w).-1
  by case: (size w) Hsz => [|[|n]].
have := endpoint_implies_next_has_left_child
  Hu Hk Hep.
rewrite Hklast => Hlc.
have Hne : 0 < size w
  by apply: leq_ltn_trans _ Hsz.
by rewrite has_left_child_last // in Hlc.
Qed.

(* expand_cde_rcons_C and expand_cde_rcons_D have been removed.            *)
(* Both claimed that appending a letter at the END of a cd-word commutes   *)
(* with prepending a letter — but `expand_cde` recurses on the FIRST       *)
(* letter, so the OUTPUT ORDER differs.  Computationally verified false:   *)
(*   expand_cde (rcons [C_letter] C_letter) = [[ff];[ft];[tf];[tt]]        *)
(*   ([seq s ++ [::false] | s <- expand_cde [C_letter]]                    *)
(*      ++ [seq s ++ [::true] | s <- expand_cde [C_letter]]) =             *)
(*       [[ff];[tf];[ft];[tt]]                                              *)
(*   These differ at positions 1, 2.                                       *)
(* The lemmas were unused outside this file, so removed entirely.          *)

(* -- fact3: helper infrastructure ---------------------------------------- *)

(* has_left_child implies is_internal *)
Lemma has_left_child_is_internal i w :
  i < size w -> has_left_child i w -> is_internal i w.
Proof.
have Hgen : forall t : mmtree nat, valid_mm t ->
  forall i0, i0 < size (mmtree_to_seq t) ->
  has_left_child_t i0 t -> 1 < window_size_t i0 t.
  elim => [//|l IHl x r IHr] /=.
  case=> Hmm [Hvl Hvr] i0 Hi0 Hlc0.
  rewrite size_cat /= addnS in Hi0.
  case: (ltngtP i0 (size (mmtree_to_seq l))) => Hil.
  + rewrite (@window_size_t_Node_lt l x r i0 Hil).
    apply: IHl => //.
    by rewrite (@has_left_child_t_Node_lt l x r i0 Hil) in Hlc0.
  + rewrite (@window_size_t_Node_gt l x r i0 Hil).
    rewrite (@has_left_child_t_Node_gt l x r i0 Hil) in Hlc0.
    apply: IHr => //.
    rewrite ltn_subLR; last exact: Hil.
    by rewrite addSn.
  + rewrite Hil (@window_size_t_Node_eq l x r) ltnS.
    rewrite Hil (@has_left_child_t_Node_eq l x r) in Hlc0.
    case Hszr : (size (mmtree_to_seq r)) => [|n0]; last by [].
    exfalso.
    have Hszr_nil : mmtree_to_seq r = [::]
      by move: Hszr; case: (mmtree_to_seq r).
    rewrite Hszr_nil cats1 in Hmm.
    have Hsl_pos : 0 < size (mmtree_to_seq l) by exact: Hlc0.
    have Hjlt := mm_pos_rcons_lt x Hsl_pos.
    by rewrite Hmm ltnn in Hjlt.
move=> Hi Hlc.
rewrite /is_internal Hi /=.
have Hroundtrip : mmtree_to_seq (mmtree_of_seq_mm w) = w
  by exact: mmtree_of_seq_mmK.
have Hv : valid_mm (mmtree_of_seq_mm w) by exact: valid_mm_build.
rewrite -Hroundtrip (window_size_t_eq i Hv).
apply: (Hgen _ Hv); first by rewrite Hroundtrip.
by rewrite -(has_left_child_t_eq i Hv) Hroundtrip.
Qed.

(* Every endpoint k < (size w).-1 is the predecessor of a    *)
(* D-type internal vertex at k+1 (when w is uniq).            *)
Lemma endpoint_succ_is_D_internal k w :
  uniq w -> k.+1 < size w -> ~~ is_internal k w ->
  is_internal k.+1 w && has_left_child k.+1 w.
Proof.
move=> Hu Hk1 Hep.
have Hlc := endpoint_implies_next_has_left_child Hu Hk1 Hep.
by rewrite (has_left_child_is_internal Hk1 Hlc) Hlc.
Qed.

(* expand_cde_cat removed: unused outside this file. *)

(* -- fact3: size lemmas --------------------------------------------------- *)

Lemma size_powerset_of (ivs : seq nat) :
  size (foldl (fun acc i =>
    acc ++ [seq s ++ [:: i] | s <- acc]) [:: [::]] ivs)
  = 2 ^ size ivs.
Proof.
have Hgen : forall acc : seq (seq nat),
  size (foldl (fun (acc' : seq (seq nat)) (i : nat) =>
    acc' ++ [seq s ++ [:: i] | s <- acc']) acc ivs) =
  size acc * 2 ^ size ivs.
  elim: ivs => [|v ivs IH] acc //=.
    by rewrite expn0 muln1.
  rewrite IH size_cat size_map.
  rewrite expnS mulnCA.
  by rewrite mulnA mul2n addnn.
by rewrite Hgen /= mul1n.
Qed.

Lemma size_powerset_internal w :
  size (powerset_internal w) = 2 ^ size (internal_vertices w).
Proof. exact: size_powerset_of. Qed.

Lemma uniq_powerset_of (ivs : seq nat) :
  uniq ivs ->
  uniq (foldl (fun acc i =>
    acc ++ [seq s ++ [:: i] | s <- acc]) [:: [::]] ivs).
Proof.
have Hgen : forall (ivs0 : seq nat) (acc : seq (seq nat)),
  uniq ivs0 -> uniq acc ->
  (forall s, s \in acc -> all (fun x : nat => x \notin ivs0) s) ->
  uniq (foldl (fun (acc' : seq (seq nat)) (i : nat) =>
    acc' ++ [seq s ++ [:: i] | s <- acc']) acc ivs0).
  elim=> [|j ivs0 IH] acc //=.
  move=> /andP[Hj Hivs] Huacc Hdisj.
  apply: IH => //.
    rewrite cat_uniq Huacc /=.
    apply/andP; split.
      apply/hasPn => x /mapP [s Hs ->{x}].
      apply/negP => Hxa.
      have := Hdisj _ Hxa => /allP /(_ j).
      have Hjmem : j \in s ++ [:: j] by rewrite mem_cat inE eqxx orbT.
      by move/(_ Hjmem); rewrite inE eqxx.
    have -> : [seq s ++ [:: j] | s <- acc] = [seq rcons s j | s <- acc].
      by apply: eq_map => s; rewrite cats1.
    by rewrite map_inj_uniq //; exact: rcons_injl.
  move=> s' /[!mem_cat] /orP [Hs'a | /mapP [s Hs ->{s'}]].
    have := Hdisj _ Hs'a => /allP Hall.
    apply/allP => x Hx; have := Hall _ Hx.
    by rewrite inE negb_or => /andP [_ ->].
  apply/allP => x; rewrite mem_cat => /orP [Hxs | Hxj].
    have := Hdisj _ Hs => /allP /(_ x Hxs).
    by rewrite inE negb_or => /andP [_ ->].
  by rewrite mem_seq1 in Hxj; move/eqP: Hxj => -> .
move=> Huniq; apply: Hgen => // s.
by rewrite mem_seq1 => /eqP -> .
Qed.

Lemma uniq_powerset_internal w : uniq (powerset_internal w).
Proof. by apply: uniq_powerset_of; apply: filter_uniq; apply: iota_uniq. Qed.

(* Every element of powerset_internal is a subset of internal_vertices.       *)
Lemma subset_powerset_of (ivs : seq nat) :
  forall ss, ss \in foldl (fun acc i =>
    acc ++ [seq s ++ [:: i] | s <- acc]) [:: [::]] ivs ->
  {subset ss <= ivs}.
Proof.
have Hgen : forall (ivs0 : seq nat) (acc : seq (seq nat)) (used : seq nat),
  (forall s, s \in acc -> {subset s <= used}) ->
  forall ss, ss \in foldl (fun (acc' : seq (seq nat)) (i : nat) =>
    acc' ++ [seq s ++ [:: i] | s <- acc']) acc ivs0 ->
  {subset ss <= used ++ ivs0}.
  elim=> [|j ivs0 IH] acc used Hacc ss /=.
    by rewrite cats0; exact: Hacc.
  move=> Hss.
  have HIH : {subset ss <= (used ++ [:: j]) ++ ivs0}.
    apply: IH Hss => s.
    rewrite mem_cat => /orP [Hsa | /mapP [s' Hs' Hseq]].
      move=> x Hxs; rewrite mem_cat (Hacc _ Hsa _ Hxs) //.
    move=> x; rewrite Hseq mem_cat => /orP [Hxs' | Hxj].
      by rewrite mem_cat (Hacc _ Hs' _ Hxs').
    rewrite mem_seq1 in Hxj; move/eqP: Hxj => ->.
    by rewrite !mem_cat mem_seq1 eqxx /= orbT.
  by move=> x /HIH; rewrite -catA.
move=> ss Hss.
have := Hgen ivs [:: [::]] [::] _ ss Hss.
rewrite cat0s; apply.
by move=> s; rewrite mem_seq1 => /eqP -> x //.
Qed.

Lemma subset_powerset_internal w ss :
  ss \in powerset_internal w -> {subset ss <= internal_vertices w}.
Proof. exact: subset_powerset_of. Qed.

(* Every element of powerset_internal is a subseq of internal_vertices.       *)
Lemma subseq_powerset_of (ivs : seq nat) :
  forall ss, ss \in foldl (fun acc i =>
    acc ++ [seq s ++ [:: i] | s <- acc]) [:: [::]] ivs ->
  subseq ss ivs.
Proof.
have Hgen : forall (ivs0 : seq nat) (acc : seq (seq nat)) (used : seq nat),
  (forall s, s \in acc -> subseq s used) ->
  forall ss, ss \in foldl (fun (acc' : seq (seq nat)) (i : nat) =>
    acc' ++ [seq s ++ [:: i] | s <- acc']) acc ivs0 ->
  subseq ss (used ++ ivs0).
  elim=> [|j ivs0 IH] acc used Hacc ss /=.
    by rewrite cats0; exact: Hacc.
  move=> Hss.
  have HIH : subseq ss ((used ++ [:: j]) ++ ivs0).
    apply: IH Hss => s.
    rewrite mem_cat => /orP [Hsa | /mapP [s' Hs' Hseq]].
      apply: subseq_trans (Hacc _ Hsa) _.
      exact: prefix_subseq.
    rewrite Hseq.
    by apply: cat_subseq; [exact: Hacc | exact: subseq_refl].
  by rewrite -catA /= in HIH.
move=> ss Hss.
have := Hgen ivs [:: [::]] [::] _ ss Hss.
rewrite cat0s; apply.
by move=> s; rewrite mem_seq1 => /eqP ->.
Qed.

Lemma subseq_powerset_internal w ss :
  ss \in powerset_internal w -> subseq ss (internal_vertices w).
Proof. exact: subseq_powerset_of. Qed.

(* Bit-level recovery for a C-vertex: bit v of char_mono(apply_psis ss w)     *)
(* equals the original descent bit XOR the indicator of v in ss.              *)
Lemma char_mono_apply_psis_C_bit ss w v :
  uniq w -> uniq ss ->
  (forall i, i \in ss -> is_internal i w) ->
  is_internal v w ->
  ~~ has_left_child v w ->
  nth false (char_mono (apply_psis ss w)) v =
    is_descent_seq w v (+) (v \in ss).
Proof.
elim: ss w => [|u ss IH] w Hu Huss Hint Hintv Hcv.
  rewrite /= addbF.
  by rewrite (nth_char_mono (is_internal_lt Hintv)).
move: Huss => /= /andP [Hunin Husss].
have Hintu : is_internal u w by apply: Hint; rewrite mem_head.
have Hupsi : uniq (psi u w) := uniq_psi u Hu.
have Hint_psi : forall i, i \in ss -> is_internal i (psi u w).
  move=> i Hi.
  rewrite -[psi u w]/(apply_psis [::u] w) is_internal_apply_psis //.
  by apply: Hint; rewrite in_cons Hi orbT.
have Hintv_psi : is_internal v (psi u w).
  by rewrite -[psi u w]/(apply_psis [::u] w) is_internal_apply_psis.
have Hcv_psi : ~~ has_left_child v (psi u w).
  by rewrite -[psi u w]/(apply_psis [::u] w) has_left_child_apply_psis.
rewrite /= -/(apply_psis _ _).
rewrite (IH (psi u w) Hupsi Husss Hint_psi Hintv_psi Hcv_psi).
rewrite (descent_psi_effect Hu Hintu (is_internal_lt Hintv)).
rewrite in_cons.
case Hlcu: (has_left_child u w) => /=.
- have Hvu_neq : (v == u) = false.
    apply: negbTE; apply: contraTneq Hcv => ->.
    by rewrite Hlcu.
  have Hvum1_neq : (v == u.-1) = false.
    apply: negbTE; apply: contraTneq Hintv => ->.
    have Hu_pos : 0 < u.
      case Hu0: u Hlcu => [|n] //=.
      by rewrite has_left_child_0.
    by have := LR_pred_is_endpoint Hu Hu_pos Hintu Hlcu.
  by rewrite Hvu_neq Hvum1_neq.
case Hvu: (v == u) => /=.
- move/eqP: Hvu => Hvu.
  by rewrite Hvu (negbTE Hunin) /= addbT addbF.
by [].
Qed.

(* Bit-level recovery for a D-vertex at position v.-1: predecessor bit        *)
(* depends on whether v is in ss (swap behaviour).                            *)
Lemma char_mono_apply_psis_D_bit_pred ss w v :
  uniq w -> uniq ss ->
  (forall i, i \in ss -> is_internal i w) ->
  is_internal v w ->
  has_left_child v w ->
  nth false (char_mono (apply_psis ss w)) v.-1 =
    is_descent_seq w (if v \in ss then v else v.-1).
Proof.
elim: ss w => [|u ss IH] w Hu Huss Hint Hintv Hdv.
  rewrite /=.
  by rewrite (nth_char_mono (leq_ltn_trans (leq_pred v) (is_internal_lt Hintv))).
move: Huss => /= /andP [Hunin Husss].
have Hintu : is_internal u w by apply: Hint; rewrite mem_head.
have Hupsi : uniq (psi u w) := uniq_psi u Hu.
have Hint_psi : forall i, i \in ss -> is_internal i (psi u w).
  move=> i Hi.
  rewrite -[psi u w]/(apply_psis [::u] w) is_internal_apply_psis //.
  by apply: Hint; rewrite in_cons Hi orbT.
have Hintv_psi : is_internal v (psi u w).
  by rewrite -[psi u w]/(apply_psis [::u] w) is_internal_apply_psis.
have Hdv_psi : has_left_child v (psi u w).
  by rewrite -[psi u w]/(apply_psis [::u] w) has_left_child_apply_psis.
rewrite /= -/(apply_psis _ _).
rewrite (IH (psi u w) Hupsi Husss Hint_psi Hintv_psi Hdv_psi).
have Hv_pos : 0 < v.
  case Hv0: v Hdv => [|n] //=.
  by rewrite has_left_child_0.
have Hv_lt := is_internal_lt Hintv.
have Hvm1_lt : v.-1 < (size w).-1 := leq_ltn_trans (leq_pred v) Hv_lt.
have Hvm1u_neq : u != v.-1.
  apply: contraTneq Hintu => ->.
  by have := LR_pred_is_endpoint Hu Hv_pos Hintv Hdv.
rewrite in_cons.
case Hvss: (v \in ss) => /=.
- rewrite orbT.
  rewrite (descent_psi_effect Hu Hintu Hv_lt).
  case Hvu: (v == u).
    by move/eqP: Hvu => Hvu; move: Hunin; rewrite -Hvu Hvss.
  case Hlcu: (has_left_child u w) => //.
  have Hu_pos : 0 < u.
    case Hu0: u Hlcu => [|n] //=.
    by rewrite has_left_child_0.
  have Hvum1 : (v == u.-1) = false.
    apply: negbTE; apply: contraTneq Hintv => ->.
    by have := LR_pred_is_endpoint Hu Hu_pos Hintu Hlcu.
  by rewrite Hvum1.
- rewrite orbF.
  rewrite (descent_psi_effect Hu Hintu Hvm1_lt).
  case Hvu: (v == u) => /=.
  + move/eqP: Hvu => Heq.
    have Hlcu : has_left_child u w by rewrite -Heq.
    rewrite Hlcu.
    have Hvm1_neq_v : (v.-1 == v) = false.
      by apply: negbTE; rewrite neq_ltn ltn_predL Hv_pos.
    by rewrite -Heq Hvm1_neq_v eqxx.
  + have Hvm1u : (v.-1 == u) = false.
      by apply: negbTE; rewrite eq_sym; exact: Hvm1u_neq.
    rewrite Hvm1u.
    case Hlcu: (has_left_child u w) => //.
    have Hu_pos : 0 < u.
      case Hu0: u Hlcu => [|n] //=.
      by rewrite has_left_child_0.
    have Hvm1um1 : (v.-1 == u.-1) = false.
      apply: negbTE; apply/eqP => H.
      move: Hvu; suff -> : v = u by rewrite eqxx.
      by rewrite -(prednK Hv_pos) -(prednK Hu_pos) H.
    by rewrite Hvm1um1.
Qed.

(* Bit-level recovery for a D-vertex at position v: self bit depends on       *)
(* whether v is in ss (swap behaviour).                                       *)
Lemma char_mono_apply_psis_D_bit_self ss w v :
  uniq w -> uniq ss ->
  (forall i, i \in ss -> is_internal i w) ->
  is_internal v w ->
  has_left_child v w ->
  nth false (char_mono (apply_psis ss w)) v =
    is_descent_seq w (if v \in ss then v.-1 else v).
Proof.
elim: ss w => [|u ss IH] w Hu Huss Hint Hintv Hdv.
  rewrite /=.
  by rewrite (nth_char_mono (is_internal_lt Hintv)).
move: Huss => /= /andP [Hunin Husss].
have Hintu : is_internal u w by apply: Hint; rewrite mem_head.
have Hupsi : uniq (psi u w) := uniq_psi u Hu.
have Hint_psi : forall i, i \in ss -> is_internal i (psi u w).
  move=> i Hi.
  rewrite -[psi u w]/(apply_psis [::u] w) is_internal_apply_psis //.
  by apply: Hint; rewrite in_cons Hi orbT.
have Hintv_psi : is_internal v (psi u w).
  by rewrite -[psi u w]/(apply_psis [::u] w) is_internal_apply_psis.
have Hdv_psi : has_left_child v (psi u w).
  by rewrite -[psi u w]/(apply_psis [::u] w) has_left_child_apply_psis.
rewrite /= -/(apply_psis _ _).
rewrite (IH (psi u w) Hupsi Husss Hint_psi Hintv_psi Hdv_psi).
have Hv_pos : 0 < v.
  case Hv0: v Hdv => [|n] //=.
  by rewrite has_left_child_0.
have Hv_lt := is_internal_lt Hintv.
have Hvm1_lt : v.-1 < (size w).-1 := leq_ltn_trans (leq_pred v) Hv_lt.
have Hvm1u_neq : u != v.-1.
  apply: contraTneq Hintu => ->.
  by have := LR_pred_is_endpoint Hu Hv_pos Hintv Hdv.
rewrite in_cons.
case Hvss: (v \in ss) => /=.
- rewrite orbT.
  rewrite (descent_psi_effect Hu Hintu Hvm1_lt).
  case Hvu: (v == u).
    by move/eqP: Hvu => Hvu; move: Hunin; rewrite -Hvu Hvss.
  have Hvm1u : (v.-1 == u) = false.
    by apply: negbTE; rewrite eq_sym; exact: Hvm1u_neq.
  rewrite Hvm1u.
  case Hlcu: (has_left_child u w) => //.
  have Hu_pos : 0 < u.
    case Hu0: u Hlcu => [|n] //=.
    by rewrite has_left_child_0.
  have Hvm1um1 : (v.-1 == u.-1) = false.
    apply: negbTE; apply/eqP => H.
    move: Hvu; suff -> : v = u by rewrite eqxx.
    by rewrite -(prednK Hv_pos) -(prednK Hu_pos) H.
  by rewrite Hvm1um1.
- rewrite orbF.
  rewrite (descent_psi_effect Hu Hintu Hv_lt).
  case Hvu: (v == u) => /=.
  + move/eqP: Hvu => Heq.
    have Hlcu : has_left_child u w by rewrite -Heq.
    by rewrite Hlcu -Heq.
  + case Hlcu: (has_left_child u w) => //.
    have Hu_pos : 0 < u.
      case Hu0: u Hlcu => [|n] //=.
      by rewrite has_left_child_0.
    have Hvum1 : (v == u.-1) = false.
      apply: negbTE; apply: contraTneq Hintv => ->.
      by have := LR_pred_is_endpoint Hu Hu_pos Hintu Hlcu.
    by rewrite Hvum1.
Qed.

Lemma size_expand_cde letters :
  size (expand_cde letters) =
  2 ^ size [seq l <- letters
           | match l with E_letter => false
                        | _ => true end].
Proof.
elim: letters => [|[||] l IH] //=.
- rewrite size_cat !size_map IH expnS.
  by rewrite mul2n -addnn.
- rewrite size_cat !size_map IH expnS.
  by rewrite mul2n -addnn.
Qed.

Lemma size_phi_w w :
  size (phi_w w) = size (internal_vertices w).
Proof. by rewrite phi_w_as_map size_map. Qed.

Lemma size_expand_cde_phi_w w :
  size (expand_cde (phi_w w)) =
  2 ^ size (internal_vertices w).
Proof.
rewrite size_expand_cde.
congr (2 ^ _).
rewrite phi_w_as_map filter_map size_map size_filter.
rewrite -[RHS](count_predT (internal_vertices w)).
apply: eq_in_count => i _ /=.
by case: (has_left_child i w).
Qed.

(* -- fact3: the proof ----------------------------------------------------- *)

Definition check_fact3 (w : seq nat) : bool :=
  sort leq_seqb
    [seq char_mono (apply_psis ss w)
    | ss <- powerset_internal w]
  ==
  sort leq_seqb (expand_cde (phi_w w)).

(* check_fact3 is correct by construction *)
Lemma check_fact3P w :
  reflect
    (sort leq_seqb
      [seq char_mono (apply_psis ss w)
      | ss <- powerset_internal w]
    =
    sort leq_seqb (expand_cde (phi_w w)))
    (check_fact3 w).
Proof. exact: eqP. Qed.

(* Base case for check_fact3: size <= 1 is trivial. *)
Lemma check_fact3_size1 w :
  size w <= 1 -> check_fact3 w.
Proof.
case: w => [|a [|b s]] //= _.
apply/eqP.
have Hws : window_size 0 [:: a] = 1.
  apply/eqP; rewrite eqn_leq.
  apply/andP; split.
    have := window_size_bound 0 [:: a].
    by rewrite subn0.
  by apply: window_size_gt0.
have Hphi : phi_w [:: a] = [::].
  rewrite /phi_w /phi'_w /= /classify_vertex_cde /is_internal /=.
  by rewrite Hws.
have Hpw : powerset_internal [:: a] = [:: [::]].
  rewrite /powerset_internal /internal_vertices /=.
  by rewrite /is_internal /= Hws.
rewrite Hphi Hpw /=.
by rewrite /apply_psis /char_mono /=.
Qed.

(* check_fact3_true, fact3, and examples are in psi_cdindex_support.v     *)
(* (after phi_w_support_general) where the structural proof               *)
(* infrastructure is available.                                           *)
