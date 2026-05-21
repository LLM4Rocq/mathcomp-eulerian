(* psi_descent_v2.v — Option A: Structural recursion on mmtree              *)
(* Replaces fuel-based strong induction with structural induction on the    *)
(* min-max tree, producing O(n) proof terms instead of O(3^n).             *)
(*                                                                          *)
(* Strategy: The 5 structural properties (tree_props) are proved by         *)
(* structural induction on `mmtree nat`. At each `Node l x r`, the         *)
(* in-order traversal is `sl ++ x :: sr`, and validity says                *)
(* `mm_pos s = size sl`. The cons-unfolding lemmas (window_size_cons etc.) *)
(* are applied once per node and hidden behind Opaque bridges.             *)

From mathcomp Require Import all_ssreflect.
Require Import mmtree psi_core psi_comm.
(* Re-export so that downstream psi_* files transitively get
   [is_descent_seq] without each having to import perm_seq_basics. *)
From mathcomp_eulerian Require Export perm_seq_basics.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* ===== Descent predicate =====

   [is_descent_seq] was previously defined here; it now lives in
   [perm_seq_basics.v] so that the §1.4 closure (foata, qfact, qeul,
   altsub) can use it without importing the cd-index chain.  See
   [docs/plans/CD_INDEX_SEPARATION_PLAN.md]. *)

(** [is_descent_seq_ex] : the descent set of [[3;1;4;7;5;9;2;6]] is
    [{0, 3, 5}], a concrete sanity check. *)
Example is_descent_seq_ex :
  let w := [:: 3; 1; 4; 7; 5; 9; 2; 6] in
  [seq k <- iota 0 7 | is_descent_seq w k] = [:: 0; 3; 5].
Proof. by []. Qed.

(* ===== has_left_child (unchanged from original) ===== *)

(** [has_left_child_fuel fuel i s] tests, by fuel-bounded recursion on
    [mm_pos], whether the vertex at in-order position [i] of [M(s)] has a
    left child (equivalent to it being an LR vertex). *)
Fixpoint has_left_child_fuel (fuel : nat) (i : nat) (s : seq nat) : bool :=
  match fuel with
  | 0 => false
  | fuel'.+1 =>
      match s with
      | [::] => false
      | _ :: _ =>
          let j := mm_pos s in
          if i < j then has_left_child_fuel fuel' i (take j s)
          else if i == j then (0 < j)
          else has_left_child_fuel fuel' (i - j - 1) (drop j.+1 s)
      end
  end.

(** [has_left_child i w] : the vertex at in-order position [i] of [M(w)]
    has a left child.  Used to dispatch the descent-effect of [psi_i]
    into LR (with left child) and R (right-child only) cases. *)
Definition has_left_child (i : nat) (w : seq nat) : bool :=
  has_left_child_fuel (size w) i w.

(** [has_left_child_fuel_0] : the vertex at in-order position [0] never
    has a left child (it is the leftmost vertex). *)
Lemma has_left_child_fuel_0 : forall fuel s,
  has_left_child_fuel fuel 0 s = false.
Proof.
elim=> [//|fuel IH] [//|a s0].
by simpl; case: ifP => Hlt; [apply: IH | case: ifP].
Qed.

(** [has_left_child_0] : top-level corollary of [has_left_child_fuel_0]
    -- position [0] never has a left child. *)
Lemma has_left_child_0 s : has_left_child 0 s = false.
Proof. exact: has_left_child_fuel_0. Qed.

(** [has_left_child_fuel_monotone] : independence of fuel above the input
    size, the [has_left_child] analogue of [window_size_fuel_monotone]. *)
Lemma has_left_child_fuel_monotone fuel1 fuel2 i s :
  size s <= fuel1 -> fuel1 <= fuel2 ->
  has_left_child_fuel fuel2 i s = has_left_child_fuel fuel1 i s.
Proof.
elim: fuel1 fuel2 i s => [| f1 IH] f2 i s Hsz1 Hle.
  move: Hsz1; rewrite leqn0 => /nilP ->.
  by case: f2 Hle.
case: f2 Hle => // f2 Hle.
case: s Hsz1 => [// | a s0 Hsz1] /=.
set s := a :: s0.
have Hj : mm_pos s < size s by apply: mm_pos_lt.
set j := mm_pos s.
have Hj2 : j <= size s0 by rewrite -ltnS.
have Htake_sz : size (take j s) <= f1.
  rewrite size_take Hj.
  by apply: (leq_trans Hj2); rewrite -ltnS.
have Hdrop_sz : size (drop j s0) <= f1.
  rewrite size_drop.
  by apply: (leq_trans (leq_subr _ _)); rewrite -ltnS.
have Hle1 : f1 <= f2 by [].
case: ifP => _.
  by apply: IH.
case: ifP => _ //.
by apply: IH.
Qed.

(** [has_left_child_cons] : structural unfolding of [has_left_child] on
    a [cons] by the [mm_pos] split, mirroring [window_size_cons]. *)
Lemma has_left_child_cons i a s0 :
  let s := a :: s0 in
  let j := mm_pos s in
  has_left_child i s =
    if i < j then has_left_child i (take j s)
    else if i == j then (0 < j)
    else has_left_child (i - j - 1) (drop j.+1 s).
Proof.
set s := a :: s0. set j := mm_pos s.
have Hj : j < size s by apply: mm_pos_lt.
have Hj2 : j <= size s0 by rewrite -ltnS.
have Htake_sz : size (take j s) <= size s0.
  by rewrite size_take Hj.
have Hdrop_sz : size (drop j s0) <= size s0.
  by rewrite size_drop; apply: leq_subr.
rewrite /has_left_child /= -/j.
case: ifP => _.
  abstract (apply: has_left_child_fuel_monotone => //).
case: ifP => _ //.
abstract (apply: has_left_child_fuel_monotone => //).
Qed.

(** [has_left_child_false] : position 2 in [[3;1;4;7;5;9;2;6]] is an R
    vertex (no left child). *)
Example has_left_child_false :
  has_left_child 2 [:: 3; 1; 4; 7; 5; 9; 2; 6] = false.
Proof. by []. Qed.

(** [has_left_child_true] : position 5 in the same word is an LR vertex. *)
Example has_left_child_true :
  has_left_child 5 [:: 3; 1; 4; 7; 5; 9; 2; 6] = true.
Proof. by []. Qed.

(** [rank_shift_interior_order_ex] : numerical witness that [rank_shift_seq]
    preserves interior order on [[4;7;5]]. *)
Example rank_shift_interior_order_ex :
  let L := [:: 4; 7; 5] in
  (nth 0 L 1 > nth 0 L 2) =
  (nth 0 (rank_shift_seq L) 1 > nth 0 (rank_shift_seq L) 2).
Proof. by []. Qed.

(* ===== Tree validity ===== *)
(* A tree is valid_mm if at each node, the root sits at the mm_pos           *)
(* position of the in-order traversal.                                       *)

(** [valid_mm t] : the tree [t] is a valid min-max tree, i.e. at every
    [Node l x r] the root sits at [mm_pos] of the in-order traversal.
    Specifies the trees in the image of [mmtree_of_seq_mm]. *)
Fixpoint valid_mm (t : mmtree nat) : Prop :=
  match t with
  | Leaf => True
  | Node l x r =>
      mm_pos (mmtree_to_seq l ++ x :: mmtree_to_seq r) =
        size (mmtree_to_seq l) /\
      valid_mm l /\ valid_mm r
  end.

(** [valid_mm_build] : every output of [mmtree_of_seq_mm] satisfies
    [valid_mm], the structural invariant used by [tree_structure]. *)
Lemma valid_mm_build : forall s, valid_mm (mmtree_of_seq_mm s).
Proof.
rewrite /mmtree_of_seq_mm.
suff H : forall fuel s, size s <= fuel ->
  valid_mm (mmtree_of_seq_mm_fuel fuel s).
  by move=> s; apply: H.
elim=> [|fuel IH] s Hsz /=.
  by case: s Hsz.
case: s Hsz => [//|a s0 Hsz].
set s := a :: s0; set j := mm_pos s.
have Hj : j < size s by apply: mm_pos_lt.
set tl := mmtree_of_seq_mm_fuel fuel (take j s).
set tr := mmtree_of_seq_mm_fuel fuel (drop j.+1 s).
have Htl_sz : size (take j s) <= fuel.
  rewrite size_take Hj.
  by rewrite -ltnS; apply: (leq_trans Hj).
have Htr_sz : size (drop j.+1 s) <= fuel.
  rewrite size_drop.
  have : size s <= fuel.+1 by exact: Hsz.
  move: Hj; case: (size s) => // k Hk Hk1.
  rewrite subSS.
  have H1 : k - j <= k by exact: leq_subr.
  apply: leq_trans H1 _.
  by rewrite -ltnS.
have Htl_eq : mmtree_to_seq tl = take j s
  by apply: mmtree_of_seq_mm_fuel_correct.
have Htr_eq : mmtree_to_seq tr = drop j.+1 s
  by apply: mmtree_of_seq_mm_fuel_correct.
split; [|split].
- rewrite Htl_eq Htr_eq.
  have -> : take j s ++ nth 0 s j :: drop j.+1 s = s.
    by rewrite -[RHS](cat_take_drop j s) (drop_nth 0 Hj).
  by rewrite size_take Hj.
- exact: IH _ Htl_sz.
- exact: IH _ Htr_sz.
Qed.
#[global] Opaque valid_mm_build.

(* ===== Bridge lemmas ===== *)
(* Each proved once via cons lemmas, then made Opaque. These are the only    *)
(* places where fuel_monotone appears; the structural induction proof        *)
(* never touches fuel.                                                       *)

Section Bridges.

Variables (sl sr : seq nat) (x : nat).
Let s := sl ++ x :: sr.

Hypothesis Hmm : mm_pos s = size sl.

(* -- take/drop simplification under mm_pos -- *)

(** [take_mm_eq] : at the [mm_pos] split, [take (size sl) s] recovers the
    left-subtree in-order [sl]. *)
Lemma take_mm_eq : take (size sl) s = sl.
Proof. by rewrite /s take_cat ltnn subnn take0 cats0. Qed.

(** [drop_mm_eq] : dual of [take_mm_eq] -- [drop (size sl).+1 s] is the
    right-subtree in-order [sr]. *)
Lemma drop_mm_eq : drop (size sl).+1 s = sr.
Proof.
rewrite /s drop_cat ltnNge leqnSn /=.
by rewrite subSn // subnn /= drop0.
Qed.

(* -- window_size bridge -- *)

(** [ws_bridge_left] : on a valid node [s = sl ++ x :: sr], when [i] is
    in the left subtree, [window_size i s] reduces to [window_size i sl].
    Bridge between flat and structural recursion. *)
Lemma ws_bridge_left i :
  i < size sl ->
  window_size i s = window_size i sl.
Proof.
move=> Hi.
have Hs_ne : s <> [::] by rewrite /s; case: (sl).
case Hs : s Hs_ne Hmm => [//|a s0] _ Hmm'.
rewrite (window_size_cons i a s0).
have -> : mm_pos (a :: s0) = size sl by rewrite -Hs.
by rewrite Hi -Hs take_mm_eq.
Qed.

(** [ws_bridge_root] : at the root of the subtree, the M-window has size
    [size s - size sl] (root + right subtree). *)
Lemma ws_bridge_root :
  window_size (size sl) s = size s - size sl.
Proof.
have Hs_ne : s <> [::] by rewrite /s; case: (sl).
case Hs : s Hs_ne Hmm => [//|a s0] _ Hmm'.
rewrite (window_size_cons (size sl) a s0).
have -> : mm_pos (a :: s0) = size sl by rewrite -Hs.
by rewrite ltnn eqxx.
Qed.

(** [ws_bridge_right] : when [i] is in the right subtree, [window_size i s]
    reduces to [window_size (i - size sl - 1) sr] -- the right-subtree
    descent step. *)
Lemma ws_bridge_right i :
  size sl < i ->
  window_size i s = window_size (i - size sl - 1) sr.
Proof.
move=> Hi.
have Hs_ne : s <> [::] by rewrite /s; case: (sl).
case Hs : s Hs_ne Hmm => [//|a s0] _ Hmm'.
rewrite (window_size_cons i a s0).
have -> : mm_pos (a :: s0) = size sl by rewrite -Hs.
rewrite ltnNge (ltnW Hi) /= eq_sym (ltn_eqF Hi).
congr (window_size _ _).
have -> : drop (size sl) s0 = drop (size sl).+1 s by rewrite Hs.
exact: drop_mm_eq.
Qed.

(* -- window_at bridge -- *)

(** [wa_bridge_left] : the [window_at] analogue of [ws_bridge_left]. *)
Lemma wa_bridge_left i :
  i < size sl ->
  window_at i s = window_at i sl.
Proof.
move=> Hi.
have Hs_ne : s <> [::] by rewrite /s; case: (sl).
case Hs : s Hs_ne Hmm => [//|a s0] _ Hmm'.
rewrite (window_at_cons i a s0).
have -> : mm_pos (a :: s0) = size sl by rewrite -Hs.
by rewrite Hi -Hs take_mm_eq.
Qed.

(** [wa_bridge_root] : at the root, [window_at] is the suffix
    [drop (size sl) s] (root + right-subtree labels). *)
Lemma wa_bridge_root :
  window_at (size sl) s = drop (size sl) s.
Proof.
have Hs_ne : s <> [::] by rewrite /s; case: (sl).
case Hs : s Hs_ne Hmm => [//|a s0] _ Hmm'.
rewrite (window_at_cons (size sl) a s0).
have -> : mm_pos (a :: s0) = size sl by rewrite -Hs.
by rewrite ltnn eqxx.
Qed.

(** [wa_bridge_right] : the [window_at] analogue of [ws_bridge_right]. *)
Lemma wa_bridge_right i :
  size sl < i ->
  window_at i s = window_at (i - size sl - 1) sr.
Proof.
move=> Hi.
have Hs_ne : s <> [::] by rewrite /s; case: (sl).
case Hs : s Hs_ne Hmm => [//|a s0] _ Hmm'.
rewrite (window_at_cons i a s0).
have -> : mm_pos (a :: s0) = size sl by rewrite -Hs.
rewrite ltnNge (ltnW Hi) /= eq_sym (ltn_eqF Hi).
congr (window_at _ _).
have -> : drop (size sl) s0 = drop (size sl).+1 s by rewrite Hs.
exact: drop_mm_eq.
Qed.

(* -- has_left_child bridge -- *)

(** [hlc_bridge_left] : [has_left_child] structural bridge analogous to
    [ws_bridge_left]. *)
Lemma hlc_bridge_left i :
  i < size sl ->
  has_left_child i s = has_left_child i sl.
Proof.
move=> Hi.
have Hs_ne : s <> [::] by rewrite /s; case: (sl).
case Hs : s Hs_ne Hmm => [//|a s0] _ Hmm'.
rewrite (has_left_child_cons i a s0).
have -> : mm_pos (a :: s0) = size sl by rewrite -Hs.
by rewrite Hi -Hs take_mm_eq.
Qed.

(** [hlc_bridge_root] : at the root, [has_left_child] is true iff there
    is a nonempty left subtree. *)
Lemma hlc_bridge_root :
  has_left_child (size sl) s = (0 < size sl).
Proof.
have Hs_ne : s <> [::] by rewrite /s; case: (sl).
case Hs : s Hs_ne Hmm => [//|a s0] _ Hmm'.
rewrite (has_left_child_cons (size sl) a s0).
have -> : mm_pos (a :: s0) = size sl by rewrite -Hs.
by rewrite ltnn eqxx.
Qed.

(** [hlc_bridge_right] : [has_left_child] structural bridge analogous to
    [ws_bridge_right]. *)
Lemma hlc_bridge_right i :
  size sl < i ->
  has_left_child i s = has_left_child (i - size sl - 1) sr.
Proof.
move=> Hi.
have Hs_ne : s <> [::] by rewrite /s; case: (sl).
case Hs : s Hs_ne Hmm => [//|a s0] _ Hmm'.
rewrite (has_left_child_cons i a s0).
have -> : mm_pos (a :: s0) = size sl by rewrite -Hs.
rewrite ltnNge (ltnW Hi) /= eq_sym (ltn_eqF Hi).
congr (has_left_child _ _).
have -> : drop (size sl) s0 = drop (size sl).+1 s by rewrite Hs.
exact: drop_mm_eq.
Qed.

End Bridges.

(* Make all bridges opaque to prevent proof-term inlining *)
#[global] Opaque ws_bridge_left ws_bridge_root ws_bridge_right.
#[global] Opaque wa_bridge_left wa_bridge_root wa_bridge_right.
#[global] Opaque hlc_bridge_left hlc_bridge_root hlc_bridge_right.
#[global] Opaque take_mm_eq drop_mm_eq.

(* ===== Base-case lemmas for i = root ===== *)

(* These are the non-trivial base cases when i equals the root position.     *)
(* They are proved separately and made Opaque to keep the structural         *)
(* induction proof's term small.                                             *)

Local Lemma pre_win_lt_max_eq
  i a s0
  (Hlc : 0 < mm_pos (a :: s0))
  (Heq_ij : i = mm_pos (a :: s0)) :
  nth 0 (a :: s0) i.-1 <
    nth 0 (sort leq (window_at i (a :: s0)))
          (window_size i (a :: s0)).-1.
Proof.
subst i.
set s := a :: s0; set j := mm_pos s.
have Hj : j < size s by apply: mm_pos_lt.
have Hs_ne : s <> [::] by discriminate.
have Hdrop_ne : drop j s <> [::].
  move=> Habs;
    have : size (drop j s) = 0 by rewrite Habs.
  by rewrite size_drop => /eqP;
     rewrite subn_eq0 leqNgt Hj.
have [Hno_min Hno_max] := notin_take_mm Hs_ne.
have Hmax_d := max_val_drop Hs_ne Hno_max Hj.
have Hmax_sort := max_eq_nth_sort_last Hdrop_ne.
have Hpred_lt : j.-1 < j by rewrite prednK.
have Hpred_in : nth 0 s j.-1 \in take j s.
  rewrite -(nth_take 0 Hpred_lt).
  by apply: mem_nth; rewrite size_take Hj.
have Hpred_le :
  nth 0 s j.-1 <= foldr maxn (head 0 s) (behead s).
  by apply: foldr_maxn_ge; apply: mem_nth;
     exact: ltn_trans Hpred_lt Hj.
have Hpred_ne :
  nth 0 s j.-1 != foldr maxn (head 0 s) (behead s).
  apply/negP => /eqP Heq.
  have : foldr maxn (head 0 s) (behead s)
    \in take j s by rewrite -Heq.
  by rewrite (negbTE Hno_max).
rewrite (window_at_cons j a s0)
  (window_size_cons j a s0) -/j ltnn eqxx.
rewrite -(size_drop j s) -Hmax_sort Hmax_d.
by rewrite ltn_neqAle Hpred_ne Hpred_le.
Qed.

Local Lemma pre_win_gt_min_eq
  i a s0
  (Hlc : 0 < mm_pos (a :: s0))
  (Heq_ij : i = mm_pos (a :: s0)) :
  nth 0 (a :: s0) i.-1 >
    nth 0 (sort leq (window_at i (a :: s0))) 0.
Proof.
subst i.
set s := a :: s0; set j := mm_pos s.
have Hj : j < size s by apply: mm_pos_lt.
have Hs_ne : s <> [::] by discriminate.
have Hdrop_ne : drop j s <> [::].
  move=> Habs;
    have : size (drop j s) = 0 by rewrite Habs.
  by rewrite size_drop => /eqP;
     rewrite subn_eq0 leqNgt Hj.
have [Hno_min Hno_max] := notin_take_mm Hs_ne.
have Hmin_d := min_val_drop Hs_ne Hno_min Hj.
have Hmin_sort := min_eq_nth_sort_0 Hdrop_ne.
have Hpred_lt : j.-1 < j by rewrite prednK.
have Hpred_in : nth 0 s j.-1 \in take j s.
  rewrite -(nth_take 0 Hpred_lt).
  by apply: mem_nth; rewrite size_take Hj.
have Hpred_ge :
  foldr minn (head 0 s) (behead s)
    <= nth 0 s j.-1.
  by apply: foldr_minn_le; apply: mem_nth;
     exact: ltn_trans Hpred_lt Hj.
have Hpred_ne :
  nth 0 s j.-1 != foldr minn (head 0 s) (behead s).
  apply/negP => /eqP Heq.
  have : foldr minn (head 0 s) (behead s)
    \in take j s by rewrite -Heq.
  by rewrite (negbTE Hno_min).
rewrite (window_at_cons j a s0) -/j ltnn eqxx.
rewrite -Hmin_sort Hmin_d.
by rewrite ltn_neqAle eq_sym Hpred_ne Hpred_ge.
Qed.

Local Lemma xone_desc_eq
  i a s0
  (Huniq : uniq (a :: s0))
  (Hlc : 0 < mm_pos (a :: s0))
  (Hws : 1 < size (a :: s0) - mm_pos (a :: s0))
  (Heq_ij : i = mm_pos (a :: s0)) :
  is_descent_seq (a :: s0) i.-1 (+)
  is_descent_seq (a :: s0) i.
Proof.
subst i.
set s := a :: s0; set j := mm_pos s.
have Hj : j < size s by apply: mm_pos_lt.
have Hs_ne : s <> [::] by discriminate.
have Hdrop_ne : drop j s <> [::].
  move=> Habs;
    have : size (drop j s) = 0 by rewrite Habs.
  by rewrite size_drop => /eqP;
     rewrite subn_eq0 leqNgt Hj.
have [Hno_min Hno_max] := notin_take_mm Hs_ne.
have Hnth := nth_w_mm_pos Hs_ne.
have Hpred_lt : j.-1 < j by rewrite prednK.
have Hpred_in : nth 0 s j.-1 \in take j s.
  rewrite -(nth_take 0 Hpred_lt).
  by apply: mem_nth; rewrite size_take Hj.
have Hj1_lt : j.+1 < size s.
  have : j + 2 <= size s
    by rewrite -(leq_subRL 2 (ltnW Hj)).
  by rewrite addn2.
have Hj1_in : nth 0 s j.+1 \in s
  by apply: mem_nth.
rewrite /is_descent_seq (prednK Hlc).
case: Hnth => Hval.
- have Hd_pred : nth 0 s j.-1 > nth 0 s j.
    rewrite Hval ltn_neqAle; apply/andP; split.
    + apply/negP => /eqP Heq.
      have Hin :
        foldr minn (head 0 s) (behead s)
          \in take j s by rewrite Heq.
      by rewrite Hin in Hno_min.
    + apply: foldr_minn_le. apply: mem_nth.
      exact: ltn_trans Hpred_lt Hj.
  have Hnd_j : ~~ (nth 0 s j > nth 0 s j.+1).
    rewrite -leqNgt Hval.
    apply: foldr_minn_le. exact: Hj1_in.
  by rewrite Hd_pred (negbTE Hnd_j).
- have Hnd_pred :
    ~~ (nth 0 s j.-1 > nth 0 s j).
    rewrite -leqNgt Hval.
    apply: foldr_maxn_ge. apply: mem_nth.
    exact: ltn_trans Hpred_lt Hj.
  have Hd_j : nth 0 s j > nth 0 s j.+1.
    rewrite Hval ltn_neqAle; apply/andP; split.
    + apply/negP => /eqP Heq.
      have Heq2 : nth 0 s j = nth 0 s j.+1
        by rewrite Hval -Heq.
      have : j == j.+1.
        by rewrite -(nth_uniq 0 Hj Hj1_lt Huniq)
           Heq2 eqxx.
      by rewrite eqn_leq ltnn andbF.
    + apply: foldr_maxn_ge. exact: Hj1_in.
  by rewrite (negbTE Hnd_pred) Hd_j.
Qed.

(* ===== tree_props definition (unchanged) ===== *)

(** [tree_props i w] is the conjunction of five structural properties at
    in-order position [i]: post-window extremum, two pre-window-vs-window
    inequalities, the descent flip, and the no-left-child extremum.
    Bundled to share a single structural induction. *)
Definition tree_props (i : nat) (w : seq nat) :=
  (i + window_size i w < size w ->
    (nth 0 w (i + window_size i w)
       < nth 0 (sort leq (window_at i w)) 0) \/
    (nth 0 w (i + window_size i w)
       > nth 0 (sort leq (window_at i w))
               (window_size i w).-1))
  /\
  (0 < i -> has_left_child i w ->
    1 < window_size i w ->
    head 0 (window_at i w) ==
      nth 0 (sort leq (window_at i w)) 0 ->
    nth 0 w i.-1 <
      nth 0 (sort leq (window_at i w))
            (window_size i w).-1)
  /\
  (0 < i -> has_left_child i w ->
    1 < window_size i w ->
    head 0 (window_at i w) ==
      nth 0 (sort leq (window_at i w))
            (window_size i w).-1 ->
    nth 0 w i.-1 >
      nth 0 (sort leq (window_at i w)) 0)
  /\
  (0 < i -> has_left_child i w ->
    1 < window_size i w ->
    is_descent_seq w i.-1 (+) is_descent_seq w i)
  /\
  (0 < i -> ~~ has_left_child i w ->
    1 < window_size i w ->
    (nth 0 w i.-1
       < nth 0 (sort leq (window_at i w)) 0) \/
    (nth 0 w i.-1
       > nth 0 (sort leq (window_at i w))
               (window_size i w).-1)).

(** [pred_sub_add] : an arithmetic identity used to align in-order
    indices when descending into the right subtree. *)
Lemma pred_sub_add i j :
  j < i -> 0 < i - j - 1 ->
  (i - j - 1).-1 + j.+1 = i.-1.
Proof.
move=> Hji Hi'0.
have : i - j - 1 + j.+1 = i
  by rewrite -subnDA addn1 subnK.
case: (i - j - 1) Hi'0 => [//|m'] _ Hm.
by rewrite addSn in Hm; rewrite /= -Hm.
Qed.

(* ===== THE STRUCTURAL INDUCTION PROOF ===== *)
(* This is the heart of Option A. We prove tree_props for any valid          *)
(* mmtree by structural induction. The proof term is O(n) because:          *)
(*   - Each node contributes O(1) work (bridge lemma + IH application)      *)
(*   - No fuel_monotone proofs are generated inline                         *)
(*   - Base cases reference opaque local lemmas                             *)

(** [tree_structure_via_tree] : [tree_props] holds for every position [i]
    of the in-order traversal of any valid min-max tree.  Proved by
    structural induction on [t], dispatching on [i] vs the root index. *)
Lemma tree_structure_via_tree t :
  valid_mm t -> uniq (mmtree_to_seq t) ->
  forall i, tree_props i (mmtree_to_seq t).
Proof.
elim: t => [|l IHl x r IHr] Hv Hu i.
(* --- Leaf: s = [::], all properties vacuous --- *)
  by rewrite /tree_props /=; repeat split.
(* --- Node l x r --- *)
simpl in Hv.
set sl := mmtree_to_seq l in Hv Hu |- *.
set sr := mmtree_to_seq r in Hv Hu |- *.
set s := sl ++ x :: sr in Hv Hu |- *.
have [Hmm [Hvl Hvr]] := Hv.
(* Extract uniq for subtrees *)
have Huniq_l : uniq sl.
  by have : uniq (sl ++ x :: sr);
     [exact: Hu | rewrite cat_uniq => /andP[]].
have Huniq_r : uniq sr.
  have : uniq (sl ++ x :: sr) by exact: Hu.
  rewrite cat_uniq => /andP [_ /andP [_ /=]].
  by rewrite andbC => /andP [? _].
(* IH for subtrees *)
have IHl' := IHl Hvl Huniq_l.
have IHr' := IHr Hvr Huniq_r.
(* Size facts *)
have Hsz_s : size s = size sl + 1 + size sr.
  by rewrite /s size_cat /= addnS addn1 addSn.
have Hs_ne : s <> [::].
  by rewrite /s; case: (sl) => [|??]; discriminate.
(* 3-way case split on i vs size sl *)
case: (ltngtP i (size sl)) => [Hij | Hji | Heq_ij].
(* ==== Case i < size sl: recurse on left subtree ==== *)
- have [P1l [P2l [P3l [P4l P5l]]]] := IHl' i.
  have Hij' : i < mm_pos s by rewrite Hmm.
  split; [|split; [|split; [|split]]].
  + (* P1: post-window extremum *)
    move=> Hpost.
    rewrite (wa_bridge_left Hmm Hij)
            (ws_bridge_left Hmm Hij) in Hpost *.
    have Hfit := window_fits_left Hs_ne Hij'.
    rewrite Hmm (ws_bridge_left Hmm Hij) in Hfit.
    set ws_l := window_size i sl.
    case Hbnd : (i + ws_l < size sl).
    * (* Window fits entirely inside left subtree *)
      have Hpost_l : i + ws_l < size sl := Hbnd.
      have := P1l Hpost_l.
      by rewrite nth_cat Hbnd.
    * (* Window reaches boundary: i + ws_l = size sl *)
      have Hfit2 : i + ws_l = size sl.
        move/negbT: Hbnd; rewrite -leqNgt => Hge.
        by apply/eqP; rewrite eqn_leq Hge Hfit.
      rewrite Hfit2.
      have Hnth_j := nth_w_mm_pos Hs_ne.
      set wa := window_at i sl.
      have Hws_gt0 : 0 < ws_l.
        by apply: window_size_gt0; exact: Hij.
      have Hwa_ne : wa <> [::].
        move=> Hab.
        have Hsz0 : size wa = 0 by rewrite Hab.
        have Hsz_wa : size wa = ws_l.
          rewrite /wa /window_at size_takel //.
          by rewrite size_drop; exact: window_size_bound.
        by move: Hws_gt0; rewrite -Hsz_wa Hsz0.
      have Hsz_wa : size wa = ws_l.
        rewrite /wa /window_at size_takel //.
        by rewrite size_drop; exact: window_size_bound.
      have Hwa_sub : {subset wa <= sl}.
        move=> y; rewrite /wa /window_at => Hy.
        have := mem_take Hy; exact: mem_drop.
      have [Hno_min Hno_max] := notin_take_mm Hs_ne.
      rewrite Hmm in Hno_min Hno_max.
      have Htake_sl : take (size sl) s = sl.
        by rewrite /s take_cat ltnn subnn take0 cats0.
      have Hwa_sub_take : {subset wa <= take (size sl) s}.
        by move=> y Hy; rewrite Htake_sl; exact: Hwa_sub.
      have Hmin_sort := min_eq_nth_sort_0 Hwa_ne.
      have Hmax_sort := max_eq_nth_sort_last Hwa_ne.
      set minwa := foldr minn (head 0 wa) (behead wa).
      set maxwa := foldr maxn (head 0 wa) (behead wa).
      have Hminwa_in : minwa \in wa.
        by rewrite /minwa; case: (wa) Hwa_ne =>
          [//|b t] _ /=; exact: min_in.
      have Hmaxwa_in : maxwa \in wa.
        by rewrite /maxwa; case: (wa) Hwa_ne =>
          [//|b t] _ /=; exact: max_in.
      have Hminwa_in_s : minwa \in s.
        exact: mem_take (Hwa_sub_take _ Hminwa_in).
      have Hmaxwa_in_s : maxwa \in s.
        exact: mem_take (Hwa_sub_take _ Hmaxwa_in).
      case: Hnth_j; rewrite -/s Hmm => Hval.
      -- left; rewrite Hval -Hmin_sort.
         have Hminwa_le :
           foldr minn (head 0 s) (behead s) <= minwa.
           apply: foldr_minn_le.
           by case: (s) Hs_ne Hminwa_in_s.
         have Hminwa_ne :
           foldr minn (head 0 s) (behead s) != minwa.
           apply/negP => /eqP Heq_v.
           have : foldr minn (head 0 s) (behead s)
             \in take (size sl) s
             by rewrite Heq_v; exact: Hwa_sub_take.
           by rewrite (negbTE Hno_min).
         by rewrite ltn_neqAle Hminwa_ne Hminwa_le.
      -- right.
         have Hmaxwa_le :
           maxwa <= foldr maxn (head 0 s) (behead s).
           apply: foldr_maxn_ge.
           by case: (s) Hs_ne Hmaxwa_in_s.
         have Hmaxwa_ne :
           maxwa != foldr maxn (head 0 s) (behead s).
           apply/negP => /eqP Heq_v.
           have : foldr maxn (head 0 s) (behead s)
             \in take (size sl) s
             by rewrite -Heq_v; exact: Hwa_sub_take.
           by rewrite (negbTE Hno_max).
         have Hmaxwa_eq :
           nth 0 (sort leq wa) (ws_l.-1) = maxwa.
           have -> : ws_l.-1 = (size wa).-1
             by rewrite Hsz_wa.
           by rewrite -Hmax_sort.
         rewrite Hval Hmaxwa_eq.
         by rewrite ltn_neqAle Hmaxwa_ne Hmaxwa_le.
  + (* P2: pre-window lt max when min head *)
    move=> Hi0 Hlc Hws Hhead.
    rewrite (hlc_bridge_left Hmm Hij) in Hlc.
    rewrite (wa_bridge_left Hmm Hij) in Hws Hhead *.
    rewrite (ws_bridge_left Hmm Hij) in Hws Hhead *.
    have := P2l Hi0 Hlc Hws Hhead.
    by rewrite nth_cat
       (leq_ltn_trans (leq_pred _) Hij).
  + (* P3: pre-window gt min when max head *)
    move=> Hi0 Hlc Hws Hhead.
    rewrite (hlc_bridge_left Hmm Hij) in Hlc.
    rewrite (wa_bridge_left Hmm Hij) in Hws Hhead *.
    rewrite (ws_bridge_left Hmm Hij) in Hws Hhead *.
    have := P3l Hi0 Hlc Hws Hhead.
    by rewrite nth_cat
       (leq_ltn_trans (leq_pred _) Hij).
  + (* P4: exactly one descent LR *)
    move=> Hi0 Hlc Hws.
    rewrite (hlc_bridge_left Hmm Hij) in Hlc.
    rewrite (ws_bridge_left Hmm Hij) in Hws.
    have Hfit := window_fits_left Hs_ne Hij'.
    rewrite Hmm (ws_bridge_left Hmm Hij) in Hfit.
    have Hi1_lt : i.+1 < size sl.
      suff : i + 2 <= size sl by rewrite addn2.
      by apply: leq_trans _ Hfit; rewrite leq_add2l.
    have Hpred_lt : i.-1 < size sl :=
      leq_ltn_trans (leq_pred _) Hij.
    have := P4l Hi0 Hlc Hws.
    rewrite /is_descent_seq (prednK Hi0).
    by rewrite !(nth_cat) Hpred_lt Hij Hi1_lt.
  + (* P5: pre-window extremum R *)
    move=> Hi0 Hnlc Hws.
    rewrite (hlc_bridge_left Hmm Hij) in Hnlc.
    rewrite (wa_bridge_left Hmm Hij) in Hws *.
    rewrite (ws_bridge_left Hmm Hij) in Hws *.
    have := P5l Hi0 Hnlc Hws.
    by rewrite nth_cat
       (leq_ltn_trans (leq_pred _) Hij).
(* ==== Case size sl < i: recurse on right subtree ==== *)
- set i' := i - size sl - 1.
  have Hi'_eq : i' + (size sl).+1 = i.
    by rewrite /i' -subnDA addn1 subnK.
  have Hdrop_eq : drop (size sl).+1 s = sr.
    rewrite /s drop_cat ltnNge leqnSn /=.
    by rewrite subSn // subnn /= drop0.
  have Hsz_rs :
    size sr + (size sl).+1 = size s.
    by rewrite addnC addSn /s size_cat
       /= addnS.
  have [P1r [P2r [P3r [P4r P5r]]]] := IHr' i'.
  split; [|split; [|split; [|split]]].
  + (* P1: post-window extremum *)
    move=> Hpost.
    rewrite (wa_bridge_right Hmm Hji)
            (ws_bridge_right Hmm Hji)
      in Hpost *.
    have Hpost_r :
      i' + window_size i' sr < size sr.
      rewrite -(ltn_add2r (size sl).+1)
        addnAC Hi'_eq Hsz_rs.
      exact: Hpost.
    have := P1r Hpost_r.
    set ws' := window_size i' sr.
    have Hnth_eq :
      nth 0 s (i + ws') =
        nth 0 sr (i' + ws').
      rewrite -Hdrop_eq nth_drop.
      congr (nth 0 s _).
      by rewrite addnA
         [(size sl).+1 + i']addnC
         Hi'_eq.
    by rewrite Hnth_eq.
  + (* P2: pre-window lt max when min head *)
    move=> Hi0 Hlc Hws Hhead.
    rewrite (hlc_bridge_right Hmm Hji)
      in Hlc.
    rewrite (wa_bridge_right Hmm Hji)
            (ws_bridge_right Hmm Hji)
      in Hws Hhead *.
    rewrite -/i' in Hlc.
    have Hi0' : 0 < i'.
      case Hi'0 : i' Hlc => [|//] /=.
      by rewrite has_left_child_0.
    have Hpred_eq :
      i'.-1 + (size sl).+1 = i.-1.
      have Hsucc : i'.-1.+1 = i'
        by rewrite prednK.
      have : i'.-1.+1 + (size sl).+1 = i
        by rewrite Hsucc Hi'_eq.
      by move=> <-; rewrite addSn.
    have Hnth_p2 :
      nth 0 s i.-1 = nth 0 sr i'.-1.
      by rewrite -Hdrop_eq nth_drop
         addnC Hpred_eq.
    have := P2r Hi0' Hlc Hws Hhead.
    by rewrite Hnth_p2.
  + (* P3: pre-window gt min when max head *)
    move=> Hi0 Hlc Hws Hhead.
    rewrite (hlc_bridge_right Hmm Hji)
      in Hlc.
    rewrite (wa_bridge_right Hmm Hji)
            (ws_bridge_right Hmm Hji)
      in Hws Hhead *.
    rewrite -/i' in Hlc.
    have Hi0' : 0 < i'.
      case Hi'0 : i' Hlc => [|//] /=.
      by rewrite has_left_child_0.
    have Hpred_eq :
      i'.-1 + (size sl).+1 = i.-1.
      have Hsucc : i'.-1.+1 = i'
        by rewrite prednK.
      have : i'.-1.+1 + (size sl).+1 = i
        by rewrite Hsucc Hi'_eq.
      by move=> <-; rewrite addSn.
    have Hnth_p3 :
      nth 0 s i.-1 = nth 0 sr i'.-1.
      by rewrite -Hdrop_eq nth_drop
         addnC Hpred_eq.
    have := P3r Hi0' Hlc Hws Hhead.
    by rewrite Hnth_p3.
  + (* P4: exactly one descent *)
    move=> Hi0 Hlc Hws.
    rewrite (hlc_bridge_right Hmm Hji)
      in Hlc.
    rewrite (ws_bridge_right Hmm Hji)
      in Hws.
    rewrite -/i' in Hlc.
    have Hi0' : 0 < i'.
      case Hi'0 : i' Hlc => [|//] /=.
      by rewrite has_left_child_0.
    have Hpred_eq :
      i'.-1 + (size sl).+1 = i.-1.
      have Hsucc : i'.-1.+1 = i'
        by rewrite prednK.
      have : i'.-1.+1 + (size sl).+1 = i
        by rewrite Hsucc Hi'_eq.
      by move=> <-; rewrite addSn.
    have Hi1_eq :
      i'.+1 + (size sl).+1 = i.+1
      by rewrite addSn Hi'_eq.
    have Hnth_pred :
      nth 0 s i.-1 = nth 0 sr i'.-1.
      by rewrite -Hdrop_eq nth_drop
         addnC Hpred_eq.
    have Hnth_i :
      nth 0 s i = nth 0 sr i'.
      by rewrite -Hdrop_eq nth_drop
         [(size sl).+1 + i']addnC Hi'_eq.
    have Hnth_i1 :
      nth 0 s i.+1 = nth 0 sr i'.+1.
      by rewrite -Hdrop_eq nth_drop
         [(size sl).+1 + i'.+1]addnC Hi1_eq.
    have := P4r Hi0' Hlc Hws.
    rewrite /is_descent_seq (prednK Hi0')
      (prednK Hi0).
    by rewrite -Hnth_pred -Hnth_i -Hnth_i1.
  + (* P5: pre-window extremum, no left child *)
    move=> Hi0 Hnlc Hws.
    rewrite (hlc_bridge_right Hmm Hji)
      in Hnlc.
    rewrite (wa_bridge_right Hmm Hji)
            (ws_bridge_right Hmm Hji)
      in Hws *.
    case H0 : (0 < i').
    * (* i' > 0: direct translation *)
      have Hpe :
        (size sl).+1 + i'.-1 = i.-1.
        rewrite addnC.
        exact: pred_sub_add Hji H0.
      have Hnth_pe :
        nth 0 s i.-1 = nth 0 sr i'.-1.
        rewrite -[i.-1]Hpe.
        by rewrite -Hdrop_eq nth_drop.
      case: (P5r H0 Hnlc Hws) =>
        [Hl | Hr].
      -- by left; rewrite Hnth_pe.
      -- by right; rewrite Hnth_pe.
    * (* i' = 0: boundary case,
         i = (size sl).+1 *)
      move/negbT: H0;
        rewrite -eqn0Ngt => /eqP Hi'0.
      have Hieq : i = (size sl).+1.
        by rewrite -Hi'_eq Hi'0 add0n.
      rewrite /i' Hieq subSn // subnn
        in Hws *.
      set wa := window_at 0 sr.
      have Hws0 :
        1 < window_size 0 sr := Hws.
      have Hwa_ne : wa <> [::].
        move=> Hab.
        have Hswa :
          size wa = window_size 0 sr.
          rewrite /wa /window_at drop0.
          apply: size_takel.
          by have :=
            window_size_bound 0 sr;
             rewrite subn0.
        by move: Hws0;
          rewrite -Hswa Hab.
      have Hsub : {subset wa <= s}.
        move=> y Hy.
        have Hyr : y \in sr.
          by move: Hy;
             rewrite /wa /window_at drop0;
             exact: mem_take.
        rewrite /s mem_cat; apply/orP;
          right.
        by rewrite in_cons Hyr orbT.
      have Hjni :
        nth 0 s (size sl) \notin wa.
        apply/negP => Hab.
        have Hd :
          nth 0 s (size sl) \in sr.
          by move: Hab;
             rewrite /wa /window_at
               drop0;
             exact: mem_take.
        have Ht :
          nth 0 s (size sl) \in
            take (size sl).+1 s.
          rewrite -(nth_take 0
            (ltnSn (size sl))).
          apply: mem_nth.
          rewrite size_takel;
            last by rewrite /s size_cat /=
               addnS ltnS leq_addr.
          exact: ltnSn.
        have Huniq_s : uniq s := Hu.
        move: Huniq_s;
          rewrite -(cat_take_drop
            (size sl).+1 s)
          cat_uniq =>
          /andP [_ /andP [Hno _]].
        move/hasPn: Hno.
        rewrite Hdrop_eq => /(_ _ Hd).
        by rewrite Ht.
      have := nth_w_mm_pos Hs_ne.
      rewrite Hmm =>
        [] [Hval | Hval].
      -- left.
         rewrite -(min_eq_nth_sort_0
           Hwa_ne).
         set m := foldr minn
           (head 0 wa) (behead wa).
         have Hm_in : m \in wa.
           rewrite /m;
             case: (wa) Hwa_ne =>
               [//|b t] _ /=;
             exact: min_in.
         have Hle :
           foldr minn (head 0 s)
             (behead s) <= m.
           apply: foldr_minn_le.
           have Hm_s := Hsub _ Hm_in.
           by case: (s) Hs_ne Hm_s.
         have Hne2 :
           foldr minn (head 0 s)
             (behead s) != m.
           apply/negP => /eqP Heq.
           have :
             nth 0 s (size sl) = m
             by rewrite Hval Heq.
           move=> HH;
             rewrite HH in Hjni.
           by rewrite (negbTE Hjni)
              in Hm_in.
         by rewrite Hval
            ltn_neqAle Hne2 Hle.
      -- right.
         have Hswa :
           size wa = window_size 0 sr.
           rewrite /wa /window_at drop0.
           apply: size_takel.
           by have :=
             window_size_bound 0 sr;
              rewrite subn0.
         rewrite -Hswa
           -(max_eq_nth_sort_last
               Hwa_ne).
         set M := foldr maxn
           (head 0 wa) (behead wa).
         have HM_in : M \in wa.
           rewrite /M;
             case: (wa) Hwa_ne =>
               [//|b t] _ /=;
             exact: max_in.
         have Hle :
           M <= foldr maxn (head 0 s)
                  (behead s).
           apply: foldr_maxn_ge.
           by case: (s) Hs_ne
              (Hsub _ HM_in).
         have Hne2 :
           M != foldr maxn (head 0 s)
                  (behead s).
           apply/negP => /eqP Heq.
           have :
             nth 0 s (size sl) = M
             by rewrite Hval -Heq.
           move=> HH;
             rewrite HH in Hjni.
           by rewrite (negbTE Hjni)
              in HM_in.
         by rewrite Hval
            ltn_neqAle Hne2 Hle.
(* ==== Case i = size sl: base cases ==== *)
- subst i.
  have Hsl_le : size sl <= size s
    by rewrite Hsz_s -addnA leq_addr.
  have Hmm_s : size sl = mm_pos s by rewrite Hmm.
  change (mmtree_to_seq (Node l x r)) with s.
  have Hu_s : uniq s
    by change s with (mmtree_to_seq (Node l x r)).
  split; [|split; [|split; [|split]]].
  + (* P1: vacuous — size sl + ws = size s *)
    move=> Hpost; exfalso.
    move: Hpost; rewrite (ws_bridge_root Hmm).
    by rewrite addnC subnK // ltnn.
  + (* P2: pre_win_lt_max_eq *)
    move=> Hj0 Hlc Hws Hhead.
    rewrite Hmm_s.
    rewrite Hmm_s in Hlc Hws Hhead.
    have Hs_cons : exists a s0, s = a :: s0
      by case: (s) Hs_ne => [//|a s0] _;
         exists a, s0.
    case: Hs_cons => [a [s0 Hs_eq]].
    rewrite Hs_eq in Hlc Hws Hhead Hu_s |- *.
    have Hlc' : 0 < mm_pos (a :: s0)
      by rewrite -Hs_eq -Hmm_s.
    exact: (pre_win_lt_max_eq Hlc' erefl).
  + (* P3: pre_win_gt_min_eq *)
    move=> Hj0 Hlc Hws Hhead.
    rewrite Hmm_s.
    rewrite Hmm_s in Hlc Hws Hhead.
    have Hs_cons : exists a s0, s = a :: s0
      by case: (s) Hs_ne => [//|a s0] _;
         exists a, s0.
    case: Hs_cons => [a [s0 Hs_eq]].
    rewrite Hs_eq in Hlc Hws Hhead Hu_s |- *.
    have Hlc' : 0 < mm_pos (a :: s0)
      by rewrite -Hs_eq -Hmm_s.
    exact: (pre_win_gt_min_eq Hlc' erefl).
  + (* P4: xone_desc_eq *)
    move=> Hj0 Hlc Hws.
    rewrite (hlc_bridge_root Hmm) in Hlc.
    rewrite (ws_bridge_root Hmm) in Hws.
    have Hs_cons : exists a s0, s = a :: s0
      by case: (s) Hs_ne => [//|a s0] _;
         exists a, s0.
    case: Hs_cons => [a [s0 Hs_eq]].
    have Hlc' : 0 < mm_pos (a :: s0)
      by rewrite -Hs_eq -Hmm_s.
    have Hws' : 1 < size (a :: s0) -
      mm_pos (a :: s0)
      by rewrite -Hs_eq -Hmm_s.
    have Hu' : uniq (a :: s0) by rewrite -Hs_eq.
    rewrite Hmm_s Hs_eq.
    exact: (@xone_desc_eq (mm_pos (a :: s0)) a s0
              Hu' Hlc' Hws' erefl).
  + (* P5: vacuous — hlc = (0 < size sl)
       contradicts ~~ hlc when 0 < size sl *)
    move=> Hj0 Hnlc.
    rewrite (hlc_bridge_root Hmm) in Hnlc.
    by move/negP: Hnlc.
Qed.

(* ===== Derive tree_structure ============= *)

(** [tree_structure] : [tree_props i w] for every uniq [w], obtained by
    re-routing through [mmtree_of_seq_mm] and [tree_structure_via_tree]. *)
Lemma tree_structure i w : uniq w -> tree_props i w.
Proof.
move=> Hu.
rewrite -(mmtree_of_seq_mmK w).
apply: tree_structure_via_tree.
- exact: valid_mm_build.
- by rewrite mmtree_of_seq_mmK.
Qed.
(* -- Derive the 5 individual lemmas as projections ----------------------- *)

(** [post_window_extremum] : the entry just past the window is either
    smaller than every window value or larger than every window value
    -- the post-window position is a global extremum.  First projection
    of [tree_props]. *)
Lemma post_window_extremum i w :
  uniq w -> i + window_size i w < size w ->
  (nth 0 w (i + window_size i w)
     < nth 0 (sort leq (window_at i w)) 0) \/
  (nth 0 w (i + window_size i w)
     > nth 0 (sort leq (window_at i w))
             (window_size i w).-1).
Proof.
by move=> Hu Hpost;
   exact: (tree_structure i Hu).1.
Qed.
#[global] Opaque post_window_extremum.

(* Non-triviality: w = [3;1;4;7;5;9;2;6], i=2.
   Window = [4;7;5] at [2,5).
   Post-window element at position 5: w[5] = 9.
   max(window) = 7. 9 > 7 = true. *)
(** [post_window_extremum_ex] : numerical witness of
    [post_window_extremum] at position 2 in [[3;1;4;7;5;9;2;6]]. *)
Example post_window_extremum_ex :
  let w := [:: 3; 1; 4; 7; 5; 9; 2; 6] in
  nth 0 w (2 + window_size 2 w) >
    nth 0 (sort leq (window_at 2 w))
          (window_size 2 w).-1.
Proof. by []. Qed.

(** [pre_window_lt_max_when_min_head] : at an LR vertex whose head is the
    window-min, the pre-window entry [w_{i-1}] is below the window-max.
    Discharges the [head = min] branch of [exactly_one_descent_LR]. *)
Lemma pre_window_lt_max_when_min_head :
  forall (i : nat) (w : seq nat),
  uniq w -> 0 < i -> has_left_child i w ->
  1 < window_size i w ->
  head 0 (window_at i w) ==
    nth 0 (sort leq (window_at i w)) 0 ->
  nth 0 w i.-1 <
    nth 0 (sort leq (window_at i w))
          (window_size i w).-1.
Proof.
by move=> i w Hu Hi0 Hlc Hws Hh;
   exact: (tree_structure i Hu).2.1.
Qed.
#[global] Opaque pre_window_lt_max_when_min_head.

(** [pre_window_gt_min_when_max_head] : dual of
    [pre_window_lt_max_when_min_head] -- at an LR vertex whose head is the
    window-max, [w_{i-1}] is above the window-min. *)
Lemma pre_window_gt_min_when_max_head :
  forall (i : nat) (w : seq nat),
  uniq w -> 0 < i -> has_left_child i w ->
  1 < window_size i w ->
  head 0 (window_at i w) ==
    nth 0 (sort leq (window_at i w))
          (window_size i w).-1 ->
  nth 0 w i.-1 >
    nth 0 (sort leq (window_at i w)) 0.
Proof.
by move=> i w Hu Hi0 Hlc Hws Hh;
   exact: (tree_structure i Hu).2.2.1.
Qed.
#[global] Opaque pre_window_gt_min_when_max_head.

(* Non-triviality: w = [3;1;4;7;5;9;2;6], i=5.
   Window = [9;2;6]. Head = 9 = max.
   min(window) = 2. w[4] = 5 > 2. *)
(** [pre_window_gt_min_ex] : witness for [pre_window_gt_min_when_max_head]
    at position 5 in [[3;1;4;7;5;9;2;6]]. *)
Example pre_window_gt_min_ex :
  let w := [:: 3; 1; 4; 7; 5; 9; 2; 6] in
  nth 0 w 4 >
    nth 0 (sort leq (window_at 5 w)) 0.
Proof. by []. Qed.

(** [exactly_one_descent_LR] : at an LR vertex with nontrivial window,
    exactly one of positions [i-1, i] is a descent of [w].  Used by the
    descent-effect theorems in [psi_descent_thms.v]. *)
Lemma exactly_one_descent_LR :
  forall (i : nat) (w : seq nat),
  uniq w -> 0 < i -> has_left_child i w ->
  1 < window_size i w ->
  is_descent_seq w i.-1 (+) is_descent_seq w i.
Proof.
by move=> i w Hu Hi0 Hlc Hws;
   exact: (tree_structure i Hu).2.2.2.1.
Qed.
#[global] Opaque exactly_one_descent_LR.

(* Non-triviality: w = [3;1;4;7;5;9;2;6], i=5.
   is_descent_seq w 4 = (5 > 9) = false.
   is_descent_seq w 5 = (9 > 2) = true.
   false (+) true = true. *)
(** [exactly_one_descent_LR_ex] : numerical witness of
    [exactly_one_descent_LR] at position 5 in [[3;1;4;7;5;9;2;6]]. *)
Example exactly_one_descent_LR_ex :
  let w := [:: 3; 1; 4; 7; 5; 9; 2; 6] in
  is_descent_seq w 4 (+)
    is_descent_seq w 5.
Proof. by []. Qed.

(** [pre_window_extremum_R] : at an R vertex (no left child), the entry
    [w_{i-1}] is itself a global extremum relative to the window.  R-case
    counterpart of the LR pre-window lemmas. *)
Lemma pre_window_extremum_R i w :
  uniq w -> 0 < i -> ~~ has_left_child i w ->
  1 < window_size i w ->
  (nth 0 w i.-1
     < nth 0 (sort leq (window_at i w)) 0) \/
  (nth 0 w i.-1
     > nth 0 (sort leq (window_at i w))
             (window_size i w).-1).
Proof.
by move=> Hu Hi0 Hnlc Hws;
   exact: (tree_structure i Hu).2.2.2.2.
Qed.
#[global] Opaque pre_window_extremum_R.



