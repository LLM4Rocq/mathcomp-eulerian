(* psi_cdindex_tree.v — Tree-shape structural proofs (part 2) *)
(*                                                                           *)
(* Free-endpoint and LR-predecessor lemmas, proved by structural induction  *)
(* on the min-max tree (mmtree) and lifted to seq via mmtree_of_seq_mm.     *)
(* The tree-inductive approach replaces a fuel-based size induction whose   *)
(* proof term blew past 158 GB in -vo.  Tree induction's term is linear in  *)
(* tree size (currently ~33 GB peak), well under the 128 GB cap.           *)

From mathcomp Require Import all_ssreflect.
Require Import mmtree psi_core psi_comm psi_descent_v2 psi_descent_thms.
Require Import psi_cdindex_defs psi_cdindex_tree_hlc.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* ----- M5.2 Examples ----- *)

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

(* ----- M5.4 window_size at the last index = 1 ----------------------------- *)
(* Used in the LR_pred_is_endpoint proof (root case).                       *)

(** Fuel-bounded variant: [window_size] at the last index of a non-empty
    [w] equals 1.  Used to prove the leaf-status of the last vertex. *)
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
  by move/eqP: Hjq => <-; rewrite /s /= subSn // subnn.
have Hjl : j < size s0
  by rewrite ltn_neqAle eq_sym Hjq /= leqNgt Hjn.
change (window_size_fuel fuel (size s0 - j - 1) (drop j s0) = 1).
have Hsz_ds : size (drop j s0) = size s0 - j by rewrite size_drop.
have H0ds : 0 < size (drop j s0) by rewrite Hsz_ds subn_gt0.
have Hfuel_ok : size (drop j s0) <= fuel.
  rewrite Hsz_ds; apply: leq_trans (leq_subr _ _) _.
  by rewrite ltnS in Hsz.
have -> : size s0 - j - 1 = (size (drop j s0)).-1
  by rewrite Hsz_ds subn1.
exact: IH Hfuel_ok H0ds.
Qed.

(** Last vertex has window size 1, i.e. is always an endpoint. *)
Lemma window_size_last w :
  0 < size w ->
  window_size (size w).-1 w = 1.
Proof.
move=> Hne; rewrite /window_size.
exact: window_size_last_fuel (leqnn _) Hne.
Qed.

(* ----- M5.3 Tree-level versions of window_size, has_left_child, is_internal *)

(** [window_size_t i t] is the tree-level analogue of [window_size]:
    recursion on the [mmtree] [t] using the in-order index [i]. *)
Fixpoint window_size_t (i : nat) (t : mmtree nat) : nat :=
  match t with
  | Leaf => 0
  | Node l _ r =>
      if i < size (mmtree_to_seq l) then window_size_t i l
      else if i == size (mmtree_to_seq l) then (size (mmtree_to_seq r)).+1
      else window_size_t (i - (size (mmtree_to_seq l)).+1) r
  end.

(** [has_left_child_t i t] is the tree-level analogue of [has_left_child]:
    direct structural recursion on the [mmtree]. *)
Fixpoint has_left_child_t (i : nat) (t : mmtree nat) : bool :=
  match t with
  | Leaf => false
  | Node l _ r =>
      if i < size (mmtree_to_seq l) then has_left_child_t i l
      else if i == size (mmtree_to_seq l) then 0 < size (mmtree_to_seq l)
      else has_left_child_t (i - (size (mmtree_to_seq l)).+1) r
  end.

(** Tree-level analogue of [is_internal]. *)
Definition is_internal_t (i : nat) (t : mmtree nat) : bool :=
  (i < size (mmtree_to_seq t)) && (1 < window_size_t i t).

Arguments window_size_t : simpl never.
Arguments has_left_child_t : simpl never.

(* ----- Cons-style equations for the tree-level functions ------------------ *)

(** Cons-style equation: index in left subtree forwards to [l]. *)
Lemma window_size_t_Node_lt (l : mmtree nat) x r i :
  i < size (mmtree_to_seq l) ->
  window_size_t i (Node l x r) = window_size_t i l.
Proof. by rewrite /window_size_t -/window_size_t => ->. Qed.

(** At the root index, the window covers the root and the right subtree. *)
Lemma window_size_t_Node_eq l x (r : mmtree nat) :
  window_size_t (size (mmtree_to_seq l)) (Node l x r) =
    (size (mmtree_to_seq r)).+1.
Proof. by rewrite /window_size_t -/window_size_t ltnn eqxx. Qed.

(** Index above the root forwards to the right subtree with shifted index. *)
Lemma window_size_t_Node_gt (l : mmtree nat) x r i :
  size (mmtree_to_seq l) < i ->
  window_size_t i (Node l x r) =
    window_size_t (i - (size (mmtree_to_seq l)).+1) r.
Proof.
move=> H.
have Hi1 : (i < size (mmtree_to_seq l)) = false
  by apply/negbTE; rewrite -leqNgt; exact: ltnW.
have Hi2 : (i == size (mmtree_to_seq l)) = false
  by apply/eqP=> Heq; rewrite -Heq ltnn in H.
by rewrite /window_size_t -/window_size_t Hi1 Hi2.
Qed.

(** Cons-style equation for [has_left_child_t]: index in left subtree. *)
Lemma has_left_child_t_Node_lt (l : mmtree nat) x r i :
  i < size (mmtree_to_seq l) ->
  has_left_child_t i (Node l x r) = has_left_child_t i l.
Proof. by rewrite /has_left_child_t -/has_left_child_t => ->. Qed.

(** Root has a left child iff the left subtree is non-empty. *)
Lemma has_left_child_t_Node_eq l x (r : mmtree nat) :
  has_left_child_t (size (mmtree_to_seq l)) (Node l x r) =
    (0 < size (mmtree_to_seq l)).
Proof. by rewrite /has_left_child_t -/has_left_child_t ltnn eqxx. Qed.

(** Index above the root forwards [has_left_child_t] to right subtree. *)
Lemma has_left_child_t_Node_gt (l : mmtree nat) x r i :
  size (mmtree_to_seq l) < i ->
  has_left_child_t i (Node l x r) =
    has_left_child_t (i - (size (mmtree_to_seq l)).+1) r.
Proof.
move=> H.
have Hi1 : (i < size (mmtree_to_seq l)) = false
  by apply/negbTE; rewrite -leqNgt; exact: ltnW.
have Hi2 : (i == size (mmtree_to_seq l)) = false
  by apply/eqP=> Heq; rewrite -Heq ltnn in H.
by rewrite /has_left_child_t -/has_left_child_t Hi1 Hi2.
Qed.

(** In-order seq of [Node l x r] has size [|l| + |r| + 1]. *)
Lemma size_mmtree_to_seq_node (l : mmtree nat) (x : nat) (r : mmtree nat) :
  size (mmtree_to_seq (Node l x r)) =
    size (mmtree_to_seq l) + (size (mmtree_to_seq r)).+1.
Proof. by rewrite /= size_cat /= addnS. Qed.

(** Position 0 (leftmost vertex) never has a left child. *)
Lemma has_left_child_t_0 : forall t, has_left_child_t 0 t = false.
Proof.
elim => [|l IHl x r _] //=.
rewrite /has_left_child_t -/has_left_child_t.
case Hsl : (0 < size (mmtree_to_seq l)).
  by rewrite IHl.
have -> : (0 == size (mmtree_to_seq l)) = true.
  by case: (size (mmtree_to_seq l)) Hsl.
by case: (size (mmtree_to_seq l)) Hsl.
Qed.

(* ----- Agreement: tree-level matches seq-level on valid mmtrees ---------- *)

(** Bridge: tree-level [window_size_t] agrees with seq-level [window_size]
    on the in-order traversal of any valid mmtree. *)
Lemma window_size_t_eq : forall t i,
  valid_mm t ->
  window_size i (mmtree_to_seq t) = window_size_t i t.
Proof.
elim => [|l IHl x r IHr] i.
  by rewrite /window_size /window_size_fuel.
case=> Hmm [Hvl Hvr].
case: (ltngtP i (size (mmtree_to_seq l))) => Hi.
- by rewrite (ws_bridge_left Hmm Hi) (@window_size_t_Node_lt l x r i Hi) IHl.
- rewrite (ws_bridge_right Hmm Hi) (@window_size_t_Node_gt l x r i Hi).
  rewrite IHr //.
  by rewrite -subnDA addn1.
- have HiE : i = size (mmtree_to_seq l) by [].
  rewrite HiE (ws_bridge_root Hmm) window_size_t_Node_eq.
  rewrite size_mmtree_to_seq_node addnC.
  by rewrite -addnBA // subnn addn0.
Qed.

(** Bridge: tree-level and seq-level [has_left_child] agree. *)
Lemma has_left_child_t_eq : forall t i,
  valid_mm t ->
  has_left_child i (mmtree_to_seq t) = has_left_child_t i t.
Proof.
elim => [|l IHl x r IHr] i.
  by rewrite /has_left_child /has_left_child_fuel; case: i.
case=> Hmm [Hvl Hvr].
case: (ltngtP i (size (mmtree_to_seq l))) => Hi.
- rewrite (hlc_bridge_left Hmm Hi).
  by rewrite (@has_left_child_t_Node_lt l x r i Hi) IHl.
- rewrite (hlc_bridge_right Hmm Hi) (@has_left_child_t_Node_gt l x r i Hi).
  rewrite IHr //.
  by rewrite -subnDA addn1.
- have HiE : i = size (mmtree_to_seq l) by [].
  by rewrite HiE (hlc_bridge_root Hmm) has_left_child_t_Node_eq.
Qed.

(** Bridge: tree-level and seq-level [is_internal] agree. *)
Lemma is_internal_t_eq : forall t i,
  valid_mm t ->
  is_internal i (mmtree_to_seq t) = is_internal_t i t.
Proof.
move=> t i Hv.
by rewrite /is_internal /is_internal_t (window_size_t_eq i Hv).
Qed.

(* ----- Tree-level: endpoint => next has left child ---------------------- *)

(** Tree-level: an endpoint at position [k] is immediately followed (at
    [k.+1]) by a vertex with a left child.  Used to bound [S_w_seq]. *)
Lemma endpoint_implies_next_t : forall t k,
  valid_mm t ->
  k.+1 < size (mmtree_to_seq t) ->
  ~~ is_internal_t k t -> has_left_child_t k.+1 t.
Proof.
elim => [|l IHl x r IHr] k.
  by rewrite /=.
case=> Hmm [Hvl Hvr].
rewrite size_mmtree_to_seq_node => Hk.
rewrite /is_internal_t size_mmtree_to_seq_node.
case: (ltngtP k (size (mmtree_to_seq l))) => [Hkl | Hkl | Hkl].
- (* k < |sl| *)
  case: (ltngtP k.+1 (size (mmtree_to_seq l))) => [Hk1l | Hk1l | Hk1l].
  + (* k.+1 < |sl|: recurse on left *)
    move=> Hep.
    rewrite (@has_left_child_t_Node_lt l x r k.+1 Hk1l).
    apply: IHl => //.
    move: Hep.
    have Hkbnd : k < size (mmtree_to_seq l) + (size (mmtree_to_seq r)).+1
      by apply: ltn_addr.
    rewrite Hkbnd /=.
    rewrite (@window_size_t_Node_lt l x r k Hkl).
    by rewrite /is_internal_t Hkl /=.
  + (* size sl < k.+1, but k < size sl: contradiction *)
    exfalso.
    move: Hk1l; rewrite ltnS => H1.
    by have := leq_ltn_trans H1 Hkl; rewrite ltnn.
  + (* k.+1 = size sl: at root, has_left_child_t k.+1 = (0 < |sl|) *)
    move=> _.
    rewrite Hk1l has_left_child_t_Node_eq.
    exact: leq_ltn_trans (leq0n _) Hkl.
- (* k > |sl|: in right subtree *)
  have Hk1l : size (mmtree_to_seq l) < k.+1 by exact: ltn_trans Hkl _.
  rewrite (@has_left_child_t_Node_gt l x r k.+1 Hk1l).
  have Hshift : k.+1 - (size (mmtree_to_seq l)).+1 =
                (k - (size (mmtree_to_seq l)).+1).+1
    by rewrite !subSn // ?ltnW //=.
  rewrite Hshift => Hep.
  have Hk_full : k < size (mmtree_to_seq l) + (size (mmtree_to_seq r)).+1
    by apply: leq_trans (leqnSn _) Hk.
  have Hk1_minus : k.+1 - (size (mmtree_to_seq l)).+1 < size (mmtree_to_seq r).
    rewrite ltn_subLR; last by rewrite ltnS ltnW.
    by rewrite addSn -addnS.
  have Hk_minus : k - (size (mmtree_to_seq l)).+1 < size (mmtree_to_seq r).
    apply: ltn_trans Hk1_minus.
    by rewrite Hshift ltnSn.
  apply: IHr => //.
  + by rewrite -Hshift.
  + rewrite /is_internal_t Hk_minus /=.
    move: Hep.
    rewrite Hk_full /=.
    by rewrite (@window_size_t_Node_gt l x r k Hkl).
- (* k = |sl|: at root, contradiction with ~~ is_internal *)
  have Hk_full : k < size (mmtree_to_seq l) + (size (mmtree_to_seq r)).+1
    by apply: leq_trans (leqnSn _) Hk.
  rewrite Hk_full /=.
  rewrite Hkl window_size_t_Node_eq.
  case Hszr : (size (mmtree_to_seq r)) => [|n0] /=.
  - move=> _.
    by exfalso; move: Hk; rewrite Hkl Hszr addn1 ltnn.
  - by [].
Qed.

(* ----- Tree-level: LR_pred_is_endpoint ---------------------------------- *)

(** Tree-level: the predecessor of an LR-vertex (D-vertex) is an endpoint.
    Key structural property used in the bit-recovery lemmas. *)
Lemma LR_pred_is_endpoint_t : forall t i,
  valid_mm t ->
  0 < i -> is_internal_t i t -> has_left_child_t i t ->
  ~~ is_internal_t i.-1 t.
Proof.
elim => [|l IHl x r IHr] i.
  by [].
case=> Hmm [Hvl Hvr] Hi0 Hint Hlc.
move: Hint Hlc; rewrite /is_internal_t.
rewrite size_mmtree_to_seq_node.
case: (ltngtP i (size (mmtree_to_seq l))) => [Hil | Hil | Hil].
- (* i < |sl|: in left subtree *)
  rewrite (@window_size_t_Node_lt l x r i Hil).
  rewrite (@has_left_child_t_Node_lt l x r i Hil).
  have Hibd : i < size (mmtree_to_seq l) + (size (mmtree_to_seq r)).+1
    by exact: ltn_addr.
  rewrite Hibd /= => Hwin Hlc.
  have Hint_l : is_internal_t i l by rewrite /is_internal_t Hil /=.
  have IH := IHl _ Hvl Hi0 Hint_l Hlc.
  have Hi1l : i.-1 < size (mmtree_to_seq l)
    by apply: leq_ltn_trans (leq_pred _) Hil.
  rewrite (@window_size_t_Node_lt l x r i.-1 Hi1l).
  have Hi1bd : i.-1 < size (mmtree_to_seq l) + (size (mmtree_to_seq r)).+1
    by exact: ltn_addr.
  rewrite Hi1bd /=.
  by move: IH; rewrite /is_internal_t Hi1l /=.
- (* i > |sl|: in right subtree *)
  rewrite (@window_size_t_Node_gt l x r i Hil).
  rewrite (@has_left_child_t_Node_gt l x r i Hil).
  case Hibd : (i < size (mmtree_to_seq l) + (size (mmtree_to_seq r)).+1);
    last by [].
  rewrite /= => Hwin Hlc.
  set i' := i - (size (mmtree_to_seq l)).+1.
  have Hi'_lt : i' < size (mmtree_to_seq r).
    rewrite /i' ltn_subLR; last exact: Hil.
    by rewrite addSn -addnS.
  case Ei1 : (i.-1 == size (mmtree_to_seq l)).
  + (* i.-1 = |sl|: i = (size sl).+1, i' = 0, has_left_child_t 0 r is false *)
    move/eqP: Ei1 => Ei1.
    have Hi_eq : i = (size (mmtree_to_seq l)).+1
      by rewrite -Ei1 (prednK Hi0).
    have Hi'0 : i' = 0 by rewrite /i' Hi_eq subnn.
    by exfalso; rewrite -/i' Hi'0 has_left_child_t_0 in Hlc.
  + (* i.-1 > |sl|: in right subtree *)
    have Hi1_gt : size (mmtree_to_seq l) < i.-1.
      rewrite ltn_neqAle eq_sym Ei1 /=.
      by rewrite -ltnS prednK //; exact: ltnW.
    rewrite (@window_size_t_Node_gt l x r i.-1 Hi1_gt).
    have Hi1bd' : i.-1 < size (mmtree_to_seq l) + (size (mmtree_to_seq r)).+1
      by apply: leq_ltn_trans (leq_pred _) Hibd.
    rewrite Hi1bd' /=.
    have Hi'0 : 0 < i'.
      rewrite /i' subn_gt0.
      rewrite ltn_neqAle.
      apply/andP; split.
        apply/eqP=> Heq.
        move/eqP: Ei1; apply.
        by rewrite -Heq /=.
      by [].
    have Hint_r : is_internal_t i' r
      by rewrite /is_internal_t Hi'_lt /=.
    have IH := IHr _ Hvr Hi'0 Hint_r Hlc.
    have Hi1_shift : i.-1 - (size (mmtree_to_seq l)).+1 = i'.-1
      by rewrite /i' predn_sub.
    rewrite Hi1_shift.
    move: IH; rewrite /is_internal_t.
    have Hi'1_lt : i'.-1 < size (mmtree_to_seq r)
      by apply: leq_ltn_trans (leq_pred _) Hi'_lt.
    by rewrite Hi'1_lt /=.
- (* i = |sl|: at root *)
  rewrite Hil window_size_t_Node_eq has_left_child_t_Node_eq.
  have Hibd : size (mmtree_to_seq l) <
                size (mmtree_to_seq l) + (size (mmtree_to_seq r)).+1
    by rewrite -[X in X < _]addn0 ltn_add2l.
  rewrite Hibd /=.
  move=> _ Hsl_pos.
  have Hi1l : (size (mmtree_to_seq l)).-1 < size (mmtree_to_seq l)
    by rewrite -ltnS prednK.
  rewrite (@window_size_t_Node_lt l x r _ Hi1l).
  have Hi1bd : (size (mmtree_to_seq l)).-1 <
                 size (mmtree_to_seq l) + (size (mmtree_to_seq r)).+1
    by apply: leq_ltn_trans (leq_pred _) Hibd.
  rewrite Hi1bd /=.
  rewrite -(window_size_t_eq _ Hvl) -ltnNge.
  by rewrite (window_size_last Hsl_pos).
Qed.

(* ----- Seq-level corollaries ----------------------------------------- *)

(** Seq-level corollary of [endpoint_implies_next_t] via the mmtree bridge. *)
Lemma endpoint_implies_next_has_left_child :
  forall (k : nat) (w : seq nat),
    uniq w -> k.+1 < size w -> ~~ is_internal k w -> has_left_child k.+1 w.
Proof.
move=> k w Huniq Hk1 Hep.
have Hroundtrip : mmtree_to_seq (mmtree_of_seq_mm w) = w
  by exact: mmtree_of_seq_mmK.
have Hv : valid_mm (mmtree_of_seq_mm w) by exact: valid_mm_build.
rewrite -Hroundtrip.
rewrite (has_left_child_t_eq _ Hv).
apply: endpoint_implies_next_t => //.
- by rewrite Hroundtrip.
- by rewrite -(is_internal_t_eq _ Hv) Hroundtrip.
Qed.

(** Seq-level corollary of [LR_pred_is_endpoint_t]: D-vertex predecessor is
    always an endpoint.  Used by the bit-recovery proofs in
    [psi_cdindex_core.v]. *)
Lemma LR_pred_is_endpoint :
  forall (i : nat) (w : seq nat),
    uniq w -> 0 < i -> is_internal i w ->
    has_left_child i w -> ~~ is_internal i.-1 w.
Proof.
move=> i w Huniq Hi0 Hint Hlc.
have Hroundtrip : mmtree_to_seq (mmtree_of_seq_mm w) = w
  by exact: mmtree_of_seq_mmK.
have Hv : valid_mm (mmtree_of_seq_mm w) by exact: valid_mm_build.
rewrite -Hroundtrip (is_internal_t_eq _ Hv).
apply: LR_pred_is_endpoint_t => //.
- by rewrite -(is_internal_t_eq _ Hv) Hroundtrip.
- by rewrite -(has_left_child_t_eq _ Hv) Hroundtrip.
Qed.

Example endpoint_next_has_left_child_ex :
  has_left_child 1 [:: 3; 1; 5; 4; 2; 6].
Proof. by vm_compute. Qed.

Example endpoint_next_has_left_child_ex2 :
  has_left_child 4 [:: 3; 1; 5; 4; 2; 6].
Proof. by vm_compute. Qed.

Example LR_pred_is_endpoint_ex :
  ~~ is_internal 0 [:: 3; 1; 5; 4; 2; 6].
Proof. by vm_compute. Qed.

Example LR_pred_is_endpoint_ex2 :
  ~~ is_internal 3 [:: 3; 1; 5; 4; 2; 6].
Proof. by vm_compute. Qed.

Example LR_pred_is_endpoint_ex3 :
  ~~ is_internal 4 [:: 3; 1; 4; 7; 5; 9; 2; 6].
Proof. by vm_compute. Qed.
