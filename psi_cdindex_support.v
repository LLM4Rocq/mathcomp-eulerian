(* psi_cdindex_support.v — phi_w_support_general and structural helpers.

   Split from psi_cdindex.v to reduce -vo compilation memory.
   The cd-width/D-offset and expand_cde membership infrastructure now
   lives in psi_cdindex_support_defs.v. This file keeps the tree/phi_w
   support lemmas, phi_w_support_general, and the Fact #3 wrapper
   layer. *)

From mathcomp Require Import all_ssreflect.
Require Import mmtree psi_core psi_comm psi_descent_v2 psi_descent_thms.
Require Import psi_cdindex_core psi_cdindex_witness.
Require Export psi_cdindex_support_defs.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Block /=-driven reduction through the fuel parameters of window_size and *)
(* has_left_child.  These Fixpoints recurse over fuel = size s, and any /= *)
(* that fires inside a deep proof unfolds them through every layer.          *)
Arguments window_size_fuel : simpl never.
Arguments has_left_child_fuel : simpl never.

(* ========================================================================= *)
(* ===== M6.8: phi_w_support_general ======================================= *)
(* X ∈ expand_cde(Φ_w) ⟺ S_w ⊆ ω(desc(X)) *)
(* ========================================================================= *)

(* -- S_w_seq elements are bounded: k ∈ S_w_seq w → k < (size w).-2 -- *)
(* S_w_seq w = [seq i.-1 | i <- iota 1 (size w).-1                         *)
(*                        & is_D_letter (classify_vertex_cde i w)].          *)
(* Since i ∈ iota 1 (size w).-1, i ranges from 1 to (size w).-1.            *)
(* The last position (size w).-1 is always an endpoint (leaf in the          *)
(* min-max tree), so is_D_letter there is false.                             *)
(* Hence max i in the filter is (size w).-2, giving k = i.-1 ≤ (size w).-3. *)
(* Thus k < (size w).-2 = (size w).-1.-1.                                   *)

(** Every element of [S_w_seq w] is bounded: [k < (size w).-2].  Holds
    because the last vertex of [w] is always an endpoint, hence cannot
    contribute a [D] letter. *)
Lemma S_w_seq_bound w k :
  k \in S_w_seq w -> k < (size w).-1.-1.
Proof.
rewrite /S_w_seq.
move=> /mapP [i].
rewrite mem_filter => /andP [Hd Hi] ->.
move: Hi; rewrite mem_iota => /andP [Hi1 Hi2].
(* Need: i.-1 < (size w).-1.-1, i.e., i < (size w).-1 *)
suff Hlt : i < (size w).-1.
  by case: i Hi1 Hi2 Hd Hlt => [//|i'] _ _ _ /=; case: (size w) => [|[|n]] //=.
rewrite ltn_neqAle.
have Hle : i <= (size w).-1.
  by rewrite -ltnS; case: (size w) Hi2 => [|n] //=.
rewrite Hle andbT.
apply/negP => /eqP Heqi.
(* i = (size w).-1: the last position is always an endpoint *)
move: Hd; rewrite Heqi /is_D_letter /classify_vertex_cde.
(* is_internal (size w).-1 w = false because window_size = 1 *)
have Hws1 : window_size (size w).-1 w <= 1.
  apply: leq_trans (window_size_bound (size w).-1 w) _.
  case: (size w) Hi2 => [|[|n]] //= _.
  by rewrite subSS subSnn.
have Hnint : is_internal (size w).-1 w = false.
  rewrite /is_internal.
  case Hlt : ((size w).-1 < size w) => //=.
  by rewrite ltnNge Hws1.
by rewrite Hnint.
Qed.

(** Vertex classification is invariant under [psi j]. *)
Lemma classify_vertex_cde_psi j i w :
  uniq w ->
  classify_vertex_cde i (psi j w) = classify_vertex_cde i w.
Proof.
move=> Hu.
rewrite /classify_vertex_cde.
by rewrite (is_internal_apply_psis [:: j]) //
           (has_left_child_apply_psis [:: j]).
Qed.

(** [S_w_seq] is invariant under [psi j], hence constant on each M-class. *)
(* -- Structural helpers for cde_total_width and D_offsets --------------- *)
(* These provide explicit decomposition lemmas for phi_w, D_offsets, and  *)
(* S_w_seq at mm_pos, producing small proof terms that avoid heavy        *)
(* simpl/vm_compute during -vo compilation.                               *)

(** [mm_pos s < (size s).-1] for uniq [s] of size at least 2.  Ensures
    the root of the min-max tree is an internal vertex. *)
Lemma mm_pos_lt_pred (s : seq nat) :
  uniq s -> 1 < size s -> mm_pos s < (size s).-1.
Proof.
case: s => [//|a s0] Hu Hsz.
set s := a :: s0. set j := mm_pos s.
have Hne : s <> [::] by [].
have Hj : j < size s := mm_pos_lt Hne.
apply/negP => /negP; rewrite -leqNgt => Hle.
have Heq : j = (size s).-1.
  apply/eqP; rewrite eqn_leq Hle andbT.
  by case: (size s) Hj => [|n] //=; rewrite ltnS.
have Hdrop_sz : size (drop j s) = 1.
  rewrite size_drop Heq.
  by case: (size s) Hsz Hj => [//|[//|n]] _ _ /=; rewrite subSS subSnn.
have [Hno_min Hno_max] := notin_take_mm Hne.
have Hmin_drop :
  foldr minn (head 0 s) (behead s) \in drop j s.
  have Hmin_in_s : foldr minn (head 0 s) (behead s) \in s.
    have := min_in (behead s) (head 0 s).
    by have ->: head 0 s :: behead s = s by [].
  rewrite -[X in _ \in X](cat_take_drop j s) mem_cat in Hmin_in_s.
  case/orP: Hmin_in_s => [Hin|//].
  by rewrite Hin in Hno_min.
have Hmax_drop :
  foldr maxn (head 0 s) (behead s) \in drop j s.
  have Hmax_in_s : foldr maxn (head 0 s) (behead s) \in s.
    have := max_in (behead s) (head 0 s).
    by have ->: head 0 s :: behead s = s by [].
  rewrite -[X in _ \in X](cat_take_drop j s) mem_cat in Hmax_in_s.
  case/orP: Hmax_in_s => [Hin|//].
  by rewrite Hin in Hno_max.
have [x Hdrop_eq] : exists x, drop j s = [:: x]
  by case: (drop j s) Hdrop_sz =>
     [//|x [|y t]] //= _; exists x.
have Hall_eq : forall y, y \in s -> y = x.
  move=> y Hy.
  have Hmin_x :
    foldr minn (head 0 s) (behead s) = x
    by move: Hmin_drop; rewrite Hdrop_eq mem_seq1
       => /eqP.
  have Hmax_x :
    foldr maxn (head 0 s) (behead s) = x
    by move: Hmax_drop; rewrite Hdrop_eq mem_seq1
       => /eqP.
  have Hmin' : x <= y.
    rewrite -Hmin_x; apply: psi_core.foldr_minn_le.
    by have ->: head 0 s :: behead s = s by [].
  have Hmax' : y <= x.
    rewrite -Hmax_x; apply: psi_core.foldr_maxn_ge.
    by have ->: head 0 s :: behead s = s by [].
  by apply/eqP; rewrite eqn_leq Hmax' Hmin'.
move: Hu; rewrite /s /= => /andP [Hnotin _].
have Ha_eq : a = x by apply: Hall_eq; rewrite mem_head.
have Hb : head 0 s0 \in s.
  rewrite [in X in _ \in X]/s !inE; apply/orP; right.
  by case: (s0) Hsz => [|b t] _ //=; rewrite mem_head.
have Hh_eq : head 0 s0 = x by apply: Hall_eq.
have Hsz0 : 0 < size s0 by case: (s0) Hsz.
have Hh_eq2 : head 0 s0 = a by rewrite Hh_eq.
have : a \in s0.
  rewrite -Hh_eq2.
  by case: (s0) Hsz0 => [|b t] //= _; rewrite mem_head.
move=> Hain; by rewrite Hain in Hnotin.
Qed.

(** Classification splits across [mm_pos]: for [i < j = mm_pos s], use
    classification on the left subtree [take j s]. *)
Lemma classify_vertex_left i a s0 :
  let j := mm_pos (a :: s0) in
  i < j ->
  classify_vertex_cde i (a :: s0) =
  classify_vertex_cde i (take j (a :: s0)).
Proof.
move=> /= Hij.
set j := mm_pos (a :: s0). set s := a :: s0.
have Hj : j < size s
  := mm_pos_lt
     (fun H : s = [::] => ltac:(discriminate H)).
rewrite /classify_vertex_cde /is_internal.
rewrite (window_size_cons i a s0) -/s -/j Hij.
rewrite (has_left_child_cons i a s0) -/s -/j Hij.
have -> : i < size s = true
  by exact: ltn_trans Hij Hj.
have ->: size (take j s) = j by rewrite size_takel // ltnW.
by rewrite Hij.
Qed.

(** Classification on the right side of [mm_pos]: for [i > j], shift
    index by [j.+1] and classify in the right subtree [drop j.+1 s]. *)
Lemma classify_vertex_right i a s0 :
  let j := mm_pos (a :: s0) in
  j < i ->
  classify_vertex_cde i (a :: s0) =
  classify_vertex_cde (i - j - 1)
    (drop j.+1 (a :: s0)).
Proof.
move=> /= Hji.
set j := mm_pos (a :: s0). set s := a :: s0.
have Hj : j < size s
  := mm_pos_lt
     (fun H : s = [::] => ltac:(discriminate H)).
rewrite /classify_vertex_cde /is_internal.
rewrite (window_size_cons i a s0) -/s -/j.
rewrite (has_left_child_cons i a s0) -/s -/j.
have -> : (i < j) = false by rewrite ltnNge ltnW.
have -> : (i == j) = false by apply: gtn_eqF.
suff -> : (i < size s) =
  (i - j - 1 < size (drop j.+1 s)) by done.
rewrite size_drop /s /=.
case: i Hji => [//|i] Hji /=.
rewrite ltnS subSS.
have ->: i.+1 - j - 1 = i - j by rewrite subnAC subn1.
by rewrite ltn_sub2rE // ltnW.
Qed.

(** Classification at the root [j = mm_pos s] of a uniq seq of size at
    least 2: [D_letter] if the root has a left subtree ([j > 0]), else
    [C_letter]. *)
Lemma classify_vertex_mm a s0 :
  let j := mm_pos (a :: s0) in
  uniq (a :: s0) -> 1 < size (a :: s0) ->
  classify_vertex_cde j (a :: s0) =
  (if 0 < j then D_letter else C_letter).
Proof.
move=> /= Hu Hsz.
set j := mm_pos (a :: s0). set s := a :: s0.
have Hj : j < size s
  := mm_pos_lt
     (fun H : s = [::] => ltac:(discriminate H)).
have Hjp : j < (size s).-1 by apply: mm_pos_lt_pred; rewrite /s.
rewrite /classify_vertex_cde /is_internal.
rewrite (window_size_cons j a s0) -/s -/j ltnn eqxx Hj.
have -> : 1 < size s - j = true
  by rewrite ltn_subRL addnC /= ltnS.
rewrite /=.
rewrite (has_left_child_cons j a s0) -/s -/j
  ltnn eqxx.
by case: (0 < j).
Qed.

(** Cons decomposition of [phi_w] when [mm_pos = 0] (root has no left
    subtree): the root contributes a [C_letter] and recursion peels into
    the tail. *)
Lemma phi_w_cons_mm0 a rest :
  mm_pos (a :: rest) = 0 ->
  1 < size (a :: rest) ->
  phi_w (a :: rest) = C_letter :: phi_w rest.
Proof.
move=> Hmm Hsz.
rewrite /phi_w /phi'_w /=.
rewrite /classify_vertex_cde /is_internal.
rewrite (window_size_cons 0 a rest)
  -/(mm_pos (a :: rest)) Hmm ltnn eqxx subn0.
rewrite Hsz /= has_left_child_0 /=.
congr cons; congr (filter _).
apply: (@eq_from_nth _ E_letter).
  by rewrite !size_map !size_iota.
move=> k Hk.
rewrite size_map size_iota in Hk.
rewrite !(nth_map 0) ?size_iota //.
rewrite !nth_iota // add0n.
have H := classify_skip_mm0 Hmm (ltn0Sn k).
rewrite /classify_vertex_cde /is_internal in H.
rewrite -[1 + k]/(k.+1).
rewrite subn1 /= in H.
exact H.
Qed.

(** Decomposition of [phi_w] at [mm_pos > 0]: [phi_w s] equals the cd-index
    of the left subtree concatenated with [D_letter] then the cd-index of
    the right subtree. *)
Lemma phi_w_decomp_mm a s0 :
  let s := a :: s0 in
  let j := mm_pos s in
  uniq s -> 1 < size s -> 0 < j ->
  phi_w s = phi_w (take j s) ++
    D_letter :: phi_w (drop j.+1 s).
Proof.
move=> /= Hu Hsz Hj0.
set s := a :: s0. set j := mm_pos s.
have Hne : s <> [::] by [].
have Hj : j < size s := mm_pos_lt Hne.
rewrite /phi_w /phi'_w.
have Hiota_split : iota 0 (size s) =
  iota 0 j ++ j :: iota j.+1 (size s - j.+1).
  rewrite -cat1s catA.
  have ->: iota 0 j ++ [:: j] = iota 0 j.+1.
    by rewrite -addn1 iotaD /= add0n.
  by rewrite -iotaD subnKC.
rewrite Hiota_split !map_cat /= !filter_cat /=.
rewrite (classify_vertex_mm Hu Hsz) Hj0 /=.
congr (_ ++ _ :: _).
- congr (filter _ _).
  have Hsz_take : size (take j s) = j by rewrite size_takel // ltnW.
  rewrite Hsz_take.
  apply/eq_in_map => i; rewrite mem_iota add0n => /andP [_ Hi].
  by apply: classify_vertex_left Hi.
- congr (filter _ _).
  rewrite -[RHS]/(map _ (iota 0
    (size (drop j.+1 s)))).
  rewrite size_drop.
  apply: (@eq_from_nth _ E_letter).
    by rewrite !size_map !size_iota.
  move=> k Hk.
  rewrite size_map size_iota in Hk.
  rewrite !(nth_map 0) ?size_iota //.
  rewrite !nth_iota ?add0n //.
  have Hjk : j < j.+1 + k
    by rewrite addSn ltnS leq_addr.
  rewrite (classify_vertex_right Hjk).
  by rewrite addSn -addnS addKn subn1.
Qed.

(** Cons decomposition of [D_offsets] over a [C] head: every offset
    shifts by 1 bit. *)
Lemma D_offsets_cons_C m :
  D_offsets (C_letter :: m) =
  [seq x.+1 | x <- D_offsets m].
Proof.
rewrite /D_offsets /=.
rewrite -map_comp.
have Hiota : iota 1 (size m) = [seq j.+1 | j <- iota 0 (size m)].
  by elim: (size m) 1 0 => [|n IH] m1 m2 //=; rewrite IH.
rewrite Hiota filter_map -map_comp.
rewrite (eq_filter (a2 := fun i => is_D_letter (nth C_letter m i)));
  last by move=> i.
apply/eq_in_map => i Hi /=.
by rewrite /cde_offset /= /cde_width add1n.
Qed.

(** Concatenation decomposition of [D_offsets] across a [D] inserted
    between [m1] and [m2]: left offsets, then the [D] at offset
    [cde_total_width m1], then right offsets shifted by
    [cde_total_width m1 + 2]. *)
Lemma D_offsets_cat_D m1 m2 :
  D_offsets (m1 ++ D_letter :: m2) =
  D_offsets m1 ++
  cde_total_width m1 ::
  [seq cde_total_width m1 + 2 + x
  | x <- D_offsets m2].
Proof.
rewrite /D_offsets.
have Hsz : size (m1 ++ D_letter :: m2) =
  size m1 + (size m2).+1
  by rewrite size_cat /=.
rewrite Hsz iotaD add0n filter_cat map_cat.
have Hleft :
  [seq cde_offset (m1 ++ D_letter :: m2) i
  | i <- [seq i <- iota 0 (size m1)
  | is_D_letter
      (nth C_letter
        (m1 ++ D_letter :: m2) i)]]
  = D_offsets m1.
  rewrite /D_offsets.
  rewrite (eq_in_filter
    (a2 := fun i => is_D_letter (nth C_letter m1 i))); last first.
    move=> i; rewrite mem_iota add0n => /andP [_ Hi].
    by rewrite nth_cat Hi.
  apply/eq_in_map => i Hi.
  have Hi_lt : i < size m1.
    move: Hi; rewrite mem_filter mem_iota add0n.
    by case/andP=> _ /andP [].
  by rewrite /cde_offset take_cat Hi_lt.
have Hmid_f : is_D_letter (nth C_letter
  (m1 ++ D_letter :: m2) (size m1)) = true
  by rewrite nth_cat ltnn subnn.
have Hmid_o : cde_offset (m1 ++ D_letter :: m2)
  (size m1) = cde_total_width m1.
  rewrite /cde_offset /cde_total_width.
  by rewrite take_cat ltnn subnn take0 cats0.
have Hcons : iota (size m1) (size m2).+1 =
  size m1 :: iota (size m1).+1 (size m2) by [].
rewrite Hleft Hcons /= Hmid_f /= Hmid_o.
congr (cat (D_offsets m1)); congr (cons (cde_total_width m1)).
(* Goal: map (cde_offset (m1 ++ D_letter :: m2))
     (filter (is_D_letter ∘ nth C_letter (m1 ++ D_letter :: m2))
       (iota (size m1).+1 (size m2)))
   = [seq cde_total_width m1 + 2 + x | x <- D_offsets m2]
   Use iota shift:
   iota (size m1).+1 (size m2)
     = map (addn (size m1).+1) (iota 0 (size m2)) *)
have Hshift : iota (size m1).+1 (size m2) =
  [seq (size m1).+1 + i | i <- iota 0 (size m2)].
  by rewrite -iotaDl addn0.
rewrite Hshift filter_map -map_comp /D_offsets -map_comp.
rewrite (eq_filter (a2 := fun i =>
  is_D_letter (nth C_letter m2 i))); last first.
  move=> k /=.
  rewrite nth_cat.
  have HltF : ((size m1).+1 + k < size m1) = false
    by rewrite ltnNge
       (leq_trans (leqnSn (size m1)) (leq_addr k (size m1).+1)).
  by rewrite HltF addSn -addnS addKn.
apply/eq_in_map => k Hk /=.
have Hk_lt : k < size m2.
  move: Hk; rewrite mem_filter mem_iota add0n.
  by case/andP=> _ /andP [].
rewrite /cde_offset /cde_total_width take_cat.
have HltF : ((size m1).+1 + k < size m1) = false
  by rewrite ltnNge
     (leq_trans (leqnSn (size m1)) (leq_addr k (size m1).+1)).
by rewrite HltF addSn -addnS addKn /= map_cat sumn_cat addnA.
Qed.

(** Decomposition of [S_w_seq] at [mm_pos > 0], parallel to
    [phi_w_decomp_mm]: left positions, then [j.-1] (the D-position
    contributed by the root), then right positions shifted by [j.+1]. *)
Lemma S_w_seq_decomp_mm a s0 :
  let s := a :: s0 in
  let j := mm_pos s in
  uniq s -> 1 < size s -> 0 < j ->
  S_w_seq s =
  S_w_seq (take j s) ++ j.-1 ::
  [seq x + j.+1 | x <- S_w_seq (drop j.+1 s)].
Proof.
move=> /= Hu Hsz Hj0.
set s := a :: s0. set j := mm_pos s.
have Hne : s <> [::] by [].
have Hj : j < size s := mm_pos_lt Hne.
rewrite /S_w_seq.
have Hsplit : iota 1 (size s).-1 =
  iota 1 j.-1 ++ j :: iota j.+1 ((size s).-1 - j).
  have Hjpred : j <= (size s).-1 by
    rewrite -ltnS (prednK (ltnW Hsz)).
  have Hlen : (size s).-1 = j.-1 + ((size s).-1 - j).+1 by
    rewrite -addn1 addnA addnAC addn1 (prednK Hj0) subnKC.
  by rewrite {1}Hlen iotaD add1n (prednK Hj0).
rewrite Hsplit !filter_cat /= !map_cat /=.
have Hleft_filter : forall i,
  i \in iota 1 j.-1 ->
  is_D_letter (classify_vertex_cde i s) =
  is_D_letter (classify_vertex_cde i (take j s)).
  move=> i; rewrite mem_iota => /andP [_ Hij].
  have Hij' : i < j.
    have Heq : 1 + j.-1 = j by rewrite add1n prednK.
    by rewrite -Heq.
  by rewrite (classify_vertex_left Hij').
rewrite (eq_in_filter Hleft_filter).
have Hmid :
  is_D_letter (classify_vertex_cde j s) = true
  by rewrite (classify_vertex_mm Hu Hsz) Hj0.
rewrite Hmid /=.
have Hright_filter : forall i,
  i \in iota j.+1 ((size s).-1 - j) ->
  is_D_letter (classify_vertex_cde i s) =
  is_D_letter (classify_vertex_cde (i - j - 1)
    (drop j.+1 s)).
  move=> i; rewrite mem_iota => /andP [Hji _].
  by rewrite (classify_vertex_right Hji).
rewrite (eq_in_filter Hright_filter).
congr (_ ++ _ :: _).
- by rewrite size_takel // ltnW.
- (* After eq_in_filter Hright_filter, filter uses classify (i-j-1) d.
     Strategy: shift index, simplify predicate, exclude 0, use eq_in_map. *)
  set d := drop j.+1 s.
  have Hq0 : is_D_letter (classify_vertex_cde 0 d) = false.
    rewrite /classify_vertex_cde /is_internal.
    case E : (0 < size d) => //=.
    case E2 : (1 < window_size 0 d) => //=.
    by rewrite has_left_child_0.
  have Hnd : (size s).-1 - j = size d.
    rewrite /d size_drop.
    case: (size s) Hsz => [//|[//|m]] _; by rewrite !subSS.
  rewrite Hnd.
  have Hshift : iota j.+1 (size d) = [seq j.+1 + k | k <- iota 0 (size d)]
    by rewrite -iotaDl addn0.
  rewrite Hshift filter_map -map_comp.
  rewrite (eq_filter (a2 := fun k =>
    is_D_letter (classify_vertex_cde k d))); last first.
    by move=> k /=; rewrite addSn -addnS addKn subn1.
  have Hfilt :
    filter (fun k => is_D_letter (classify_vertex_cde k d)) (iota 0 (size d)) =
    filter (fun k => is_D_letter (classify_vertex_cde k d))
           (iota 1 (size d).-1).
    case: (size d) => [//|m]; by rewrite /= Hq0.
  rewrite Hfilt /S_w_seq -map_comp.
  apply: (@eq_in_map nat nat _ _ _).1 => k Hk.
  rewrite mem_filter mem_iota in Hk.
  move: Hk => /andP [_ /andP [Hk1 _]].
  case: k Hk1 => [//|k'] _.
  unfold comp. simpl. by rewrite addnC addnS.
Qed.

(* -- Total width of phi_w = (size w).-1 (structural) ------------------- *)
(* Proved by strong induction on size w with mm_pos decomposition.        *)
(* The mm_pos = 0 case uses phi_w_cons_mm0 (vertex 0 is C).              *)
(* The mm_pos > 0 case uses phi_w_decomp_mm (root is D) and IH for       *)
(* take j w and drop j.+1 w.                                              *)

(** Total bit-width of [phi_w w] equals [(size w).-1] for any uniq [w]
    (proved by structural induction on size with [mm_pos] decomposition).
    Captures that [expand_cde (phi_w w)] elements are descent-bit strings. *)
Lemma cde_total_width_phi_w_all w :
  uniq w ->
  cde_total_width (phi_w w) = (size w).-1.
Proof.
move=> Hu.
suff Hgen : forall n w, size w <= n -> uniq w ->
  cde_total_width (phi_w w) = (size w).-1.
  exact: Hgen (leqnn _) Hu.
move: w Hu => _ _.
elim => [|n IH] w Hsz Hu.
  by move: Hsz; rewrite leqn0 => /eqP/size0nil ->.
case Hsz1 : (size w <= 1).
  case: w Hu Hsz Hsz1 => [//|a [|b s]] //= _ _ _.
  rewrite /cde_total_width /phi_w /phi'_w
    /classify_vertex_cde /is_internal
    /window_size /window_size_fuel
    /mm_pos /min_pos /max_pos /= eqxx /=.
  by [].
have Hsz2 : 1 < size w
  by case: (size w) Hsz1 => [|[|m]].
case Hszn : (size w <= n).
  exact: IH w Hszn Hu.
case: w Hsz Hu Hsz1 Hsz2 Hszn =>
  [//|a rest] Hsz Hu _ Hsz2 Hszn.
set s := a :: rest. set j := mm_pos s.
have Hne : s <> [::] by [].
have Hj : j < size s := mm_pos_lt Hne.
have HuL : uniq (take j s) := take_uniq j Hu.
have HuR : uniq (drop j.+1 s)
  := drop_uniq j.+1 Hu.
have Hsw : size s = n.+1.
  apply/eqP; rewrite eqn_leq Hsz /=.
  by rewrite ltnNge Hszn.
have HszL : size (take j s) <= n.
  rewrite size_takel; last exact: ltnW.
  by rewrite -ltnS -Hsw.
have HszR : size (drop j.+1 s) <= n.
  rewrite size_drop Hsw /=. exact: leq_subr.
have IHL := IH _ HszL HuL.
have IHR := IH _ HszR HuR.
case Hj0 : (0 < j).
  rewrite (phi_w_decomp_mm Hu Hsz2 Hj0).
  (* Use have to state explicit equalities *)
  have HtotalL : cde_total_width (phi_w (take j s)) = (size (take j s)).-1
    := IHL.
  have HtotalR : cde_total_width (phi_w (drop j.+1 s))
                   = (size (drop j.+1 s)).-1 := IHR.
  rewrite cde_total_width_cat HtotalL.
  (* Goal: (size (take j s)).-1
              + cde_total_width (D_letter :: phi_w (drop j.+1 s)) = ... *)
  have -> : cde_total_width (D_letter :: phi_w (drop j.+1 s)) =
    2 + cde_total_width (phi_w (drop j.+1 s)).
    by rewrite /cde_total_width /=.
  rewrite HtotalR.
  rewrite size_takel; last exact: ltnW.
  rewrite size_drop.
  have HszR1 : 0 < size s - j.+1.
    rewrite subn_gt0.
    exact: mm_pos_lt_pred Hu Hsz2.
  (* Goal: j.-1 + (2 + (size s - j.+1).-1) = (size s).-1 *)
  (* We know 0 < j and 0 < size s - j.+1 and j < size s *)
  (* Massage: j.-1 + 2 = j + 1, then j + 1 + (size s - j.+1).-1 *)
  (* = j + 1 + (size s - j.+1 - 1) = j + 1 + size s - j.+1 - 1 = size s - 1 *)
  have Hstep1 : j.-1 + 2 = j.+1 by rewrite addn2 (prednK Hj0).
  have Hstep2 : (size s - j.+1).-1.+1 = size s - j.+1 := prednK HszR1.
  rewrite [j.-1 + _]addnA Hstep1.
  (* now: j.+1 + (size s - j.+1).-1 = (size s).-1 *)
  rewrite -subn1 (addnBA _ HszR1) subnKC; last exact: Hj.
  by rewrite subn1.
move: Hj0; rewrite lt0n => /negbFE /eqP Hj0.
rewrite (phi_w_cons_mm0 Hj0 Hsz2).
have HszR' : size rest <= n.
  by move: Hsz; rewrite /s /= ltnS.
have HuR' : uniq rest.
  by move: Hu; rewrite /s cons_uniq => /andP [].
have HconsC : cde_total_width (C_letter :: phi_w rest) =
  1 + cde_total_width (phi_w rest) by rewrite /cde_total_width /=.
have H0rest : 0 < size rest
  by move: Hsz2; rewrite /s /= ltnS.
rewrite HconsC (IH rest HszR' HuR') /s /=.
by rewrite add1n prednK.
Qed.

(** Sized variant of [cde_total_width_phi_w_all]; states the bit-width
    identity under the usable hypothesis [2 <= size w]. *)
Lemma cde_total_width_phi_w w :
  uniq w -> 2 <= size w ->
  cde_total_width (phi_w w) = (size w).-1.
Proof.
by move=> Hu _; exact: cde_total_width_phi_w_all.
Qed.

(* -- D_offsets of phi_w w = S_w_seq w (structural) ---------------------- *)
(* Same induction structure. The mm_pos = 0 case uses D_offsets_cons_C    *)
(* and S_w_seq_shift. The mm_pos > 0 case uses D_offsets_cat_D,           *)
(* S_w_seq_decomp_mm, and the key identity j.-1 + 2 = j.+1 for j > 0.    *)

(** Headline structural identity: the [D]-offsets of [phi_w w] coincide
    with [S_w_seq w].  Proved by structural induction on size with
    [mm_pos] decomposition. *)
Lemma D_offsets_phi_w_eq_S_w_seq w :
  uniq w -> 2 <= size w ->
  D_offsets (phi_w w) = S_w_seq w.
Proof.
move=> Hu Hsz2.
suff Hgen : forall n w, size w <= n -> uniq w ->
  D_offsets (phi_w w) = S_w_seq w.
  exact: Hgen (leqnn _) Hu.
move: w Hu Hsz2 => _ _ _.
elim => [|n IH] w Hsz Hu.
  by move: Hsz; rewrite leqn0 => /eqP/size0nil ->.
case Hsz1 : (size w <= 1).
  case: w Hu Hsz Hsz1 => [//|a [|b s]] //= _ _ _.
  rewrite /D_offsets /S_w_seq /phi_w /phi'_w
    /classify_vertex_cde /is_internal
    /window_size /window_size_fuel
    /mm_pos /min_pos /max_pos /= eqxx /=.
  by [].
have Hsz2 : 1 < size w
  by case: (size w) Hsz1 => [|[|m]].
case Hszn : (size w <= n).
  exact: IH w Hszn Hu.
case: w Hsz Hu Hsz1 Hsz2 Hszn =>
  [//|a rest] Hsz Hu _ Hsz2 Hszn.
set s := a :: rest. set j := mm_pos s.
have Hne : s <> [::] by [].
have Hj : j < size s := mm_pos_lt Hne.
have HuL : uniq (take j s) := take_uniq j Hu.
have HuR : uniq (drop j.+1 s)
  := drop_uniq j.+1 Hu.
have Hsw : size s = n.+1.
  apply/eqP; rewrite eqn_leq Hsz /=.
  by rewrite ltnNge Hszn.
have HszL : size (take j s) <= n.
  rewrite size_takel; last exact: ltnW.
  by rewrite -ltnS -Hsw.
have HszR : size (drop j.+1 s) <= n.
  rewrite size_drop Hsw /=. exact: leq_subr.
have IHL := IH _ HszL HuL.
have IHR := IH _ HszR HuR.
case Hj0 : (0 < j).
  rewrite (phi_w_decomp_mm Hu Hsz2 Hj0).
  rewrite D_offsets_cat_D.
  rewrite (S_w_seq_decomp_mm Hu Hsz2 Hj0).
  rewrite IHL IHR.
  have HwL := cde_total_width_phi_w_all HuL.
  rewrite HwL size_takel; last exact: ltnW.
  congr (_ ++ _ :: _).
  apply: eq_map => x /=.
  by rewrite addnC addn2 prednK.
move: Hj0; rewrite lt0n => /negbFE /eqP Hj0.
rewrite (phi_w_cons_mm0 Hj0 Hsz2).
rewrite D_offsets_cons_C.
rewrite (S_w_seq_shift Hj0).
have HszR' : size rest <= n.
  by move: Hsz; rewrite /s /= ltnS.
have HuR' : uniq rest.
  by move: Hu; rewrite /s cons_uniq => /andP [].
by rewrite (IH rest HszR' HuR').
Qed.

(* ===== The main theorem ================================================= *)
(* phi_w_support_general:                                                    *)
(* X ∈ expand_cde(Φ_w) ⟺ S_w ⊆ ω(desc(X)) *)
(*                                                                           *)
(* Proof structure (all intermediate lemmas proved above):                   *)
(* 1. expand_cde_mem_iff: X ∈ expand_cde(m) ⟺ all D-offset transitions *)
(*    [PROVED by induction on the cd-word m]                                *)
(* 2. has_transition_omega_seq: bit transition ⟺ omega_seq membership      *)
(*    [PROVED using mem_filter_iota_nth and foldr_maxn_ge]                  *)
(* 3. S_w_seq_bound: S_w_seq elements < (size w).-2                        *)
(*    [PROVED using window_size_bound at the last position]                 *)
(* 4. cde_total_width_phi_w: total width of phi_w = (size w).-1            *)
(*    [PROVED by structural induction on size w with mm_pos decomposition]  *)
(* 5. D_offsets_phi_w_eq_S_w_seq: D-offsets match S_w_seq                  *)
(*    [PROVED by structural induction on size w with mm_pos decomposition]  *)

(** Headline support theorem: for uniq [w] with [size w >= 2] and any
    bit-string [X] of length [(size w).-1], [X] lies in [expand_cde (phi_w w)]
    iff every d-position of [w] (i.e. every element of [S_w_seq w]) belongs
    to [omega_seq] of [X]'s descent set.  This is Stanley's support claim
    [Phi_w(a+b, ab+ba) = sum_{omega(X) supseteq S_w} u_X], the key
    ingredient feeding into [omega_proper_beta_lt] and Prop 1.6.4.
    Proof composes [expand_cde_mem_iff], [D_offsets_phi_w_eq_S_w_seq] and
    [has_transition_omega_seq]. *)
Lemma phi_w_support_general (w : seq nat) (X : seq bool) :
  uniq w -> 2 <= size w -> size X = (size w).-1 ->
  (X \in expand_cde (phi_w w)) =
  all (fun k => k \in omega_seq [seq i <- iota 0 (size w).-1 | nth false X i])
      (S_w_seq w).
Proof.
move=> Hu Hsz2 HszX.
have Hwidth := cde_total_width_phi_w Hu Hsz2.
have HszX2 : size X = cde_total_width (phi_w w) by rewrite Hwidth.
rewrite (expand_cde_mem_iff HszX2).
rewrite /all_D_transitions (D_offsets_phi_w_eq_S_w_seq Hu Hsz2).
apply/allP/allP.
- move=> Hall k Hk.
  have Hkb := S_w_seq_bound Hk.
  rewrite -(has_transition_omega_seq X Hkb).
  exact: Hall Hk.
- move=> Hall k Hk.
  have Hkb := S_w_seq_bound Hk.
  rewrite (has_transition_omega_seq X Hkb).
  exact: Hall Hk.
Qed.

(* ========================================================================= *)
(* §M5bis. Structural proof of check_fact3_true (Theorem 1.6.3)             *)
(*                                                                           *)
(* The proof avoids heavy simpl/vm_compute that causes OOM during -vo.       *)
(* Strategy: show perm_eq between char_monos and expand_cde via              *)
(* membership (using phi_w_support_general) + injectivity.                   *)
(* ========================================================================= *)

(** [expand_cde m] enumerates each cd-monomial expansion exactly once. *)
Lemma uniq_expand_cde m : uniq (expand_cde m).
Proof.
elim: m => [|[||] l IH] //=.
- rewrite cat_uniq !map_inj_uniq // ?IH ?andbT;
    try by move=> a b [].
  apply/hasPn => x /mapP [y Hy ->].
  apply/negP => /mapP [z Hz]. by case.
- rewrite cat_uniq !map_inj_uniq //; try by move=> a b [].
  rewrite ?IH ?andbT.
  apply/hasPn => x /mapP [y Hy ->].
  apply/negP => /mapP [z Hz]. by case.
Qed.

(** Two uniq sequences of the same size with one a subset of the other
    are permutations of each other. *)
Lemma perm_eq_from_subset (T : eqType) (s1 s2 : seq T) :
  uniq s1 -> uniq s2 -> size s1 = size s2 ->
  {subset s1 <= s2} -> perm_eq s1 s2.
Proof.
move=> Hu1 Hu2 Hsz Hsub.
suff Hmem : forall x, x \in s1 = (x \in s2).
  by apply: uniq_perm.
move=> x; apply/idP/idP; first exact: Hsub.
move=> Hx2; apply/negPn/negP => Hx1.
have : size (x :: s1) <= size s2.
  apply: uniq_leq_size.
    by rewrite /= Hx1.
  move=> y; rewrite in_cons => /orP [/eqP -> | /Hsub] //.
by rewrite /= Hsz ltnn.
Qed.

(** [perm_eq] of the M-class char_monos with [expand_cde (phi_w w)]
    implies the boolean Fact #3 statement. *)
Lemma check_fact3_of_perm_eq w :
  perm_eq [seq char_mono (apply_psis ss w) | ss <- powerset_internal w]
          (expand_cde (phi_w w)) ->
  check_fact3 w.
Proof.
move=> Hp; rewrite /check_fact3.
by rewrite (sort_perm_eq_leq_seqb Hp) eqxx.
Qed.

(* -- D-type vertex descent transition ------------------------------------ *)

(** At a D-vertex (LR-internal, [has_left_child i w]), the descent bits
    at [i.-1] and [i] always differ -- the LR-swap behaviour of [psi]. *)
Lemma D_vertex_descent_transition w i :
  uniq w -> 0 < i -> is_internal i w -> has_left_child i w ->
  is_descent_seq w i.-1 != is_descent_seq w i.
Proof.
move=> Hu Hi0 Hint Hlc.
have Hws : 1 < window_size i w
  by move: Hint; rewrite /is_internal => /andP [_ ->].
have Hxor := exactly_one_descent_LR Hu Hi0 Hlc Hws.
move: Hxor; case: (is_descent_seq w i.-1);
  by case: (is_descent_seq w i).
Qed.

(* -- Self-support: char_mono w is in expand_cde (phi_w w) ----------------- *)

(** Self-support: [char_mono w] is itself a member of [expand_cde (phi_w w)],
    using [phi_w_support_general] applied to [X = char_mono w]. *)
Lemma char_mono_self_mem w :
  uniq w -> 2 <= size w ->
  char_mono w \in expand_cde (phi_w w).
Proof.
move=> Hu Hsz2.
have Hszx : size (char_mono w) = (size w).-1 by rewrite size_char_mono.
rewrite (phi_w_support_general Hu Hsz2 Hszx).
apply/allP => k Hk.
have Hkb := S_w_seq_bound Hk.
rewrite -(has_transition_omega_seq (char_mono w) Hkb).
rewrite /has_transition.
move: Hk; rewrite /S_w_seq => /mapP [i].
rewrite mem_filter => /andP [Hid Hiota] Hkeq.
rewrite mem_iota /= in Hiota.
have Hi_pos : 0 < i by move: Hiota => /andP [].
have Hi_lt : i < size w.
  move: Hiota => /andP [_ Hi].
  by rewrite add1n (prednK (ltn_trans _ Hsz2)) in Hi.
have Hint : is_internal i w.
  move: Hid; rewrite /classify_vertex_cde.
  by case: (is_internal i w) => //=.
have Hlc : has_left_child i w.
  move: Hid; rewrite /classify_vertex_cde.
  case: (is_internal i w) => //=.
  by case: (has_left_child i w).
have Htrans := D_vertex_descent_transition Hu Hi_pos Hint Hlc.
have Hk_lt : k < (size w).-1.
  rewrite Hkeq -ltnS (prednK Hi_pos).
  by case: (size w) Hsz2 Hi_lt => [//|[//|m]].
have Hk1_lt : k.+1 < (size w).-1.
  have Hpred_pos : 0 < (size w).-1
    by case: (size w) Hsz2 => [|[|m]].
  by rewrite -[in X in _ < X](prednK Hpred_pos) ltnS.
rewrite (nth_char_mono Hk_lt) (nth_char_mono Hk1_lt).
by rewrite Hkeq prednK.
Qed.

(* -- Membership: all M-class char_monos are in expand_cde ----------------- *)

(** Membership: every M-class element has its [char_mono] inside
    [expand_cde (phi_w w)], by combining [phi_w_apply_psis] and
    [char_mono_self_mem]. *)
Lemma char_mono_apply_psis_mem w ss :
  uniq w -> 2 <= size w ->
  char_mono (apply_psis ss w) \in expand_cde (phi_w w).
Proof.
move=> Hu Hsz2.
rewrite -(phi_w_apply_psis ss Hu).
apply: char_mono_self_mem.
  exact: uniq_apply_psis.
by rewrite size_apply_psis.
Qed.

(* -- Injectivity: distinct subsets give distinct char_monos --------------- *)

(** Membership in [internal_vertices] is exactly [is_internal]. *)
Lemma in_internal_vertices i w :
  (i \in internal_vertices w) = is_internal i w.
Proof.
rewrite /internal_vertices mem_filter.
case Hi: (is_internal i w) => /=; last by [].
rewrite mem_iota /=.
by move: Hi => /andP [-> _].
Qed.

(** Injectivity: distinct subsets of internal vertices give distinct
    [char_mono (apply_psis ss w)].  Proof recovers the membership bit at
    each internal vertex from the char_mono via [_C_bit] / [_D_bit_self]
    + [D_vertex_descent_transition]. *)
Lemma char_mono_apply_psis_inj w ss1 ss2 :
  uniq w ->
  ss1 \in powerset_internal w ->
  ss2 \in powerset_internal w ->
  char_mono (apply_psis ss1 w) = char_mono (apply_psis ss2 w) ->
  ss1 = ss2.
Proof.
move=> Hu Hss1 Hss2 Heq.
have Hivs_uniq : uniq (internal_vertices w).
  by rewrite /internal_vertices filter_uniq // iota_uniq.
have Hsub1 : subseq ss1 (internal_vertices w) := subseq_powerset_internal Hss1.
have Hsub2 : subseq ss2 (internal_vertices w) := subseq_powerset_internal Hss2.
have Hu1 : uniq ss1 := subseq_uniq Hsub1 Hivs_uniq.
have Hu2 : uniq ss2 := subseq_uniq Hsub2 Hivs_uniq.
have Hint1 : forall i, i \in ss1 -> is_internal i w.
  by move=> i Hi; rewrite -in_internal_vertices; exact: (mem_subseq Hsub1).
have Hint2 : forall i, i \in ss2 -> is_internal i w.
  by move=> i Hi; rewrite -in_internal_vertices; exact: (mem_subseq Hsub2).
(* Step 1: equal char_monos ⟹ same membership for every internal vertex.    *)
have Hmem : ss1 =i ss2.
  move=> x.
  case Hin: (x \in internal_vertices w); last first.
    have HF1 : (x \in ss1) = false.
      apply/negP => Hx.
      by have := mem_subseq Hsub1 Hx; rewrite Hin.
    have HF2 : (x \in ss2) = false.
      apply/negP => Hx.
      by have := mem_subseq Hsub2 Hx; rewrite Hin.
    by rewrite HF1 HF2.
  rewrite in_internal_vertices in Hin.
  have Hbit : forall k, k < (size w).-1 ->
    nth false (char_mono (apply_psis ss1 w)) k =
    nth false (char_mono (apply_psis ss2 w)) k by move=> k Hk; rewrite Heq.
  case Hlc: (has_left_child x w).
  - (* D-vertex: use self bit + transition to recover (x \in ss). *)
    have Hxlt := is_internal_lt Hin.
    have Hxpos : 0 < x.
      case Hx0: x Hlc => [|n] //=.
      by rewrite has_left_child_0.
    have H1 := char_mono_apply_psis_D_bit_self Hu Hu1 Hint1 Hin Hlc.
    have H2 := char_mono_apply_psis_D_bit_self Hu Hu2 Hint2 Hin Hlc.
    have Hxx := Hbit _ Hxlt.
    rewrite H1 H2 in Hxx.
    have Hdiff := D_vertex_descent_transition Hu Hxpos Hin Hlc.
    case E1: (x \in ss1); case E2: (x \in ss2) => //.
    + rewrite E1 E2 /= in Hxx.
      by rewrite Hxx eqxx in Hdiff.
    + rewrite E1 E2 /= in Hxx.
      by rewrite -Hxx eqxx in Hdiff.
  - (* C-vertex: use C-bit lemma; xor-cancel. *)
    have Hcv : ~~ has_left_child x w by rewrite Hlc.
    have Hxlt := is_internal_lt Hin.
    have H1 := char_mono_apply_psis_C_bit Hu Hu1 Hint1 Hin Hcv.
    have H2 := char_mono_apply_psis_C_bit Hu Hu2 Hint2 Hin Hcv.
    have Hxx := Hbit _ Hxlt.
    rewrite H1 H2 in Hxx.
    by move: Hxx; case: (is_descent_seq w x);
      case: (x \in ss1); case: (x \in ss2).
(* Step 2: same membership + both subseqs of uniq base ⟹ equal sequences.   *)
have Eq1 : ss1 = [seq x <- internal_vertices w | x \in ss1].
  exact: (elimT (subseq_uniqP Hivs_uniq) Hsub1).
have Eq2 : ss2 = [seq x <- internal_vertices w | x \in ss2].
  exact: (elimT (subseq_uniqP Hivs_uniq) Hsub2).
rewrite Eq1 Eq2.
by apply: eq_in_filter => x _; exact: Hmem.
Qed.

(** The list of M-class char_monos (indexed by [powerset_internal w]) is
    duplicate-free, by [char_mono_apply_psis_inj]. *)
Lemma uniq_map_char_mono_powerset w :
  uniq w -> 2 <= size w ->
  uniq [seq char_mono (apply_psis ss w) | ss <- powerset_internal w].
Proof.
move=> Hu _.
rewrite map_inj_in_uniq; first exact: uniq_powerset_internal.
move=> ss1 ss2 Hss1 Hss2 Heq.
exact: char_mono_apply_psis_inj Hu Hss1 Hss2 Heq.
Qed.

(* -- check_fact3_true: structural proof ----------------------------------- *)

(** Boolean Fact #3 holds for every uniq [w]: combines uniq + same-size +
    membership to derive [perm_eq], then the sorted equality. *)
Lemma check_fact3_true w :
  uniq w -> check_fact3 w.
Proof.
move=> Hu.
case Hsz : (size w <= 1).
  exact: check_fact3_size1.
have Hsz2 : 2 <= size w
  by case: (size w) Hsz => [|[|m]].
apply: check_fact3_of_perm_eq.
apply: perm_eq_from_subset.
- exact: uniq_map_char_mono_powerset.
- exact: uniq_expand_cde.
- by rewrite size_map size_powerset_internal -size_expand_cde_phi_w.
- move=> x /mapP [ss _ ->].
  exact: char_mono_apply_psis_mem.
Qed.

(** Headline Fact #3 (Stanley EC1 §1.6.3, Theorem 1.6.3): the multiset of
    char_monos over the M-class of [w], canonicalised by [sort leq_seqb],
    equals the canonicalised expansion [expand_cde (phi_w w)].  Direct
    consequence of [check_fact3_true] via [check_fact3P]. *)
Lemma fact3 : forall (w : seq nat),
  uniq w ->
  sort leq_seqb
    [seq char_mono (apply_psis ss w)
    | ss <- powerset_internal w]
  =
  sort leq_seqb (expand_cde (phi_w w)).
Proof.
move=> w Hu.
by apply/check_fact3P; apply: check_fact3_true.
Qed.

(* ----- Fact3 examples (vm_compute on small instances) -------------------- *)

Example fact3_ex_315426 :
  let w := [:: 3; 1; 5; 4; 2; 6] in
  sort leq_seqb [seq char_mono (apply_psis ss w) | ss <- powerset_internal w]
  = sort leq_seqb (expand_cde (phi_w w)).
Proof. by vm_compute. Qed.

Example fact3_ex_213 :
  let w := [:: 2; 1; 3] in
  sort leq_seqb [seq char_mono (apply_psis ss w) | ss <- powerset_internal w]
  = sort leq_seqb (expand_cde (phi_w w)).
Proof. by vm_compute. Qed.
