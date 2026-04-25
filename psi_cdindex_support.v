(* psi_cdindex_support.v — phi_w_support_general and structural helpers      *)
(*                                                                           *)
(* Split from psi_cdindex.v to reduce -vo compilation memory.                *)
(* Contains: cde_width/D_offsets infrastructure, expand_cde membership       *)
(* characterization, S_w_seq_bound, cde_total_width_phi_w,                   *)
(* D_offsets_phi_w_eq_S_w_seq, and phi_w_support_general.                    *)

From mathcomp Require Import all_ssreflect.
Require Import mmtree psi_core psi_comm psi_descent_v2 psi_descent_thms.
Require Import psi_cdindex_core psi_cdindex_witness.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* ========================================================================= *)
(* ===== M6.8: phi_w_support_general ======================================= *)
(* X ∈ expand_cde(Φ_w) ⟺ S_w ⊆ ω(desc(X))                               *)
(* ========================================================================= *)

(* -- D-offsets: cumulative bit-offset of each letter in a cd-word --------- *)
(* C contributes 1 bit, D contributes 2 bits, E contributes 0 bits.         *)

Definition cde_width (l : cde) : nat :=
  match l with C_letter => 1 | D_letter => 2 | E_letter => 0 end.

Definition cde_total_width (m : seq cde) : nat :=
  sumn [seq cde_width l | l <- m].

Definition cde_offset (m : seq cde) (i : nat) : nat :=
  sumn [seq cde_width l | l <- take i m].

Definition D_offsets (m : seq cde) : seq nat :=
  [seq cde_offset m i | i <- iota 0 (size m)
                       & is_D_letter (nth C_letter m i)].

Definition has_transition (X : seq bool) (k : nat) : bool :=
  nth false X k != nth false X k.+1.

Definition all_D_transitions (m : seq cde) (X : seq bool) : bool :=
  all (fun k => has_transition X k) (D_offsets m).

(* -- Helper: size of elements in expand_cde ------------------------------- *)
Lemma size_in_expand_cde m X :
  X \in expand_cde m -> size X = cde_total_width m.
Proof.
elim: m X => [|[||] m IH] X /=.
- by rewrite mem_seq1 => /eqP ->.
- rewrite mem_cat => /orP [Hm|Hm];
    move: Hm; rewrite mem_map; try (by move=> a b []);
    move=> /mapP [t Ht ->] /=; by rewrite (IH t Ht).
- rewrite mem_cat => /orP [Hm|Hm];
    move: Hm; rewrite mem_map; try (by move=> a b []);
    move=> /mapP [t Ht ->] /=; by rewrite (IH t Ht).
- exact: IH.
Qed.

(* -- Core: expand_cde membership as D-transition condition ---------------- *)
(* Forward: membership implies transitions at all D-offsets.                *)

Lemma expand_cde_mem_transitions m X :
  X \in expand_cde m -> all_D_transitions m X.
Proof.
elim: m X => [|[||] m IH] X //=.
- (* C_letter *)
  rewrite mem_cat => /orP [Hm|Hm];
    move: Hm; rewrite mem_map; try (by move=> a b []);
    move=> /mapP [t Ht ->];
    rewrite /all_D_transitions /D_offsets /=;
    apply/allP => k;
    rewrite mem_map; try (by move=> a b; rewrite /cde_offset /= !add0n => []);
    move=> /mapP [j]; rewrite mem_filter => /andP [Hd Hj] ->;
    rewrite /has_transition /cde_offset /=;
    move: (IH t Ht);
    rewrite /all_D_transitions /D_offsets;
    move/allP => Hall; apply: Hall;
    apply/mapP; exists j; by [|rewrite mem_filter Hd].
- (* D_letter *)
  rewrite mem_cat => /orP [Hm|Hm];
    move: Hm; rewrite mem_map; try (by move=> a b []);
    move=> /mapP [t Ht ->];
    rewrite /all_D_transitions /D_offsets /=;
    apply/allP => k; rewrite inE;
    move=> /orP [/eqP -> | Hrest];
      try by rewrite /has_transition /=;
    move: Hrest;
    rewrite mem_map; try (by move=> a b; rewrite /cde_offset /= !add0n => []);
    move=> /mapP [j]; rewrite mem_filter => /andP [Hd Hj] ->;
    rewrite /has_transition /cde_offset /=;
    move: (IH t Ht);
    rewrite /all_D_transitions /D_offsets;
    move/allP => Hall; apply: Hall;
    apply/mapP; exists j; by [|rewrite mem_filter Hd].
- (* E_letter *)
  exact: IH.
Qed.

(* Backward: correct size + transitions at D-offsets implies membership.    *)

Lemma transitions_expand_cde_mem m X :
  size X = cde_total_width m ->
  all_D_transitions m X ->
  X \in expand_cde m.
Proof.
elim: m X => [|[||] m IH] X /=.
- by move=> /size0nil ->.
- (* C_letter *)
  case: X => [// | b X] /= [HszX] Hall.
  rewrite mem_cat; apply/orP.
  have HallT : all_D_transitions m X.
    rewrite /all_D_transitions /D_offsets.
    apply/allP => k /mapP [j Hj ->].
    move: Hall; rewrite /all_D_transitions /D_offsets /=.
    move/allP => Hall2.
    have Hin : cde_offset (C_letter :: m) j.+1 \in
      [seq cde_offset (C_letter :: m) i
      | i <- iota 0 (size m).+1
      & is_D_letter (nth C_letter (C_letter :: m) i)].
      apply/mapP; exists j.+1 => //.
      move: Hj; rewrite !mem_filter => /andP [Hd Hj2].
      rewrite /= Hd /=.
      by move: Hj2; rewrite !mem_iota /= !add0n ltnS.
    move: (Hall2 _ Hin).
    by rewrite /has_transition /cde_offset /=.
  case: b; [right|left]; apply/mapP; exists X => //; exact: IH.
- (* D_letter *)
  case: X => [// | b1 [// | b2 X]] /= [HszX] Hall.
  rewrite mem_cat; apply/orP.
  have Htrans : b1 != b2.
    move: Hall; rewrite /all_D_transitions /D_offsets /=.
    move/allP => Hall2.
    have : (0 : nat) \in
      (0 :: [seq cde_offset (D_letter :: m) i
            | i <- iota 1 (size m)
            & is_D_letter (nth C_letter (D_letter :: m) i)]).
      by rewrite inE eqxx.
    move=> Hin; move: (Hall2 _ Hin).
    by rewrite /has_transition /=.
  have HallT : all_D_transitions m X.
    rewrite /all_D_transitions /D_offsets.
    apply/allP => k /mapP [j Hj ->].
    move: Hall; rewrite /all_D_transitions /D_offsets /=.
    move/allP => Hall2.
    have Hin : cde_offset (D_letter :: m) j.+1 \in
      (0 :: [seq cde_offset (D_letter :: m) i
            | i <- iota 1 (size m)
            & is_D_letter (nth C_letter (D_letter :: m) i)]).
      rewrite inE; apply/orP; right.
      apply/mapP; exists j.+1 => //.
      move: Hj; rewrite !mem_filter => /andP [Hd Hj2].
      rewrite /= Hd /=.
      by move: Hj2; rewrite !mem_iota /= !add0n addn1 ltnS.
    move: (Hall2 _ Hin).
    by rewrite /has_transition /cde_offset /=.
  case: b1 Htrans => /=; case: b2 => //= _.
  + left; apply/mapP; exists X => //; exact: IH.
  + right; apply/mapP; exists X => //; exact: IH.
- (* E_letter *)
  move=> HszX Hall; apply: IH => //.
  move: Hall; rewrite /all_D_transitions /D_offsets /=.
  move/allP => Hall2.
  rewrite /all_D_transitions /D_offsets.
  apply/allP => k /mapP [j Hj ->].
  have Hin : cde_offset (E_letter :: m) j.+1 \in
    [seq cde_offset (E_letter :: m) i
    | i <- iota 0 (size m).+1
    & is_D_letter (nth C_letter (E_letter :: m) i)].
    apply/mapP; exists j.+1 => //.
    move: Hj; rewrite !mem_filter => /andP [Hd Hj2].
    rewrite /= Hd /=.
    by move: Hj2; rewrite !mem_iota /= !add0n ltnS.
  move: (Hall2 _ Hin).
  by rewrite /has_transition /cde_offset /=.
Qed.

(* Combined: X ∈ expand_cde(m) iff all D-offset transitions hold. *)
Lemma expand_cde_mem_iff m X :
  size X = cde_total_width m ->
  (X \in expand_cde m) = all_D_transitions m X.
Proof.
move=> Hsz; apply/idP/idP.
- exact: expand_cde_mem_transitions.
- exact: transitions_expand_cde_mem Hsz.
Qed.

(* -- has_transition = omega_seq membership -------------------------------- *)
(* k ∈ omega_seq(desc(X)) iff nth false X k ≠ nth false X (k+1),           *)
(* where desc(X) = {i < m : X[i] = true}.                                  *)

Lemma mem_filter_iota_nth (X : seq bool) m i :
  i < m ->
  (i \in [seq j <- iota 0 m | nth false X j]) = nth false X i.
Proof.
move=> Hi.
rewrite mem_filter mem_iota add0n Hi andbT /=.
by case: (nth false X i).
Qed.

Lemma foldr_maxn_ge (s : seq nat) x : x \in s -> x <= foldr maxn 0 s.
Proof.
elim: s => [//|a s IH].
rewrite inE => /orP [/eqP -> | Hin].
- by rewrite /= leq_maxl.
- by rewrite /=; apply: leq_trans (IH Hin) _; exact: leq_maxr.
Qed.

Lemma mem_omega_seq (s : seq nat) k :
  k \in omega_seq s =
  ((k \in s) != (k.+1 \in s)) && (k < (foldr maxn 0 s).+1).
Proof. by rewrite /omega_seq mem_filter mem_iota add0n. Qed.

Lemma has_transition_omega_seq X m k :
  k < m.-1 ->
  has_transition X k =
  (k \in omega_seq [seq i <- iota 0 m | nth false X i]).
Proof.
move=> Hk.
have Hk2 : k.+1 < m.
  by rewrite -[m](@prednK m) ?ltnS //; case: m Hk.
have Hk1 : k < m by exact: ltnW.
set desc := [seq i <- iota 0 m | nth false X i].
rewrite /has_transition mem_omega_seq.
have -> : (k \in desc) = nth false X k.
  by rewrite /desc mem_filter_iota_nth.
have -> : (k.+1 \in desc) = nth false X k.+1.
  by rewrite /desc mem_filter_iota_nth.
suff Hbound : (nth false X k != nth false X k.+1) ->
  k < (foldr maxn 0 desc).+1.
  case: (nth false X k != nth false X k.+1) (Hbound) => //= Hb.
  by rewrite Hb.
move=> Hneq.
move: Hneq.
case Hxk : (nth false X k); case Hxk1 : (nth false X k.+1) => //= _.
- have Hkin : k \in desc
    by rewrite /desc mem_filter mem_iota add0n Hk1 Hxk.
  by apply: (leq_ltn_trans (foldr_maxn_ge Hkin)); exact: ltnSn.
- have Hkin : k.+1 \in desc
    by rewrite /desc mem_filter mem_iota add0n Hk2 Hxk1.
  apply: (leq_ltn_trans _ (ltnSn _)).
  by apply: (leq_trans (leqnSn k)); exact: foldr_maxn_ge.
Qed.

(* -- S_w_seq elements are bounded: k ∈ S_w_seq w → k < (size w).-2 ------- *)
(* S_w_seq w = [seq i.-1 | i <- iota 1 (size w).-1                         *)
(*                        & is_D_letter (classify_vertex_cde i w)].          *)
(* Since i ∈ iota 1 (size w).-1, i ranges from 1 to (size w).-1.            *)
(* The last position (size w).-1 is always an endpoint (leaf in the          *)
(* min-max tree), so is_D_letter there is false.                             *)
(* Hence max i in the filter is (size w).-2, giving k = i.-1 ≤ (size w).-3. *)
(* Thus k < (size w).-2 = (size w).-1.-1.                                   *)

Lemma S_w_seq_bound w k :
  k \in S_w_seq w -> k < (size w).-1.-1.
Proof.
rewrite /S_w_seq.
move=> /mapP [i].
rewrite mem_filter => /andP [Hd Hi] ->.
move: Hi; rewrite mem_iota => /andP [Hi1 Hi2].
(* Need: i.-1 < (size w).-1.-1, i.e., i < (size w).-1 *)
suff Hlt : i < (size w).-1.
  by case: i Hi1 Hlt => [//|i] _ /=; rewrite ltnS.
rewrite ltn_neqAle.
have Hle : i <= (size w).-1.
  by rewrite -ltnS; case: (size w) Hi2 => [|n] //=.
rewrite Hle andbT.
apply/negP => /eqP Heqi.
(* i = (size w).-1: the last position is always an endpoint *)
move: Hd; rewrite Heqi /is_D_letter /classify_vertex_cde.
(* is_internal (size w).-1 w = false because window_size = 1 *)
have Hws1 : window_size (size w).-1 w <= 1.
  have := window_size_bound (size w).-1 w.
  by case: (size w) Hi2 => [|[|n]] //=; rewrite subSS subn0.
have Hnint : is_internal (size w).-1 w = false.
  rewrite /is_internal.
  case Hlt : ((size w).-1 < size w) => //=.
  by rewrite ltnNge Hws1.
by rewrite Hnint.
Qed.

(* -- S_w_seq is psi-invariant --------------------------------------------- *)
Lemma classify_vertex_cde_psi j i w :
  uniq w ->
  classify_vertex_cde i (psi j w) = classify_vertex_cde i w.
Proof.
move=> Hu.
rewrite /classify_vertex_cde.
by rewrite (is_internal_apply_psis [:: j]) //
           (has_left_child_apply_psis [:: j]).
Qed.

Lemma S_w_seq_psi j w :
  uniq w -> S_w_seq (psi j w) = S_w_seq w.
Proof.
move=> Hu.
rewrite /S_w_seq size_psi.
congr map; congr filter.
apply: eq_in_filter => i _.
exact: classify_vertex_cde_psi.
Qed.

(* -- Structural helpers for cde_total_width and D_offsets --------------- *)
(* These provide explicit decomposition lemmas for phi_w, D_offsets, and  *)
(* S_w_seq at mm_pos, producing small proof terms that avoid heavy        *)
(* simpl/vm_compute during -vo compilation.                               *)

Lemma cde_total_width_cat s1 s2 :
  cde_total_width (s1 ++ s2) =
  cde_total_width s1 + cde_total_width s2.
Proof. by rewrite /cde_total_width map_cat sumn_cat. Qed.

(* mm_pos < (size s).-1 for uniq sequences of size >= 2. *)
(* This ensures the root of the min-max tree is internal. *)
Lemma mm_pos_lt_pred (s : seq nat) :
  uniq s -> 1 < size s -> mm_pos s < (size s).-1.
Proof.
case: s => [//|a s0] Hu Hsz.
set s := a :: s0. set j := mm_pos s.
have Hne : s <> [::] by [].
have Hj : j < size s := mm_pos_lt Hne.
apply/negP => /negP; rewrite -leqNgt => Hle.
have Heq : j = (size s).-1
  by apply/eqP; rewrite eqn_leq Hle -ltnS prednK //
     (leq_trans _ Hsz).
have Hdrop_sz : size (drop j s) = 1
  by rewrite size_drop Heq;
     case: (size s) Hsz => [|[|n]].
have [Hno_min Hno_max] := notin_take_mm Hne.
have Hmin_drop :
  foldr minn (head 0 s) (behead s) \in drop j s.
  have := min_in s.
  by rewrite -(cat_take_drop j s) mem_cat =>
     /orP [/(negP Hno_min)//|].
have Hmax_drop :
  foldr maxn (head 0 s) (behead s) \in drop j s.
  have := max_in s.
  by rewrite -(cat_take_drop j s) mem_cat =>
     /orP [/(negP Hno_max)//|].
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
  have := foldr_minn_le Hy;
  have := foldr_maxn_ge Hy.
  rewrite Hmin_x Hmax_x => H2 H1.
  by apply/eqP; rewrite eqn_leq H1 H2.
move: Hu; rewrite /s /= => /andP [Hnotin _].
have := Hall_eq a (mem_head a s0).
have : head 0 s0 \in s.
  case: s0 Hsz Hnotin => [//|b t] /= _ _.
  by rewrite /s /= !inE eqxx orbT.
move=> Hb Ha_eq; have := Hall_eq _ Hb.
rewrite Ha_eq => Hh_eq.
case: s0 Hsz Hnotin => [//|b t] /= _ Hnotin.
by rewrite Ha_eq Hh_eq inE eqxx in Hnotin.
Qed.

(* classify_vertex_cde decomposition at mm_pos *)
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
by rewrite size_takel // ltnW // Hij.
Qed.

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
rewrite size_drop.
case: i Hji => [//|i] /= Hji.
rewrite subSS subn0.
by rewrite ltn_sub2r // ltnS.
Qed.

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
have Hjp : j < (size s).-1
  := mm_pos_lt_pred Hu Hsz.
rewrite /classify_vertex_cde /is_internal.
rewrite (window_size_cons j a s0) -/s -/j
  ltnn eqxx.
have -> : j < size s = true by [].
have -> : 1 < size s - j = true
  by rewrite ltn_subRL addnC /= ltnS.
rewrite /=.
rewrite (has_left_child_cons j a s0) -/s -/j
  ltnn eqxx.
by case: (0 < j).
Qed.

(* phi_w cons decomposition when mm_pos = 0 *)
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
have -> : 0 < size (a :: rest) = true by [].
have -> : 1 < size (a :: rest) = true by [].
rewrite /= has_left_child_0 /=.
congr cons; congr (filter _).
apply: (@eq_from_nth _ E_letter).
  by rewrite !size_map !size_iota.
move=> k Hk.
rewrite size_map size_iota in Hk.
rewrite !(nth_map 0) ?size_iota //.
rewrite !nth_iota // add0n.
exact: classify_skip_mm0 Hmm (ltn0Sn k).
Qed.

(* phi_w decomposition when mm_pos > 0 *)
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
  iota 0 j ++ j :: iota j.+1 (size s - j.+1)
  by rewrite -cat1s catA -iota_add addnC subnK //
     ltnW.
rewrite Hiota_split !map_cat /= !filter_cat /=.
rewrite (classify_vertex_mm Hu Hsz) Hj0 /=.
congr (_ ++ _ :: _).
- congr (filter _ _).
  apply: eq_in_map => i.
  rewrite mem_iota add0n => /andP [_ Hi].
  exact: classify_vertex_left Hi.
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
  by rewrite addSn /= addnK.
Qed.

(* D_offsets decomposition: C_letter :: m *)
Lemma D_offsets_cons_C m :
  D_offsets (C_letter :: m) =
  [seq x.+1 | x <- D_offsets m].
Proof.
rewrite /D_offsets /=.
rewrite -map_comp.
transitivity
  [seq (cde_offset m i).+1
  | i <- [seq i <- iota 0 (size m)
  | is_D_letter (nth C_letter m i)]]; last done.
congr map.
- apply: eq_in_filter => i.
  rewrite mem_iota add0n => /andP [_ Hi].
  by rewrite /= nth_cat /= Hi.
- apply: funext => i.
  by rewrite /cde_offset /= /cde_width add1n.
Qed.

(* D_offsets decomposition: m1 ++ D_letter :: m2 *)
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
rewrite Hsz iota_add add0n filter_cat map_cat.
have Hleft :
  [seq cde_offset (m1 ++ D_letter :: m2) i
  | i <- [seq i <- iota 0 (size m1)
  | is_D_letter
      (nth C_letter
        (m1 ++ D_letter :: m2) i)]]
  = D_offsets m1.
  congr map; congr filter.
  - apply: eq_in_filter => i.
    rewrite mem_iota add0n => /andP [_ Hi].
    by rewrite nth_cat Hi.
  - apply: eq_in_map => i.
    rewrite mem_filter => /andP [_ Hi_iota].
    have Hi : i < size m1.
      by move: Hi_iota; rewrite mem_iota add0n
         => /andP [].
    by rewrite /cde_offset take_cat Hi.
rewrite Hleft [iota _ _]/=.
have Hmid_f : is_D_letter (nth C_letter
  (m1 ++ D_letter :: m2) (size m1)) = true
  by rewrite nth_cat ltnn subnn.
rewrite Hmid_f /=.
have Hmid_o : cde_offset (m1 ++ D_letter :: m2)
  (size m1) = cde_total_width m1.
  rewrite /cde_offset /cde_total_width.
  by rewrite take_cat ltnn subnn take0 cats0.
rewrite Hmid_o.
congr cons; rewrite -map_comp.
transitivity
  [seq cde_total_width m1 + 2 + x
  | x <- D_offsets m2]; last done.
rewrite /D_offsets -map_comp.
rewrite (eq_filter (a2 := fun i =>
  is_D_letter (nth C_letter m2 i))); last first.
  move=> k /=; rewrite nth_cat.
  have -> : (size m1 + k.+1 < size m1) = false
    by rewrite ltnNge leq_addr.
  by rewrite addnS addKn.
rewrite (eq_map (f2 := fun i =>
  cde_total_width m1 + 2 +
  cde_offset m2 i)); last first.
  move=> k /=.
  rewrite /cde_offset /cde_total_width take_cat.
  have -> : (size m1 + k.+1 < size m1) = false
    by rewrite ltnNge leq_addr.
  rewrite addnS addKn /= map_cat sumn_cat.
  by rewrite take_cat ltnn subnn take0 cats0
     addnA.
done.
Qed.

(* S_w_seq decomposition at mm_pos > 0 *)
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
  have Hj1 : 1 <= j by [].
  rewrite -{1}(subnK Hj1) iota_add addn1.
  rewrite -cat1s catA; congr (_ ++ _).
  rewrite -iota_add addSn addnC subnK //.
  by case: (size s) Hsz => [|[|n]].
rewrite Hsplit !filter_cat /= !map_cat /=.
have Hleft_filter : forall i,
  i \in iota 1 j.-1 ->
  is_D_letter (classify_vertex_cde i s) =
  is_D_letter (classify_vertex_cde i (take j s)).
  move=> i; rewrite mem_iota => /andP [_ Hij].
  by rewrite (classify_vertex_left
    (ltn_trans Hij (ltn_predK Hj0) : i < j)).
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
- rewrite -map_comp size_drop.
  rewrite -[iota j.+1 _]/(map (addn j.+1)
    (iota 0 _)).
  rewrite filter_map /= map_comp map_comp.
  rewrite (eq_filter (a2 := fun k =>
    is_D_letter (classify_vertex_cde k
      (drop j.+1 s)))); last first.
    by move=> k /=; rewrite addnS /= addnK.
  rewrite (eq_map (f2 := fun k => k + j));
    last first.
    by move=> k /=; rewrite addnS.
  rewrite /S_w_seq -map_comp.
  rewrite (eq_map (f2 := fun k => k + j));
    last first.
    by move=> k /=;
       rewrite -addnS subn1 -pred_Sn.
  congr map; rewrite size_drop.
  set n := (size s).-1 - j.
  rewrite -[n]/(size (drop j.+1 s)).
    2: by rewrite size_drop /n;
        case: (size s) Hsz => [|[|m]].
  rewrite [iota 0 _]/=.
  have -> : is_D_letter (classify_vertex_cde 0
    (drop j.+1 s)) = false.
    rewrite /classify_vertex_cde /is_internal.
    case E : (0 < size (drop j.+1 s)) => //=.
    case E2 : (1 < window_size 0 (drop j.+1 s))
      => //=.
    by rewrite has_left_child_0.
  by [].
Qed.

(* -- Total width of phi_w = (size w).-1 (structural) ------------------- *)
(* Proved by strong induction on size w with mm_pos decomposition.        *)
(* The mm_pos = 0 case uses phi_w_cons_mm0 (vertex 0 is C).              *)
(* The mm_pos > 0 case uses phi_w_decomp_mm (root is D) and IH for       *)
(* take j w and drop j.+1 w.                                              *)

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
    /mm_pos /min_pos /max_pos /=.
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
  rewrite cde_total_width_cat /=
    /cde_total_width /= -/cde_total_width.
  rewrite IHL IHR.
  rewrite size_takel; last exact: ltnW.
  rewrite size_drop.
  have HszR1 : 0 < size s - j.+1.
    rewrite subn_gt0.
    exact: mm_pos_lt_pred Hu Hsz2.
  rewrite prednK // -addnA addnC -addnA.
  rewrite [2 + _]addnC subnS prednK //.
  rewrite addnC -subnS.
  rewrite -[j in _ + (size s - j)]prednK //.
  rewrite subnS addnS addnC subnK //.
  exact: ltnW (ltnW (mm_pos_lt_pred Hu Hsz2)).
move: Hj0; rewrite lt0n negbK => /eqP Hj0.
rewrite (phi_w_cons_mm0 Hj0 Hsz2).
rewrite /= /cde_total_width /= -/cde_total_width.
have HszR' : size rest <= n.
  by move: Hsz; rewrite /s /= ltnS ltnNge Hszn.
have HuR' : uniq rest.
  by move: Hu; rewrite /s cons_uniq => /andP [].
rewrite (IH rest HszR' HuR').
by case: (size rest) Hsz2 => [|k] //.
Qed.

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
    /mm_pos /min_pos /max_pos /=.
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
  by rewrite addnC;
     case: j Hj0 => [//|j'] _ /=;
     rewrite addn2.
move: Hj0; rewrite lt0n negbK => /eqP Hj0.
rewrite (phi_w_cons_mm0 Hj0 Hsz2).
rewrite D_offsets_cons_C.
rewrite (S_w_seq_shift Hj0).
have HszR' : size rest <= n.
  by move: Hsz; rewrite /s /= ltnS ltnNge Hszn.
have HuR' : uniq rest.
  by move: Hu; rewrite /s cons_uniq => /andP [].
by rewrite (IH rest HszR' HuR').
Qed.

(* ===== The main theorem ================================================= *)
(* phi_w_support_general:                                                    *)
(* X ∈ expand_cde(Φ_w) ⟺ S_w ⊆ ω(desc(X))                               *)
(*                                                                           *)
(* Proof structure (all intermediate lemmas proved above):                   *)
(* 1. expand_cde_mem_iff: X ∈ expand_cde(m) ⟺ all D-offset transitions     *)
(*    [PROVED by induction on the cd-word m]                                *)
(* 2. has_transition_omega_seq: bit transition ⟺ omega_seq membership      *)
(*    [PROVED using mem_filter_iota_nth and foldr_maxn_ge]                  *)
(* 3. S_w_seq_bound: S_w_seq elements < (size w).-2                        *)
(*    [PROVED using window_size_bound at the last position]                 *)
(* 4. cde_total_width_phi_w: total width of phi_w = (size w).-1            *)
(*    [PROVED by structural induction on size w with mm_pos decomposition]  *)
(* 5. D_offsets_phi_w_eq_S_w_seq: D-offsets match S_w_seq                  *)
(*    [PROVED by structural induction on size w with mm_pos decomposition]  *)

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
  rewrite -(has_transition_omega_seq X (size w).-1 Hkb).
  exact: Hall Hk.
- move=> Hall k Hk.
  have Hkb := S_w_seq_bound Hk.
  rewrite (has_transition_omega_seq X (size w).-1 Hkb).
  exact: Hall Hk.
Qed.

(* ========================================================================= *)
(* §M5bis. Structural proof of check_fact3_true (Theorem 1.6.3)             *)
(*                                                                           *)
(* The proof avoids heavy simpl/vm_compute that causes OOM during -vo.       *)
(* Strategy: show perm_eq between char_monos and expand_cde via              *)
(* membership (using phi_w_support_general) + injectivity.                   *)
(* ========================================================================= *)

(* -- uniq of expand_cde -------------------------------------------------- *)
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

(* -- perm_eq from subset + same size + uniq ------------------------------- *)
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

(* -- check_fact3 from perm_eq --------------------------------------------- *)
Lemma check_fact3_of_perm_eq w :
  perm_eq [seq char_mono (apply_psis ss w) | ss <- powerset_internal w]
          (expand_cde (phi_w w)) ->
  check_fact3 w.
Proof.
move=> Hp; rewrite /check_fact3.
by rewrite (sort_perm_eq_leq_seqb Hp) eqxx.
Qed.

(* -- Root descent transition ---------------------------------------------- *)

Lemma foldr_minn_le_init s a : foldr minn a s <= a.
Proof.
by elim: s a => [//|b s IH] a /=;
  rewrite geq_min; apply/orP; right; exact: IH.
Qed.

Lemma foldr_minn_le_mem s a x : x \in s -> foldr minn a s <= x.
Proof.
elim: s a => [//|b s IH] a /=.
rewrite inE => /orP [/eqP -> | Hx].
  exact: geq_minl.
exact: leq_trans (geq_minr _ _) (IH _ Hx).
Qed.

Lemma foldr_minn_le_nth s k :
  k < size s -> foldr minn (head 0 s) (behead s) <= nth 0 s k.
Proof.
case: s => [//|a s0] /= Hk.
case: k Hk => [|k] Hk.
  exact: foldr_minn_le_init.
exact: foldr_minn_le_mem (mem_nth _ Hk).
Qed.

Lemma foldr_maxn_ge_init' s a : a <= foldr maxn a s.
Proof.
by elim: s a => [//|b s IH] a /=;
  rewrite leq_max; apply/orP; right; exact: IH.
Qed.

Lemma foldr_maxn_ge_mem' s a x : x \in s -> x <= foldr maxn a s.
Proof.
elim: s a => [//|b s IH] a /=.
rewrite inE => /orP [/eqP -> | Hx].
  exact: leq_maxl.
exact: leq_trans (IH _ Hx) (leq_maxr _ _).
Qed.

Lemma foldr_maxn_ge_nth' s k :
  k < size s -> nth 0 s k <= foldr maxn (head 0 s) (behead s).
Proof.
case: s => [//|a s0] /= Hk.
case: k Hk => [|k] Hk.
  exact: foldr_maxn_ge_init'.
exact: foldr_maxn_ge_mem' (mem_nth _ Hk).
Qed.

Lemma mm_pos_descent_neq (a : nat) (s0 : seq nat) :
  let s := a :: s0 in
  uniq s -> 1 < size s ->
  let j := mm_pos s in
  0 < j -> j < (size s).-1 ->
  is_descent_seq s j.-1 != is_descent_seq s j.
Proof.
move=> /= Hu Hsz.
set s := a :: s0; set j := mm_pos s.
move=> Hj0 Hjn.
have Hne : s <> [::] by [].
have Hj : j < size s := mm_pos_lt Hne.
have Hjpred : j.-1 < size s := leq_ltn_trans (leq_pred j) Hj.
have Hj1 : j.+1 < size s by rewrite ltnS; exact: Hjn.
have := nth_w_mm_pos Hne.
rewrite /is_descent_seq.
case.
- move=> Hmin.
  have Hlt1 : nth 0 s j < nth 0 s j.-1.
    rewrite ltn_neqAle; apply/andP; split; last first.
      by rewrite Hmin; exact: foldr_minn_le_nth.
    apply/eqP => Heq.
    by move: (nth_uniq 0 Hj Hjpred Hu); rewrite Heq eqxx /= gtn_eqF // prednK.
  have Hlt2 : nth 0 s j < nth 0 s j.+1.
    rewrite ltn_neqAle; apply/andP; split; last first.
      by rewrite Hmin; exact: foldr_minn_le_nth.
    apply/eqP => Heq.
    by move: (nth_uniq 0 Hj Hj1 Hu); rewrite Heq eqxx eqn_leq ltnn andbF.
  rewrite /is_descent_seq (prednK Hj0).
  by rewrite Hlt1 /= -leqNgt ltnW.
- move=> Hmax.
  have Hlt1 : nth 0 s j.-1 < nth 0 s j.
    rewrite ltn_neqAle; apply/andP; split; last first.
      by rewrite Hmax; exact: foldr_maxn_ge_nth'.
    apply/eqP => Heq.
    move: (nth_uniq 0 Hjpred Hj Hu); rewrite Heq eqxx /=.
    move/esym => Habs; suff : j.-1 <> j by rewrite (eqP Habs).
    by case: (j) Hj0.
  have Hlt2 : nth 0 s j.+1 < nth 0 s j.
    rewrite ltn_neqAle; apply/andP; split; last first.
      by rewrite Hmax; exact: foldr_maxn_ge_nth'.
    apply/eqP => Heq.
    by move: (nth_uniq 0 Hj1 Hj Hu); rewrite Heq eqxx eq_sym eqn_leq ltnn andbF.
  rewrite /is_descent_seq (prednK Hj0).
  by rewrite ltnNge (ltnW Hlt1) /= Hlt2.
Qed.

(* -- D-type vertex descent transition (recursive) ------------------------ *)

Lemma is_descent_seq_take w k j :
  k.+1 < j -> is_descent_seq (take j w) k = is_descent_seq w k.
Proof.
move=> Hk. rewrite /is_descent_seq.
by rewrite !nth_take // ltnW.
Qed.

Lemma is_descent_seq_drop w k j :
  j <= k -> k.+1 < size w ->
  is_descent_seq (drop j w) (k - j) = is_descent_seq w k.
Proof.
move=> Hjk Hk. rewrite /is_descent_seq !nth_drop.
congr (_ < _); congr (nth 0 w _);
  by rewrite ?addnS addnC subnK.
Qed.

Lemma D_vertex_descent_transition w i :
  uniq w -> 0 < i -> is_internal i w -> has_left_child i w ->
  is_descent_seq w i.-1 != is_descent_seq w i.
Proof.
move: w i.
suff Hgen : forall n w i, size w <= n ->
  uniq w -> 0 < i -> is_internal i w -> has_left_child i w ->
  is_descent_seq w i.-1 != is_descent_seq w i.
  by move=> w i; exact: Hgen (leqnn _).
elim => [|n IH] w i Hsz Hu Hi0 Hint Hlc.
  move: Hint; rewrite leqn0 in Hsz; move: (eqP Hsz) => /size0nil ->.
  by rewrite /is_internal.
case: w Hsz Hu Hi0 Hint Hlc => [//|a s0] Hsz Hu Hi0 Hint Hlc.
set s := a :: s0; set j := mm_pos s.
have Hne : s <> [::] by [].
have Hj : j < size s := mm_pos_lt Hne.
have His : i < size s
  by move: Hint; rewrite /is_internal => /andP [].
have Hws : 1 < window_size i s
  by move: Hint; rewrite /is_internal => /andP [_ ->].
rewrite (has_left_child_cons i a s0) -/s -/j in Hlc.
case: (ltngtP i j) => [Hij | Hji | Heq].
- have Hint_L : is_internal i (take j s).
    rewrite /is_internal size_takel ?ltnW //.
    rewrite (ltn_trans Hij Hj) /=.
    by rewrite (window_size_cons i a s0) -/s -/j Hij in Hws.
  have Hlc_L : has_left_child i (take j s) := Hlc.
  have Hi_lt_jpred : i < j.-1.
    rewrite -ltnS prednK //.
    rewrite ltn_neqAle Hij andbT.
    apply/negP => /eqP Heq_ij.
    have : has_left_child j.-1 (take j s) = false.
      apply: has_left_child_last.
      by rewrite size_takel ?ltnW // -Heq_ij.
    by rewrite -Heq_ij Hlc_L.
  have Hi1_lt_j : i.+1 < j := Hi_lt_jpred.
  rewrite -(is_descent_seq_take w i.-1 (leq_ltn_trans (leq_pred i) Hi1_lt_j)).
  rewrite -(is_descent_seq_take w i Hi1_lt_j).
  apply: IH => //.
  + rewrite size_takel; last exact: ltnW.
    exact: leq_trans (ltnW Hj) Hsz.
  + exact: take_uniq j Hu.
- have Hlc_R : has_left_child (i - j - 1) (drop j.+1 s) := Hlc.
  have Hint_R : is_internal (i - j - 1) (drop j.+1 s).
    rewrite /is_internal size_drop.
    have -> : (i - j - 1 < size s - j.+1) = (i < size s)
      by rewrite ltn_sub2r // ltn_sub2r // ltnS ltnW.
    rewrite His /=.
    by rewrite (window_size_cons i a s0) -/s -/j (ltnNge i j) (ltnW Hji) /=
              (negbTE (ltn_eqF Hji)) in Hws.
  have Hi_ge_j2 : j.+1 < i.
    rewrite ltnNge; apply/negP => Hle.
    have : i - j - 1 = 0 by
      rewrite -subn1 subnA //; apply/eqP;
      rewrite subn_eq0; exact: Hle.
    move=> Heq0.
    have : has_left_child 0 (drop j.+1 s) = false := has_left_child_0 _.
    by rewrite -Heq0 Hlc_R.
  have Hi0R : 0 < i - j - 1 by rewrite subn_gt0 ltn_sub2r.
  rewrite -(is_descent_seq_drop s i.-1 (n:=j.+1) _ _); last first.
      by rewrite -[i.-1.+1](prednK Hi0).
    by rewrite -ltnS (prednK Hi0).
  rewrite -(is_descent_seq_drop s i (n:=j.+1) _ _); last first.
      rewrite ltnS; apply: ltn_trans His.
      by case: (size s) => [//|k]; rewrite ltnS leqnn.
    exact: ltnW.
  have -> : i.-1 - j.+1 = (i - j - 1).-1
    by rewrite subn1 -subnS prednK.
  have -> : i - j.+1 = i - j - 1
    by rewrite subnS subn1.
  apply: IH => //.
  + rewrite size_drop. exact: leq_trans (leq_subr _ _) Hsz.
  + exact: drop_uniq j.+1 Hu.
- subst i.
  have Hj0 : 0 < j := Hi0.
  have Hjn : j < (size s).-1.
    apply: mm_pos_lt_pred => //.
    by case: (size s) Hj => [//|[//|k]] _.
  exact: mm_pos_descent_neq Hu _ Hj0 Hjn.
Qed.

(* -- Self-support: char_mono w is in expand_cde (phi_w w) ----------------- *)

Lemma char_mono_self_mem w :
  uniq w -> 2 <= size w ->
  char_mono w \in expand_cde (phi_w w).
Proof.
move=> Hu Hsz2.
have Hszx : size (char_mono w) = (size w).-1 by rewrite size_char_mono.
rewrite (phi_w_support_general Hu Hsz2 Hszx).
apply/allP => k Hk.
have Hkb := S_w_seq_bound Hk.
rewrite -(has_transition_omega_seq (char_mono w) (size w).-1 Hkb).
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
  rewrite Hkeq prednK // -ltnS.
  by case: (size w) Hsz2 Hi_lt => [//|[//|m]] _ /= Hi; exact: Hi.
rewrite (nth_char_mono Hk_lt) (nth_char_mono Hk1_lt).
by rewrite Hkeq prednK.
Qed.

(* -- Membership: all M-class char_monos are in expand_cde ----------------- *)

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

Lemma uniq_map_char_mono_powerset w :
  uniq w -> 2 <= size w ->
  uniq [seq char_mono (apply_psis ss w) | ss <- powerset_internal w].
Proof.
move=> Hu Hsz2.
set lhs := [seq _ | _ <- _].
set rhs := expand_cde (phi_w w).
have Hmem : {subset lhs <= rhs}.
  move=> x /mapP [ss _ ->]. exact: char_mono_apply_psis_mem.
have Hsz_lhs : size lhs = size rhs.
  rewrite /lhs /rhs size_map size_powerset_internal.
  by rewrite -size_expand_cde_phi_w.
have Huniq_rhs : uniq rhs := uniq_expand_cde _.
apply/negPn/negP => Hnuniq.
have : size lhs > size (undup lhs).
  rewrite size_undup_uniq; last exact: Hnuniq.
  by case: (lhs) Hnuniq => [//|x xs]; rewrite /= ltnS size_filter count_size.
move=> Hdup.
have Hsub : size (undup lhs) <= size rhs.
  apply: uniq_leq_size; first exact: undup_uniq.
  move=> x; rewrite mem_undup; exact: Hmem.
have : size lhs <= size rhs by rewrite Hsz_lhs.
move=> Hle.
by have := leq_ltn_trans Hsub Hdup; rewrite Hsz_lhs ltnn.
Qed.

(* -- check_fact3_true: structural proof ----------------------------------- *)

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
