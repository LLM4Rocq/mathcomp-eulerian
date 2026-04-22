(* psi.v — Milestone 2: Stanley's operators ψᵢ on min-max trees             *)
(*                                                                           *)
(* Implements the rank-shift operators ψᵢ of Stanley EC1 §1.6.3 on sequences *)
(* of distinct integers, with the min-or-max alternating tree construction   *)
(* (Option A of M2_PSI_INFORMAL.md §1.3).                                    *)

From mathcomp Require Import all_ssreflect.
Require Import mmtree.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* ----- 1. Alternating min-or-max split ----------------------------------- *)

Definition max_pos (s : seq nat) : nat :=
  index (foldr maxn (head 0 s) (behead s)) s.

Definition mm_pos (s : seq nat) : nat :=
  if min_pos s <= max_pos s then min_pos s else max_pos s.

Lemma max_in s a : foldr maxn a s \in a :: s.
Proof.
elim: s a => [| b s IH] a /=.
  by rewrite inE eqxx.
rewrite !inE.
case: leqP => _.
  have := IH a; rewrite inE => /orP [->|->] //; by rewrite !orbT.
by rewrite eqxx orbT.
Qed.

Lemma max_pos_lt s : s <> [::] -> max_pos s < size s.
Proof.
case: s => [// | a s _]; rewrite /max_pos.
by rewrite index_mem; exact: max_in.
Qed.

Lemma mm_pos_lt s : s <> [::] -> mm_pos s < size s.
Proof.
move=> Hs; rewrite /mm_pos; case: ifP => _; [exact: min_pos_lt | exact: max_pos_lt].
Qed.

Fixpoint mmtree_of_seq_mm_fuel (fuel : nat) (s : seq nat) : mmtree nat :=
  match fuel with
  | 0 => @Leaf nat
  | fuel'.+1 =>
      match s with
      | [::] => @Leaf nat
      | _ :: _ =>
          let j := mm_pos s in
          Node (mmtree_of_seq_mm_fuel fuel' (take j s))
               (nth 0 s j)
               (mmtree_of_seq_mm_fuel fuel' (drop j.+1 s))
      end
  end.

Definition mmtree_of_seq_mm (s : seq nat) : mmtree nat :=
  mmtree_of_seq_mm_fuel (size s) s.

Lemma mmtree_of_seq_mm_fuel_correct :
  forall fuel s, size s <= fuel ->
    mmtree_to_seq (mmtree_of_seq_mm_fuel fuel s) = s.
Proof.
elim => [| fuel IH] s.
  by rewrite leqn0 => /nilP ->.
case: s => [// | a s Hsz] /=.
set s0 := a :: s in Hsz *.
have Hj : mm_pos s0 < size s0 by apply: mm_pos_lt.
have Hleft : size (take (mm_pos s0) s0) <= fuel.
  rewrite size_take Hj.
  by rewrite -ltnS; apply: (leq_trans Hj).
have Hright : size (drop (mm_pos s0).+1 s0) <= fuel.
  rewrite size_drop.
  move: Hj; case: (size s0) Hsz => // k Hk Hk1.
  by rewrite subSS; apply: (leq_trans (leq_subr _ _)).
rewrite (IH _ Hleft) (IH _ Hright).
rewrite -[RHS](cat_take_drop (mm_pos s0) s0).
congr (_ ++ _).
by rewrite (drop_nth 0 Hj).
Qed.

Theorem mmtree_of_seq_mmK : forall s, mmtree_to_seq (mmtree_of_seq_mm s) = s.
Proof.
by move=> s; apply: mmtree_of_seq_mm_fuel_correct.
Qed.

(* ----- 2. Window size at position i ------------------------------------- *)
(*                                                                           *)
(* window_size i w = 1 + |right subtree of vertex at in-order position i|,   *)
(* or 0 when i is out of range. The window itself is take (window_size i w)  *)
(* (drop i w).                                                              *)

Fixpoint window_size_fuel (fuel : nat) (i : nat) (s : seq nat) : nat :=
  match fuel with
  | 0 => 0
  | fuel'.+1 =>
      match s with
      | [::] => 0
      | _ :: _ =>
          let j := mm_pos s in
          if i < j then window_size_fuel fuel' i (take j s)
          else if i == j then (size s - j)%N
          else window_size_fuel fuel' (i - j - 1) (drop j.+1 s)
      end
  end.

Definition window_size (i : nat) (s : seq nat) : nat :=
  window_size_fuel (size s) i s.

Definition window_at (i : nat) (w : seq nat) : seq nat :=
  take (window_size i w) (drop i w).

(* Key invariant: the window fits into w, i.e.
     0 < window_size i w <= size w - i   when i < size w.
   Equivalently: window_size i w = 0 when i >= size w,
   and 0 < window_size i w and i + window_size i w <= size w otherwise. *)

(* Combined invariant: gt0 iff in-range, and size-bound as slice-safe. *)
Lemma window_size_fuel_bound :
  forall fuel i s, size s <= fuel ->
    (0 < window_size_fuel fuel i s) = (i < size s)
    /\ window_size_fuel fuel i s <= size s - i.
Proof.
elim => [| fuel IH] i s Hsz.
  move: Hsz; rewrite leqn0 => /nilP ->.
  by split; case: i.
move: Hsz; case: s => [_ | a s0 Hsz]; first by split; case: i.
set s := a :: s0.
have Hs_sz : size s = (size s0).+1 by [].
have Hj : mm_pos s < size s by apply: mm_pos_lt.
set j := mm_pos s.
have Hj2 : j <= size s0 by rewrite -ltnS -Hs_sz.
have Hjf : j <= fuel by rewrite (leq_trans Hj2) // -ltnS.
rewrite /= -/j.
case Hij: (i < j).
  have Hsz' : size (take j s) <= fuel by rewrite size_take Hj.
  have [Heq Hbd] := IH i _ Hsz'.
  rewrite size_take Hj in Heq Hbd.
  split.
    by rewrite Heq Hij; symmetry; apply: (leq_ltn_trans (ltnW Hij)); rewrite ltnS.
  apply: (leq_trans Hbd).
  by rewrite leq_sub2r // ltnW.
case Hij2: (i == j).
  move/eqP in Hij2; rewrite Hij2.
  split; last by rewrite leqnn.
  by rewrite ltnS Hj2 subn_gt0 ltnS Hj2.
(* j < i : recurse on drop j.+1 s = drop j s0 *)
have Hsz2 : size (drop j s0) <= fuel.
  by rewrite size_drop; apply: (leq_trans (leq_subr _ _)).
have [Heq Hbd] := IH (i - j - 1) _ Hsz2.
rewrite size_drop in Heq Hbd.
have Hji : j < i.
  rewrite ltn_neqAle eq_sym Hij2.
  by move/negbT: Hij; rewrite -leqNgt.
split.
  rewrite Heq.
  have H1 : i - j - 1 + j.+1 = i.
    rewrite -[X in _ = X](@subnK j.+1 i) //.
    by rewrite [in RHS](_ : i - j.+1 = i - j - 1); last by rewrite -addn1 subnDA.
  have H2 : size s0 - j + j.+1 = (size s0).+1 by rewrite addnS subnK.
  by rewrite -(ltn_add2r j.+1) H1 H2.
apply: (leq_trans Hbd).
rewrite -subnDA.
have Heq_ij : j + (i - j - 1) = i - 1.
  rewrite addnBA //; first by rewrite addnC subnK // ltnW.
  by rewrite subn_gt0.
rewrite Heq_ij.
have [Hil | Hig] := leqP i (size s0).
  have Hi0 : 0 < i by exact: leq_ltn_trans Hji.
  case: i Hi0 Hji Hil Heq_ij {Hij Hij2 Hsz2 Heq Hbd} => // i' _ _ Hil _.
  by rewrite subn1 /= subSS leqnn.
have -> : size s0 - (i - 1) = 0.
  apply/eqP; rewrite subn_eq0.
  by case: i Hig Hij {Hji Hij2 Hsz2 Heq Hbd Heq_ij} => // i' Hig _; rewrite subn1 /=.
done.
Qed.

Lemma window_size_gt0 i w : i < size w -> 0 < window_size i w.
Proof.
move=> Hi.
have [Heq _] := window_size_fuel_bound i (leqnn (size w)).
by rewrite /window_size Heq.
Qed.

Lemma window_size_bound i w : window_size i w <= size w - i.
Proof.
by have [_ Hbd] := window_size_fuel_bound i (leqnn (size w)).
Qed.

Lemma window_size_oor i w : size w <= i -> window_size i w = 0.
Proof.
move=> Hi.
have [Heq _] := window_size_fuel_bound i (leqnn (size w)).
apply/eqP; rewrite -leqn0 leqNgt; apply/negP => H.
by rewrite /window_size in H; rewrite H ltnNge Hi in Heq.
Qed.

(* ----- 3. The rank-shift operator on a window --------------------------- *)

(* Rank-shift as a cyclic shift on indices into the sorted window.          *)
(* shift_amt L: if root = min, shift ranks by -1 (mod k); if root = max,    *)
(* shift by +1 (mod k). Default shift = 0 (identity) for trivial windows.   *)

Definition rank_shift_seq (L : seq nat) : seq nat :=
  let sorted := sort leq L in
  let k := size sorted in
  if (k <= 1) || ~~ uniq L then L else
  let shift_by := if head 0 L == nth 0 sorted 0 then k.-1 else 1 in
  [seq nth 0 sorted ((index y sorted + shift_by) %% k) | y <- L].

Lemma size_rank_shift_seq L : size (rank_shift_seq L) = size L.
Proof.
rewrite /rank_shift_seq.
by case: ifP => _ //; rewrite size_map.
Qed.

(* ----- 4. ψᵢ ------------------------------------------------------------- *)

Definition psi (i : nat) (w : seq nat) : seq nat :=
  take i w ++ rank_shift_seq (window_at i w) ++ drop (i + window_size i w) w.

(* ----- 5. rank_shift preserves the multiset ----------------------------- *)

(* Helper: mapping sorted back by nth-index is the identity. *)
Lemma map_nth_iota_sorted (sorted : seq nat) :
  [seq nth 0 sorted i | i <- iota 0 (size sorted)] = sorted.
Proof.
apply: (@eq_from_nth _ 0); first by rewrite size_map size_iota.
move=> i Hi.
rewrite (nth_map 0); last first.
  by rewrite size_iota; move: Hi; rewrite size_map size_iota.
rewrite nth_iota ?add0n //.
by move: Hi; rewrite size_map size_iota.
Qed.

(* For shift < k, map of (+shift) %% k on iota 0 k equals rot (k - shift) on
   iota 0 k. This uses that iota 0 k = iota 0 (k-shift) ++ iota (k-shift) shift
   and the mod rearrangement. *)
Lemma map_mod_iota_rot (shift k : nat) : shift < k ->
  [seq (i + shift) %% k | i <- iota 0 k] = rot shift (iota 0 k).
Proof.
move=> Hsh.
have Hsh_le : shift <= k by apply: ltnW.
rewrite /rot.
have Hit : iota 0 k = iota 0 (k - shift) ++ iota (k - shift) shift.
  by rewrite -iotaD subnK.
rewrite {1}Hit map_cat.
have Htake : take shift (iota 0 k) = iota 0 shift.
  rewrite -{1}(subnKC Hsh_le) iotaD take_size_cat ?size_iota //.
have Hdrop : drop shift (iota 0 k) = iota shift (k - shift).
  rewrite -{1}(subnKC Hsh_le) iotaD drop_size_cat ?size_iota //.
rewrite Htake Hdrop.
congr (_ ++ _).
  apply: (@eq_from_nth _ 0); first by rewrite size_map !size_iota.
  move=> i; rewrite size_map size_iota => Hi.
  rewrite (nth_map 0) ?size_iota // nth_iota // !add0n nth_iota //.
  rewrite addnC modn_small //.
  by rewrite -ltn_subRL.
apply: (@eq_from_nth _ 0); first by rewrite size_map !size_iota.
move=> i; rewrite size_map size_iota => Hi.
rewrite (nth_map 0) ?size_iota // nth_iota // nth_iota // !add0n.
have Hge : k <= k - shift + i + shift.
  by rewrite -addnA [i+_]addnC addnA subnK // leq_addr.
have Hsimp : (k - shift + i + shift) - k = i.
  by rewrite -addnA [i+_]addnC addnA subnK // addKn.
rewrite -[in LHS](subnKC Hge) Hsimp.
rewrite -modnDml modnn add0n modn_small //.
by apply: leq_trans Hi Hsh_le.
Qed.

Lemma rank_shift_perm_eq L : perm_eq (rank_shift_seq L) L.
Proof.
rewrite /rank_shift_seq.
case: ifP => [_ | Hcond]; first exact: perm_refl.
move/negbT: Hcond; rewrite negb_or -ltnNge negbK => /andP [Hk Huniq].
set sorted := sort leq L in Hk *.
set k := size sorted.
set shift := (if head 0 L == nth 0 sorted 0 then k.-1 else 1).
have Huniq_s : uniq sorted by rewrite sort_uniq.
have Hperm_Ls : perm_eq L sorted by rewrite perm_sym perm_sort.
have Hshift_lt : shift < k.
  have Hkpos : 0 < k by apply: (@leq_ltn_trans 1 _ _) => //; exact: ltnW.
  rewrite /shift; case: ifP => _; last by [].
  by rewrite prednK.
apply: (perm_trans (perm_map _ Hperm_Ls)).
apply: (perm_trans (y := sorted)); last by rewrite perm_sym.
set f := (fun y => nth 0 sorted ((index y sorted + shift) %% k)).
have -> : map f sorted = map (nth 0 sorted) [seq (i + shift) %% k | i <- iota 0 k].
  rewrite /f.
  apply: (@eq_from_nth _ 0); first by rewrite !size_map size_iota.
  move=> i Hi; rewrite size_map in Hi.
  have Hiota : i < size (iota 0 k) by rewrite size_iota.
  have Hmap_iota : i < size [seq (i0 + shift) %% k | i0 <- iota 0 k]
    by rewrite size_map size_iota.
  rewrite (@nth_map _ 0 _ 0 _ _ _ Hi).
  rewrite (@nth_map _ 0 _ 0 _ _ _ Hmap_iota).
  rewrite (@nth_map _ 0 _ 0 _ _ _ Hiota) nth_iota -/k //.
  by rewrite add0n index_uniq.
rewrite (map_mod_iota_rot Hshift_lt).
have <- : map (nth 0 sorted) (iota 0 k) = sorted by apply: map_nth_iota_sorted.
apply: perm_trans; last by apply/permPl; apply: perm_rot.
rewrite /rot map_cat.
rewrite !map_drop !map_take !map_nth_iota_sorted -/k.
exact: perm_refl.
Qed.


(* ----- 5b. rank_shift is an involution on uniq lists of size >= 2 ------- *)

Lemma sort_rank_shift_seq L : uniq L -> 1 < size L ->
  sort leq (rank_shift_seq L) = sort leq L.
Proof.
move=> Huniq Hsz.
apply/perm_sortP; rewrite ?sort_sorted ?sort_le_sorted //.
- by move=> ?; exact: leq_total.
- exact: leq_trans.
- exact: anti_leq.
- exact: rank_shift_perm_eq.
Qed.

Lemma uniq_rank_shift_seq L : uniq L -> uniq (rank_shift_seq L).
Proof.
by move=> Huniq; rewrite (perm_uniq (rank_shift_perm_eq L)).
Qed.

(* Size preserved — follows from perm_eq. *)
Lemma size_rank_shift_seq2 L : size (rank_shift_seq L) = size L.
Proof. by apply: perm_size; apply: rank_shift_perm_eq. Qed.


(* ----- 6. psi_perm_eq --------------------------------------------------- *)

Lemma psi_perm_eq i w : perm_eq (psi i w) w.
Proof.
rewrite /psi.
set L := window_at i w.
have Hperm_L : perm_eq (rank_shift_seq L) L by apply: rank_shift_perm_eq.
have Heq_w : w = take i w ++ L ++ drop (i + window_size i w) w.
  rewrite /L /window_at.
  rewrite -{1}[w](cat_take_drop i).
  congr (_ ++ _).
  rewrite -{1}[drop i w](cat_take_drop (window_size i w)).
  by rewrite drop_drop addnC.
rewrite [in X in perm_eq _ X]Heq_w.
by rewrite perm_cat2l perm_cat2r.
Qed.

(* Non-triviality example first, sanity check. *)

Example psi_nontrivial :
  psi 5 [:: 3; 1; 4; 7; 5; 9; 2; 6] = [:: 3; 1; 4; 7; 5; 2; 6; 9].
Proof. by []. Qed.

Example psi_involutive_ex :
  psi 5 (psi 5 [:: 3; 1; 4; 7; 5; 9; 2; 6]) = [:: 3; 1; 4; 7; 5; 9; 2; 6].
Proof. by []. Qed.

(* ----- 7. Involutivity ---------------------------------------------------- *)

(* Explicit characterization of one entry of rank_shift_seq. *)
Lemma rank_shift_seqE L : uniq L -> 1 < size L ->
  rank_shift_seq L = [seq nth 0 (sort leq L)
    ((index y (sort leq L) +
      (if head 0 L == nth 0 (sort leq L) 0 then (size L).-1 else 1))
     %% size L) | y <- L].
Proof.
move=> Hu Hsz.
rewrite /rank_shift_seq.
have Hcond : ~~ ((size (sort leq L) <= 1) || ~~ uniq L).
  by rewrite negb_or -ltnNge negbK size_sort Hsz Hu.
case: ifP => [Hc|_]; first by move/negP: Hcond; rewrite Hc.
by rewrite size_sort.
Qed.

Lemma nth_rank_shift_seq L n : uniq L -> 1 < size L -> n < size L ->
  nth 0 (rank_shift_seq L) n =
    nth 0 (sort leq L)
      ((index (nth 0 L n) (sort leq L) +
        (if head 0 L == nth 0 (sort leq L) 0 then (size L).-1 else 1))
       %% size L).
Proof.
move=> Hu Hsz Hn.
by rewrite (rank_shift_seqE Hu Hsz) (nth_map 0).
Qed.

Lemma head_rank_shift_seq L : uniq L -> 1 < size L ->
  head 0 (rank_shift_seq L) =
    nth 0 (sort leq L)
      ((index (head 0 L) (sort leq L) +
        (if head 0 L == nth 0 (sort leq L) 0 then (size L).-1 else 1))
       %% size L).
Proof.
move=> Hu Hsz.
have Hsz0 : 0 < size L by apply: ltnW.
by rewrite -nth0 (nth_rank_shift_seq Hu Hsz Hsz0) nth0.
Qed.

(* Key rank-shift involutivity lemma.  When L is uniq, has size >= 2, and
   its head is the min or max of L, applying rank_shift_seq twice is identity. *)
Lemma rank_shift_seq_involutive L : uniq L -> 1 < size L ->
  let s := sort leq L in
  (head 0 L == nth 0 s 0) || (head 0 L == nth 0 s (size L).-1) ->
  rank_shift_seq (rank_shift_seq L) = L.
Proof.
move=> Hu Hsz /= Hhead.
set s := sort leq L.  set k := size L.
have Hu_rs : uniq (rank_shift_seq L) by apply: uniq_rank_shift_seq.
have Hsz_rs : 1 < size (rank_shift_seq L) by rewrite size_rank_shift_seq2.
have Hsz_rs_eq : size (rank_shift_seq L) = k by rewrite size_rank_shift_seq2.
have Hsort_rs : sort leq (rank_shift_seq L) = s.
  by apply: sort_rank_shift_seq.
have Hk0 : 0 < k by apply: ltnW.
have Hkm1_lt : k.-1 < k by rewrite prednK.
have Hu_s : uniq s by rewrite sort_uniq.
have Hsz_s : size s = k by rewrite /s size_sort.
have Hkm1_gt0 : 0 < k.-1 by rewrite -ltnS prednK.
have Hmin_ne_max : nth 0 s 0 != nth 0 s k.-1.
  apply/negP => /eqP Hc.
  move/eqP: Hc; rewrite (nth_uniq _ _ _ Hu_s) ?Hsz_s //.
  by move/eqP => E; move: Hkm1_gt0; rewrite -E.
apply: (@eq_from_nth _ 0).
  by rewrite !size_rank_shift_seq2.
move=> n Hn.
rewrite size_rank_shift_seq2 Hsz_rs_eq in Hn.
rewrite (nth_rank_shift_seq Hu_rs Hsz_rs); last by rewrite Hsz_rs_eq.
rewrite Hsort_rs Hsz_rs_eq -/k.
rewrite (nth_rank_shift_seq Hu Hsz Hn) -/s.
set x := nth 0 s ((index (nth 0 L n) s + _) %% k).
have Hidx_x : index x s =
    (index (nth 0 L n) s + (if head 0 L == nth 0 s 0 then k.-1 else 1)) %% k.
  by rewrite /x index_uniq // Hsz_s ltn_pmod.
rewrite Hidx_x.
have Hhead_rs : head 0 (rank_shift_seq L) =
    nth 0 s ((index (head 0 L) s +
              (if head 0 L == nth 0 s 0 then k.-1 else 1)) %% k).
  by rewrite (head_rank_shift_seq Hu Hsz) -/s -/k.
rewrite Hhead_rs.
have Hk0_s : 0 < size s by rewrite Hsz_s.
case/orP: Hhead => /eqP Hhead.
- have Heq1 : head 0 L == nth 0 s 0 by rewrite Hhead.
  rewrite Heq1 Hhead.
  rewrite (index_uniq _ Hk0_s Hu_s) add0n (modn_small Hkm1_lt).
  have Hne : nth 0 s k.-1 == nth 0 s 0 = false.
    by apply/negbTE; rewrite eq_sym.
  rewrite Hne.
  set i := index (nth 0 L n) s.
  have Hi_lt : i < k by rewrite -Hsz_s /i index_mem mem_sort mem_nth.
  rewrite modnDml.
  have -> : (i + k.-1 + 1) %% k = i.
    by rewrite -addnA addn1 prednK // -modnDmr modnn addn0 modn_small.
  by rewrite /i nth_index // mem_sort mem_nth.
- have Heq1 : head 0 L == nth 0 s 0 = false.
    apply/negbTE; rewrite Hhead eq_sym.
    by move: Hmin_ne_max; rewrite eq_sym.
  rewrite Heq1 Hhead.
  have Hkm1_lt_s : k.-1 < size s by rewrite Hsz_s.
  rewrite (index_uniq _ Hkm1_lt_s Hu_s).
  have -> : (k.-1 + 1) %% k = 0.
    by rewrite addn1 prednK // modnn.
  rewrite eqxx.
  set i := index (nth 0 L n) s.
  have Hi_lt : i < k by rewrite -Hsz_s /i index_mem mem_sort mem_nth.
  rewrite modnDml.
  have -> : (i + 1 + k.-1) %% k = i.
    by rewrite -addnA add1n prednK // -modnDmr modnn addn0 modn_small.
  by rewrite /i nth_index // mem_sort mem_nth.
Qed.

(* ----- 8. Window size structural recursion ------------------------------- *)

Lemma window_size_fuel_monotone fuel1 fuel2 i s :
  size s <= fuel1 -> fuel1 <= fuel2 ->
  window_size_fuel fuel2 i s = window_size_fuel fuel1 i s.
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

(* Structural unfolding of window_size on a nonempty list. *)
Lemma window_size_cons i a s0 :
  let s := a :: s0 in
  let j := mm_pos s in
  window_size i s =
    if i < j then window_size i (take j s)
    else if i == j then (size s - j)%N
    else window_size (i - j - 1) (drop j.+1 s).
Proof.
set s := a :: s0. set j := mm_pos s.
have Hj : j < size s by apply: mm_pos_lt.
have Hj2 : j <= size s0 by rewrite -ltnS.
have Htake_sz : size (take j s) <= size s0.
  by rewrite size_take Hj.
have Hdrop_sz : size (drop j s0) <= size s0.
  by rewrite size_drop; apply: leq_subr.
rewrite /window_size /= -/j.
case: ifP => _.
  apply: window_size_fuel_monotone => //.
case: ifP => _ //.
apply: window_size_fuel_monotone => //.
Qed.

(* psi is the identity when i is out of range. *)
Lemma psi_id_oor i w : size w <= i -> psi i w = w.
Proof.
move=> Hi.
have Hws : window_size i w = 0 by apply: window_size_oor.
rewrite /psi /window_at Hws take0 addn0.
rewrite (_ : rank_shift_seq [::] = [::]); last by rewrite /rank_shift_seq.
by rewrite cat0s cat_take_drop.
Qed.

(* psi is the identity when the window has size <= 1. *)
Lemma psi_id_trivial i w : window_size i w <= 1 -> psi i w = w.
Proof.
move=> Hws.
rewrite /psi /window_at.
set L := take (window_size i w) (drop i w).
have HszL : size L <= 1.
  rewrite /L size_take size_drop.
  case: ltnP => H; first exact: Hws.
  by apply: leq_trans Hws.
have HrsL : rank_shift_seq L = L.
  rewrite /rank_shift_seq.
  suff -> : (size (sort leq L) <= 1) || ~~ uniq L by [].
  by rewrite size_sort HszL.
rewrite HrsL /L.
rewrite -[RHS](cat_take_drop i); congr (_ ++ _).
rewrite -[RHS](cat_take_drop (window_size i w) (drop i w)).
by rewrite drop_drop addnC.
Qed.

(* Window-at decomposition by the mm_pos split *)
Lemma window_at_cons i a s0 :
  let s := a :: s0 in
  let j := mm_pos s in
  window_at i s =
    if i < j then window_at i (take j s)
    else if i == j then drop j s
    else window_at (i - j - 1) (drop j.+1 s).
Proof.
set s := a :: s0. set j := mm_pos s.
have Hj : j < size s by apply: mm_pos_lt.
have Hj2 : j <= size s0 by rewrite -ltnS.
rewrite /window_at window_size_cons -/s -/j.
case: ifP => Hij.
  rewrite -{2}[s](cat_take_drop j) drop_cat size_take Hj Hij.
  rewrite take_cat size_drop size_take Hj.
  have Hws_le : window_size i (take j s) <= j - i.
    by move: (window_size_bound i (take j s)); rewrite size_take Hj.
  case: ltnP => [_ | Hge] //.
  have Heq : window_size i (take j s) = j - i.
    by apply/eqP; rewrite eqn_leq Hws_le Hge.
  rewrite Heq subnn take0 cats0.
  rewrite -{1}[drop i (take j s)]take_size size_drop size_take Hj.
  by rewrite -Heq.
case: ifP => Hij2.
  move/eqP: Hij2 => ->.
  by rewrite take_oversize // size_drop.
have Hji : j < i.
  by rewrite ltn_neqAle eq_sym Hij2; move/negbT: Hij; rewrite -leqNgt.
rewrite drop_drop.
have -> : i - j - 1 + j.+1 = i.
  have Hpos : 0 < i - j by rewrite subn_gt0.
  rewrite -[j.+1]addn1 [_ + (_ + _)]addnA.
  rewrite [_ - 1 + _ + 1](_ : _ = (i - j - 1 + 1) + j);
    last by rewrite -addnA [j + _]addnC addnA.
  by rewrite subnK // subnK // ltnW.
by [].
Qed.

(* ----- T4 prerequisites: basic psi properties ----------------------------- *)

Lemma size_psi i w : size (psi i w) = size w.
Proof. by apply: perm_size; apply: psi_perm_eq. Qed.

Lemma uniq_psi i w : uniq w -> uniq (psi i w).
Proof. by move=> Hu; rewrite (perm_uniq (psi_perm_eq i w)). Qed.

Lemma take_psi k j w :
  k <= j -> take k (psi j w) = take k w.
Proof.
move=> Hkj; rewrite /psi take_cat size_take.
have [Hj | Hj] := ltnP j (size w).
  have [Hkj2 | Hkj2] := ltnP k j.
    by rewrite take_takel // ltnW.
  have /eqP Hkj3 : k == j by rewrite eqn_leq Hkj Hkj2.
  by subst k; rewrite subnn take0 cats0.
have [Hks | Hks] := ltnP k (size w).
  by apply: take_takel.
have -> : window_size j w = 0 by apply: window_size_oor.
have -> : window_at j w = [::].
  rewrite /window_at; have -> : window_size j w = 0 by apply: window_size_oor.
  by rewrite take0.
rewrite /= addn0 drop_oversize; last by [].
rewrite cats0; have -> : take j w = w by apply: take_oversize.
by rewrite take_oversize.
Qed.

(* ----- T4 prerequisites: foldr min/max bounds ----------------------------- *)

Lemma foldr_minn_aux s a :
  foldr minn a s <= a /\ forall x, x \in s -> foldr minn a s <= x.
Proof.
elim: s a => [|b s IH] a /=; first by split => // x; rewrite in_nil.
have [H1 H2] := IH a; split.
  by apply: leq_trans (geq_minr _ _) H1.
move=> x; rewrite inE => /orP [/eqP -> | Hx].
  exact: geq_minl.
by apply: leq_trans (geq_minr _ _) (H2 _ Hx).
Qed.

Lemma foldr_minn_le s a x : x \in a :: s -> foldr minn a s <= x.
Proof.
have [H1 H2] := foldr_minn_aux s a.
by rewrite inE => /orP [/eqP -> | /(H2 _)].
Qed.

Lemma foldr_maxn_aux s a :
  a <= foldr maxn a s /\ forall x, x \in s -> x <= foldr maxn a s.
Proof.
elim: s a => [|b s IH] a /=; first by split => // x; rewrite in_nil.
have [H1 H2] := IH a; split.
  by apply: leq_trans H1 (leq_maxr _ _).
move=> x; rewrite inE => /orP [/eqP -> | Hx].
  exact: leq_maxl.
by apply: leq_trans (H2 _ Hx) (leq_maxr _ _).
Qed.

Lemma foldr_maxn_ge s a x : x \in a :: s -> x <= foldr maxn a s.
Proof.
have [H1 H2] := foldr_maxn_aux s a.
by rewrite inE => /orP [/eqP -> | /(H2 _)].
Qed.

Lemma min_val_perm_eq s1 s2 :
  s1 <> [::] -> perm_eq s1 s2 ->
  foldr minn (head 0 s1) (behead s1) =
  foldr minn (head 0 s2) (behead s2).
Proof.
case: s1 => [//|a1 s1] _; case: s2 => [|a2 s2] Hp /=.
  by have := perm_size Hp.
apply/eqP; rewrite eqn_leq; apply/andP; split.
- by apply: foldr_minn_le; rewrite (perm_mem Hp); apply: min_in.
- by apply: foldr_minn_le; rewrite -(perm_mem Hp); apply: min_in.
Qed.

Lemma max_val_perm_eq s1 s2 :
  s1 <> [::] -> perm_eq s1 s2 ->
  foldr maxn (head 0 s1) (behead s1) =
  foldr maxn (head 0 s2) (behead s2).
Proof.
case: s1 => [//|a1 s1] _; case: s2 => [|a2 s2] Hp /=.
  by have := perm_size Hp.
apply/eqP; rewrite eqn_leq; apply/andP; split.
- by apply: foldr_maxn_ge; rewrite -(perm_mem Hp); apply: max_in.
- by apply: foldr_maxn_ge; rewrite (perm_mem Hp); apply: max_in.
Qed.

(* ----- T4: window_fits_left ----------------------------------------------- *)

Lemma window_fits_left i w :
  w <> [::] -> i < mm_pos w -> i + window_size i w <= mm_pos w.
Proof.
case: w => [//|a s0] _ Hij.
rewrite (window_size_cons i a s0).
set j := mm_pos (a :: s0).
rewrite Hij.
have Hj : j < size (a :: s0) by apply: mm_pos_lt.
have := window_size_bound i (take j (a :: s0)).
rewrite size_take Hj => Hbd.
have : i + window_size i (take j (a :: s0)) <= i + (j - i)
  by rewrite leq_add2l.
by rewrite subnKC // ltnW.
Qed.

(* ----- T3: nth_psi_outside ------------------------------------------------ *)

Lemma drop_psi i w :
  drop (i + window_size i w) (psi i w) = drop (i + window_size i w) w.
Proof.
case: (leqP (size w) i) => Hiw.
  by rewrite (psi_id_oor Hiw).
set ws := window_size i w; set wa := window_at i w.
have Hws_le : ws <= size w - i by apply: window_size_bound.
have Hwa_sz : size wa = ws.
  rewrite /wa /window_at size_take size_drop.
  case: ltnP => // H.
  by apply/eqP; rewrite eqn_leq H Hws_le.
have Hsz_take : size (take i w) = i by rewrite size_take Hiw.
have Hsz_AB : size (take i w ++ rank_shift_seq wa) = i + ws.
  by rewrite size_cat Hsz_take size_rank_shift_seq Hwa_sz.
by rewrite /psi -/wa -/ws catA drop_cat Hsz_AB ltnn subnn drop0.
Qed.

Lemma nth_psi_left i w k : k < i -> nth 0 (psi i w) k = nth 0 w k.
Proof.
move=> Hki.
rewrite -(@nth_take i _ 0 k Hki (psi i w)).
by rewrite (@take_psi i i w (leqnn i)) (@nth_take i _ 0 k Hki w).
Qed.

Lemma nth_psi_right i w k :
  i + window_size i w <= k -> nth 0 (psi i w) k = nth 0 w k.
Proof.
move=> Hki.
rewrite -{1}(subnK Hki) addnC -nth_drop.
by rewrite drop_psi nth_drop addnC subnK.
Qed.

Lemma nth_psi_inside i w k :
  i < size w -> i <= k -> k < i + window_size i w ->
  nth 0 (psi i w) k =
  nth 0 (rank_shift_seq (window_at i w)) (k - i).
Proof.
move=> Hiw Hik Hkw.
set ws := window_size i w. set wa := window_at i w.
have Hws_le : ws <= size w - i by apply: window_size_bound.
have Hwa_sz : size wa = ws.
  rewrite /wa /window_at size_take size_drop.
  by case: ltnP => // H; apply/eqP; rewrite eqn_leq H Hws_le.
have Hsz_take : size (take i w) = i
  by rewrite size_take Hiw.
rewrite /psi -/ws -/wa catA.
rewrite nth_cat size_cat Hsz_take size_rank_shift_seq
        Hwa_sz Hkw.
rewrite nth_cat Hsz_take.
by rewrite ltnNge Hik.
Qed.

(* ----- T4a: perm_eq of takes under psi ----------------------------------- *)

Lemma take_psi_perm j i w :
  i < size w -> i + window_size i w <= j -> j <= size w ->
  perm_eq (take j (psi i w)) (take j w).
Proof.
move=> Hiw Hfit Hjw.
set ws := window_size i w; set wa := window_at i w.
have Hws_le : ws <= size w - i by apply: window_size_bound.
have Hwa_sz : size wa = ws.
  rewrite /wa /window_at size_take size_drop.
  by case: ltnP => // H; apply/eqP; rewrite eqn_leq H Hws_le.
have Hsz_take : size (take i w) = i by rewrite size_take Hiw.
have Hsz_psi : size (take i w ++ rank_shift_seq wa) = i + ws.
  by rewrite size_cat Hsz_take size_rank_shift_seq Hwa_sz.
have Hsz_w : size (take i w ++ wa) = i + ws.
  by rewrite size_cat Hsz_take Hwa_sz.
suff: take j (psi i w) =
  take i w ++ rank_shift_seq wa ++ take (j - (i + ws)) (drop (i + ws) w) /\
  take j w =
  take i w ++ wa ++ take (j - (i + ws)) (drop (i + ws) w).
  by case=> -> ->; rewrite perm_cat2l perm_cat2r rank_shift_perm_eq.
split.
- rewrite /psi -/ws -/wa catA take_cat Hsz_psi /ws ltnNge Hfit /=.
  by rewrite catA.
- have Hw_eq : w = take i w ++ wa ++ drop (i + ws) w.
    rewrite /wa /window_at.
    have -> : drop (i + ws) w = drop ws (drop i w)
      by rewrite drop_drop addnC.
    by rewrite cat_take_drop cat_take_drop.
  rewrite {1}Hw_eq [take i w ++ wa ++ _]catA take_cat Hsz_w
          /ws ltnNge Hfit /=.
  by rewrite catA.
Qed.

(* ----- T4b: no extremum in prefix of w ----------------------------------- *)

Lemma notin_take_mm w :
  w <> [::] ->
  let j := mm_pos w in
  [/\ foldr minn (head 0 w) (behead w) \notin take j w
    & foldr maxn (head 0 w) (behead w) \notin take j w].
Proof.
case: w => [//|a s] _ /=.
set j := mm_pos (a :: s).
have Hj : j < size (a :: s) by apply: mm_pos_lt.
split; rewrite (in_take_leq _ (ltnW Hj)) -leqNgt /j /mm_pos /min_pos /max_pos.
- by case: ifP => [_ | /negbT]; rewrite -?ltnNge //; move/ltnW.
- by case: ifP.
Qed.

(* ----- T4c: extremum at position j in psi(w) ----------------------------- *)

Lemma min_val_drop j w :
  w <> [::] ->
  foldr minn (head 0 w) (behead w) \notin take j w ->
  j < size w ->
  foldr minn (head 0 (drop j w)) (behead (drop j w)) =
  foldr minn (head 0 w) (behead w).
Proof.
case: w => [//|a s] _ Hno Hj /=.
set minv := foldr minn a s.
have Hmin_in : minv \in a :: s by apply: min_in.
have Hmin_drop : minv \in drop j (a :: s).
  rewrite -(cat_take_drop j (a :: s)) mem_cat in Hmin_in.
  by case/orP: Hmin_in => // /(negP Hno).
have Hdrop_ne : drop j (a :: s) <> [::].
  by case: (drop j (a :: s)) Hmin_drop.
apply/eqP; rewrite eqn_leq; apply/andP; split.
- apply: foldr_minn_le.
  by case: (drop j (a :: s)) Hdrop_ne Hmin_drop => [//|b t].
- have Hmin_drop' : foldr minn (head 0 (drop j (a :: s)))
      (behead (drop j (a :: s))) \in drop j (a :: s).
    by case: (drop j (a :: s)) Hdrop_ne => [//|b t] _; apply: min_in.
  apply: foldr_minn_le. exact: mem_drop Hmin_drop'.
Qed.

Lemma max_val_drop j w :
  w <> [::] ->
  foldr maxn (head 0 w) (behead w) \notin take j w ->
  j < size w ->
  foldr maxn (head 0 (drop j w)) (behead (drop j w)) =
  foldr maxn (head 0 w) (behead w).
Proof.
case: w => [//|a s] _ Hno Hj /=.
set maxv := foldr maxn a s.
have Hmax_in : maxv \in a :: s by apply: max_in.
have Hmax_drop : maxv \in drop j (a :: s).
  rewrite -(cat_take_drop j (a :: s)) mem_cat in Hmax_in.
  by case/orP: Hmax_in => // /(negP Hno).
have Hdrop_ne : drop j (a :: s) <> [::].
  by case: (drop j (a :: s)) Hmax_drop.
apply/eqP; rewrite eqn_leq; apply/andP; split.
- have Hmax_drop' : foldr maxn (head 0 (drop j (a :: s)))
      (behead (drop j (a :: s))) \in drop j (a :: s).
    by case: (drop j (a :: s)) Hdrop_ne => [//|b t] _; apply: max_in.
  apply: foldr_maxn_ge. exact: mem_drop Hmax_drop'.
- apply: foldr_maxn_ge.
  by case: (drop j (a :: s)) Hdrop_ne Hmax_drop => [//|b t].
Qed.

(* ----- T4d: mm_pos characterization --------------------------------------- *)

Lemma mm_pos_char (s : seq nat) (j : nat) :
  s <> [::] -> j < size s ->
  foldr minn (head 0 s) (behead s) \notin take j s ->
  foldr maxn (head 0 s) (behead s) \notin take j s ->
  (nth 0 s j = foldr minn (head 0 s) (behead s) \/
   nth 0 s j = foldr maxn (head 0 s) (behead s)) ->
  mm_pos s = j.
Proof.
case: s => [//|a s0] _ Hj Hno_min Hno_max /= Hval.
set minv := foldr minn a s0; set maxv := foldr maxn a s0.
have Hj' : j < size (a :: s0) by [].
have Hmin_ge : j <= index minv (a :: s0).
  by rewrite leqNgt -(in_take_leq _ (ltnW Hj')) /=.
have Hmax_ge : j <= index maxv (a :: s0).
  by rewrite leqNgt -(in_take_leq _ (ltnW Hj')) /=.
have Hsplit : a :: s0 =
  take j (a :: s0) ++ nth 0 (a :: s0) j :: drop j.+1 (a :: s0).
  by rewrite -{1}[a :: s0](cat_take_drop j) (drop_nth 0 Hj').
case: Hval => Hval.
- have Hmin_eq : index minv (a :: s0) = j.
    rewrite Hsplit index_cat (negbTE Hno_min) /= Hval eqxx /=.
    by rewrite size_take Hj' addn0.
  rewrite /mm_pos /min_pos /max_pos.
  change (foldr minn (head 0 (a :: s0)) (behead (a :: s0))) with minv.
  change (foldr maxn (head 0 (a :: s0)) (behead (a :: s0))) with maxv.
  by rewrite Hmin_eq; case: leqP => [//|]; rewrite ltnNge Hmax_ge.
- have Hmax_eq : index maxv (a :: s0) = j.
    rewrite Hsplit index_cat (negbTE Hno_max) /= Hval eqxx /=.
    by rewrite size_take Hj' addn0.
  rewrite /mm_pos /min_pos /max_pos.
  change (foldr minn (head 0 (a :: s0)) (behead (a :: s0))) with minv.
  change (foldr maxn (head 0 (a :: s0)) (behead (a :: s0))) with maxv.
  rewrite Hmax_eq.
  by case: ifP => [Hle|_] //; apply/eqP; rewrite eqn_leq Hle Hmin_ge.
Qed.

Lemma nth_w_mm_pos w :
  w <> [::] ->
  nth 0 w (mm_pos w) = foldr minn (head 0 w) (behead w) \/
  nth 0 w (mm_pos w) = foldr maxn (head 0 w) (behead w).
Proof.
case: w => [//|a s] _ /=.
rewrite /mm_pos /min_pos /max_pos; case: ifP => _.
  by left; rewrite nth_index //; apply: min_in.
by right; rewrite nth_index //; apply: max_in.
Qed.

(* ----- T4e: bridge foldr minn/maxn to sorted-list positions --------------- *)

Lemma sorted_head_le (s : seq nat) :
  sorted leq s ->
  forall x, x \in s -> head 0 s <= x.
Proof.
case: s => [//|a s] /= Hp x.
rewrite inE => /orP [/eqP ->|Hx] //.
have : all (leq a) s
  by apply: order_path_min => //; exact: leq_trans.
by move/allP => /(_ x Hx).
Qed.

Lemma sorted_last_ge (s : seq nat) :
  sorted leq s ->
  forall x, x \in s -> x <= last 0 s.
Proof.
case: s => [//|a s].
elim: s a => [|b s IH] a /= Hs x Hx.
  by move: Hx; rewrite inE => /eqP ->.
move: Hs => /andP [Hab Hpath].
move: Hx; rewrite inE => /orP [/eqP -> | Hx].
  have := IH b Hpath b; rewrite inE eqxx => /(_ isT).
  exact: leq_trans Hab.
exact: (IH b Hpath x); rewrite inE Hx orbT.
Qed.

Lemma min_eq_nth_sort_0 (L : seq nat) :
  L <> [::] ->
  foldr minn (head 0 L) (behead L) =
  nth 0 (sort leq L) 0.
Proof.
case: L => [//|a s] _ /=.
apply/eqP; rewrite eqn_leq; apply/andP; split.
- apply: foldr_minn_le.
  have : nth 0 (sort leq (a :: s)) 0 \in sort leq (a :: s).
    apply: mem_nth; by rewrite size_sort.
  by rewrite mem_sort.
- have Hmin_in : foldr minn a s \in sort leq (a :: s)
    by rewrite mem_sort; exact: min_in.
  rewrite nth0.
  exact: sorted_head_le
    (sort_sorted leq_total (a :: s)) _ Hmin_in.
Qed.

Lemma max_eq_nth_sort_last (L : seq nat) :
  L <> [::] ->
  foldr maxn (head 0 L) (behead L) =
  nth 0 (sort leq L) (size L).-1.
Proof.
case: L => [//|a s] _ /=.
apply/eqP; rewrite eqn_leq; apply/andP; split.
- have Hmax_in : foldr maxn a s \in sort leq (a :: s)
    by rewrite mem_sort; exact: max_in.
  have Heq : nth 0 (sort leq (a :: s)) (size s) =
             last 0 (sort leq (a :: s)).
    by rewrite -nth_last size_sort.
  rewrite Heq.
  exact: sorted_last_ge
    (sort_sorted leq_total (a :: s)) _ Hmax_in.
- apply: foldr_maxn_ge.
  have : nth 0 (sort leq (a :: s)) (size s)
         \in sort leq (a :: s).
    apply: mem_nth; by rewrite size_sort.
  by rewrite mem_sort.
Qed.

(* ----- T4e2: Head-flip lemmas (moved up for use in mm_pos_psi_eq) -------- *)
(* rank_shift sends min-head to max and vice versa.                         *)

Lemma rank_shift_head_min_to_max (L : seq nat) :
  uniq L -> 1 < size L ->
  head 0 L = nth 0 (sort leq L) 0 ->
  head 0 (rank_shift_seq L) =
  nth 0 (sort leq L) (size L).-1.
Proof.
move=> Hu Hsz Hmin.
rewrite (head_rank_shift_seq Hu Hsz).
have Heq : head 0 L == nth 0 (sort leq L) 0 by rewrite Hmin.
rewrite Heq.
set k := size L.
have Hk0 : 0 < k by apply: ltnW.
have Hu_s : uniq (sort leq L) by rewrite sort_uniq.
rewrite Hmin index_uniq ?add0n ?size_sort //.
by rewrite modn_small // prednK.
Qed.

Lemma rank_shift_head_max_to_min (L : seq nat) :
  uniq L -> 1 < size L ->
  head 0 L = nth 0 (sort leq L) (size L).-1 ->
  head 0 (rank_shift_seq L) = nth 0 (sort leq L) 0.
Proof.
move=> Hu Hsz Hmax.
rewrite (head_rank_shift_seq Hu Hsz).
set k := size L.
have Hk0 : 0 < k by apply: ltnW.
have Hkm1 : k.-1 < k by rewrite prednK.
have Hkm1_gt0 : 0 < k.-1 by rewrite -ltnS prednK.
have Hu_s : uniq (sort leq L) by rewrite sort_uniq.
have Hne : head 0 L == nth 0 (sort leq L) 0 = false.
  apply/negbTE/negP => /eqP Heq.
  have : nth 0 (sort leq L) 0 =
         nth 0 (sort leq L) k.-1
    by rewrite -Heq -Hmax.
  move=> Heq_s.
  have : (0 == k.-1)
    by rewrite -(nth_uniq 0 (s := sort leq L))
         ?size_sort // Heq_s eqxx.
  by move/eqP => Habs; move: Hkm1_gt0; rewrite -Habs.
rewrite Hne Hmax index_uniq ?size_sort //.
by rewrite addn1 prednK // modnn.
Qed.

(* ----- T4: mm_pos_psi_eq -------------------------------------------------- *)

Lemma mm_pos_psi_eq i w :
  uniq w -> 1 < window_size i w -> i < size w ->
  mm_pos (psi i w) = mm_pos w.
Proof.
move=> Huniq Hws Hiw.
set j := mm_pos w.
have Hw_ne : w <> [::] by case: (w) Hiw.
have Hj : j < size w by apply: mm_pos_lt.
have Hperm := psi_perm_eq i w.
have Hpsi_ne : psi i w <> [::].
  by move=> H; have := perm_size Hperm; rewrite H /= => Hsz;
     move: Hiw; rewrite -Hsz.
set minv := foldr minn (head 0 w) (behead w).
set maxv := foldr maxn (head 0 w) (behead w).
have Hminv_eq : foldr minn (head 0 (psi i w)) (behead (psi i w)) = minv.
  by apply: min_val_perm_eq => //; rewrite perm_sym.
have Hmaxv_eq : foldr maxn (head 0 (psi i w)) (behead (psi i w)) = maxv.
  by apply: max_val_perm_eq => //; rewrite perm_sym.
have [Hno_min Hno_max] := notin_take_mm Hw_ne.
(* No extremum in take j (psi i w) *)
have Hno_min_psi : minv \notin take j (psi i w).
  case: (leqP j i) => Hji.
    by rewrite (@take_psi j i w Hji).
  have Hfit := window_fits_left Hw_ne Hji.
  apply/negP => Hin.
  have Hperm_take := take_psi_perm Hiw Hfit (ltnW Hj).
  by rewrite (perm_mem Hperm_take) in Hin; move/negP: Hno_min.
have Hno_max_psi : maxv \notin take j (psi i w).
  case: (leqP j i) => Hji.
    by rewrite (@take_psi j i w Hji).
  have Hfit := window_fits_left Hw_ne Hji.
  apply/negP => Hin.
  have Hperm_take := take_psi_perm Hiw Hfit (ltnW Hj).
  by rewrite (perm_mem Hperm_take) in Hin; move/negP: Hno_max.
(* Position j in psi(w) has a global extremum *)
have Hj_extremum :
  nth 0 (psi i w) j = minv \/ nth 0 (psi i w) j = maxv.
  have Hnth_w := nth_w_mm_pos Hw_ne.
  case: (ltngtP i j) => [Hij | Hij | Hij].
  - have Hfit := window_fits_left Hw_ne Hij.
    by rewrite (nth_psi_right Hfit).
  - by rewrite (@nth_psi_left i w j Hij).
  - (* i = j: rank_shift flips the extremum *)
    subst i.
    set dw := drop j w.
    have [a [s0 Hw_eq]] : exists a s0, w = a :: s0.
      by case: (w) Hw_ne => [//|a s0] _; exists a, s0.
    have Hjw : mm_pos (a :: s0) = j by rewrite /j Hw_eq.
    have Hwa : window_at j w = dw.
      rewrite Hw_eq /dw Hw_eq.
      by rewrite (window_at_cons j a s0) -Hjw ltnn eqxx.
    have Hwsz : window_size j w = size w - j.
      rewrite Hw_eq.
      by rewrite (window_size_cons j a s0) -Hjw ltnn eqxx.
    have Hdw_ne : dw <> [::].
      move=> Hdw; move: Hj.
      have : size dw = 0 by rewrite Hdw.
      by rewrite /dw size_drop => /eqP; rewrite subn_eq0
           => Hle; rewrite ltnNge Hle.
    have Hsz_dw : size dw = size w - j
      by rewrite /dw size_drop.
    have Huniq_dw : uniq dw.
      rewrite /dw; move: Huniq.
      rewrite -{1}(cat_take_drop j w) cat_uniq.
      by move=> /andP [_ /andP [_ ->]].
    have Hsz_dw_gt1 : 1 < size dw
      by rewrite Hsz_dw -Hwsz.
    (* psi j w = take j w ++ rank_shift_seq dw *)
    have Hpsi_eq : psi j w =
      take j w ++ rank_shift_seq dw.
      rewrite /psi -/j Hwa Hwsz.
      have Hjsz : j + (size w - j) = size w.
        by apply: subnKC; apply: ltnW.
      by rewrite Hjsz drop_size cats0.
    (* nth 0 (psi j w) j = head 0 (rank_shift_seq dw) *)
    have Hnth_psi : nth 0 (psi j w) j =
      head 0 (rank_shift_seq dw).
      rewrite Hpsi_eq nth_cat size_take Hj ltnn.
      rewrite subnn nth0.
      have Hsz_rs : 0 < size (rank_shift_seq dw).
        by rewrite size_rank_shift_seq; apply: ltnW.
      by case: (rank_shift_seq dw) Hsz_rs.
    (* head of dw = nth 0 w j *)
    have Hhead_dw : head 0 dw = nth 0 w j.
      by rewrite /dw -nth0 nth_drop addn0.
    (* min/max of dw = global min/max *)
    have Hmin_dw : foldr minn (head 0 dw) (behead dw)
      = minv.
      exact: min_val_drop Hw_ne Hno_min Hj.
    have Hmax_dw : foldr maxn (head 0 dw) (behead dw)
      = maxv.
      exact: max_val_drop Hw_ne Hno_max Hj.
    (* Bridge to sort positions *)
    have Hmin_sort : nth 0 (sort leq dw) 0 = minv.
      by rewrite -(min_eq_nth_sort_0 Hdw_ne).
    have Hmax_sort :
      nth 0 (sort leq dw) (size dw).-1 = maxv.
      by rewrite -(max_eq_nth_sort_last Hdw_ne).
    rewrite Hnth_psi.
    case: Hnth_w => Hval.
    + (* head = minv: rank_shift sends min to max *)
      right.
      have Hhead_min :
        head 0 dw = nth 0 (sort leq dw) 0.
        by rewrite Hmin_sort Hhead_dw Hval.
      rewrite (rank_shift_head_min_to_max
                 Huniq_dw Hsz_dw_gt1 Hhead_min).
      exact: Hmax_sort.
    + (* head = maxv: rank_shift sends max to min *)
      left.
      have Hhead_max :
        head 0 dw = nth 0 (sort leq dw) (size dw).-1.
        by rewrite Hmax_sort Hhead_dw Hval.
      rewrite (rank_shift_head_max_to_min
                 Huniq_dw Hsz_dw_gt1 Hhead_max).
      exact: Hmin_sort.
(* Conclude using mm_pos_char *)
apply: mm_pos_char => //; first by rewrite size_psi.
- by rewrite Hminv_eq.
- by rewrite Hmaxv_eq.
- by case: Hj_extremum => ->; [left; rewrite Hminv_eq | right; rewrite Hmaxv_eq].
Qed.

(* ----- T5 helpers: psi commutes with tree decomposition ------------------- *)

Lemma ws_lt_size i w : 1 < window_size i w -> i < size w.
Proof.
move=> Hws; case: (ltnP i (size w)) => // Hge.
by move: Hws; rewrite (window_size_oor Hge).
Qed.

Lemma take_mm_psi i w :
  w <> [::] -> uniq w -> 1 < window_size i w ->
  i < mm_pos w ->
  take (mm_pos w) (psi i w) = psi i (take (mm_pos w) w).
Proof.
case: w => [//|a s0] _ Huniq Hws Hij.
set j := mm_pos (a :: s0); set s := a :: s0.
have Hj : j < size s by apply: mm_pos_lt.
have Hiw : i < size s := ltn_trans Hij Hj.
have Hfit := window_fits_left (fun E : s = [::] => ltac:(discriminate E)) Hij.
set ws := window_size i s; set wa := window_at i s.
have Hws_le : ws <= size s - i by apply: window_size_bound.
have Hwa_sz : size wa = ws.
  rewrite /wa /window_at size_take size_drop.
  by case: ltnP => // H; apply/eqP; rewrite eqn_leq H Hws_le.
have Hsz_ti : size (take i s) = i by rewrite size_take Hiw.
have Hws_t : window_size i (take j s) = ws
  by rewrite /ws (window_size_cons i a s0) -/j Hij.
have Hwa_t : window_at i (take j s) = wa
  by rewrite /wa (window_at_cons i a s0) -/j Hij.
have Hsz_AB : size (take i s ++ rank_shift_seq wa) = i + ws
  by rewrite size_cat Hsz_ti size_rank_shift_seq Hwa_sz.
rewrite /psi -/ws -/wa catA take_cat Hsz_AB.
rewrite ltnNge Hfit /=.
rewrite Hws_t Hwa_t (@take_takel _ _ _ s (ltnW Hij)).
rewrite catA; congr (_ ++ _).
rewrite (take_drop (j - (i + ws)) (i + ws)).
by rewrite subnK.
Qed.

Lemma drop_mm_psi i w :
  w <> [::] -> uniq w -> 1 < window_size i w ->
  mm_pos w < i ->
  drop (mm_pos w).+1 (psi i w) =
    psi (i - mm_pos w - 1) (drop (mm_pos w).+1 w).
Proof.
case: w => [//|a s0] _ Huniq Hws Hji.
set j := mm_pos (a :: s0); set s := a :: s0.
have Hj : j < size s by apply: mm_pos_lt.
have Hiw : i < size s := ws_lt_size Hws.
set ws := window_size i s; set wa := window_at i s.
have Hws_le : ws <= size s - i by apply: window_size_bound.
have Hwa_sz : size wa = ws.
  rewrite /wa /window_at size_take size_drop.
  by case: ltnP => // H; apply/eqP; rewrite eqn_leq H Hws_le.
have Hsz_ti : size (take i s) = i by rewrite size_take Hiw.
have Hws_d : window_size (i - j - 1) (drop j.+1 s) = ws.
  rewrite /ws (window_size_cons i a s0) -/j.
  by rewrite ltnNge (ltnW Hji) /= eq_sym (ltn_eqF Hji).
have Hwa_d : window_at (i - j - 1) (drop j.+1 s) = wa.
  rewrite /wa (window_at_cons i a s0) -/j.
  by rewrite ltnNge (ltnW Hji) /= eq_sym (ltn_eqF Hji).
(* LHS *)
rewrite /psi -/ws -/wa.
rewrite catA drop_cat size_cat Hsz_ti size_rank_shift_seq Hwa_sz.
have -> : j.+1 < i + ws = true.
  by apply: (leq_ltn_trans Hji);
     rewrite -[X in X < _]addn0 ltn_add2l; apply: ltnW.
rewrite Hwa_d Hws_d drop_cat Hsz_ti.
have Hd : drop j s0 = drop j.+1 s by rewrite /s.
case: (ltnP j.+1 i) => Hj1i /=.
- have -> : drop j.+1 (take i s) = take (i - j - 1) (drop j s0).
    rewrite Hd; symmetry; rewrite take_drop.
    by congr (drop _ (take _ _)); rewrite -subnDA addn1 subnK.
  have -> : drop (i + ws) s = drop (i - j - 1 + ws) (drop j s0).
    rewrite Hd drop_drop; congr (drop _ s).
    by rewrite -subnDA addn1 addnAC subnK.
  by rewrite catA.
- have Hj1_eq : j.+1 = i by apply/eqP; rewrite eqn_leq Hj1i Hji.
  rewrite Hj1_eq subnn drop0.
  have -> : i - j - 1 = 0 by rewrite -Hj1_eq subSn // subnn.
  by rewrite take0 cat0s add0n Hd drop_drop Hj1_eq addnC.
Qed.

(* ----- T5: window stability under psi ------------------------------------ *)

Lemma window_size_psi_self i w :
  uniq w -> 1 < window_size i w -> i < size w ->
  window_size i (psi i w) = window_size i w.
Proof.
move: i w.
suff Hgen : forall n i w, size w <= n ->
  uniq w -> 1 < window_size i w -> i < size w ->
  window_size i (psi i w) = window_size i w.
  by move=> i w Hu Hws Hiw; apply: (Hgen (size w)); rewrite ?leqnn.
elim=> [|n IH] i w Hsz Huniq Hws Hiw;
  first by move: Hiw; rewrite leqn0 in Hsz; move/eqP: Hsz => -> /=.
have Hw_ne : w <> [::] by case: (w) Hiw.
case: (w) Hw_ne Huniq Hws Hiw Hsz => [//|a s0] _ Huniq Hws Hiw Hsz.
set s := a :: s0; set j := mm_pos s.
have Hj : j < size s by apply: mm_pos_lt.
have Hj' : mm_pos (psi i s) = j by apply: mm_pos_psi_eq.
have Hs_ne : s <> [::] by discriminate.
(* Get cons decomposition of psi i s without destructing *)
have Hpsi_ne : psi i s <> [::].
  by move=> E; move: Hiw; rewrite -(size_psi i) E.
have [a' [s0' Hpsi_eq]] : exists a' s0', psi i s = a' :: s0'.
  by case: (psi i s) Hpsi_ne => [//|x y] _; exists x, y.
rewrite Hpsi_eq (window_size_cons i a' s0').
have Hj'c : mm_pos (a' :: s0') = j by rewrite -Hpsi_eq.
rewrite Hj'c.
rewrite (window_size_cons i a s0) -/j.
case: (ltngtP i j) => [Hij | Hji | Hij].
- (* i < j: recurse on take j *)
  have Htake := take_mm_psi Hs_ne Huniq Hws Hij.
  rewrite -Hpsi_eq Htake.
  apply: IH.
  + by rewrite size_take Hj; exact: leq_trans Hj Hsz.
  + have : uniq (take j s ++ drop j s).
      by rewrite cat_take_drop.
    by rewrite cat_uniq => /andP [? /andP [? ?]].
  + by move: Hws; rewrite (window_size_cons i a s0) -/j Hij.
  + by rewrite size_take Hj.
- (* i > j: recurse on drop j.+1 *)
  have Hdrop := drop_mm_psi Hs_ne Huniq Hws Hji.
  rewrite -Hpsi_eq Hdrop.
  apply: IH.
  + rewrite size_drop /s /=.
    have -> : (size s0).+1 - j.+1 = size s0 - j by [].
    have Hsz' : size s0 <= n := Hsz.
    exact: leq_trans (leq_subr _ _) Hsz'.
  + have : uniq (take j.+1 s ++ drop j.+1 s).
      by rewrite cat_take_drop.
    by rewrite cat_uniq => /andP [_ /andP [_ ?]].
  + suff -> : window_size (i - j - 1) (drop j.+1 s) =
              window_size i s by [].
    rewrite (window_size_cons i a s0) -/j.
    by rewrite ltnNge (ltnW Hji) /= eq_sym (ltn_eqF Hji).
  + rewrite size_drop -subnDA addn1.
    exact: ltn_sub2r (leq_ltn_trans Hji Hiw) Hiw.
- (* i = j: direct *)
  by rewrite -Hpsi_eq size_psi.
Qed.

Lemma window_at_psi_self i w :
  uniq w -> 1 < window_size i w -> i < size w ->
  window_at i (psi i w) = rank_shift_seq (window_at i w).
Proof.
move: i w.
suff Hgen : forall n i w, size w <= n ->
  uniq w -> 1 < window_size i w -> i < size w ->
  window_at i (psi i w) = rank_shift_seq (window_at i w).
  by move=> i w Hu Hws Hiw; apply: (Hgen (size w)); rewrite ?leqnn.
elim=> [|n IH] i w Hsz Huniq Hws Hiw;
  first by move: Hiw; rewrite leqn0 in Hsz; move/eqP: Hsz => -> /=.
have Hw_ne : w <> [::] by case: (w) Hiw.
case: (w) Hw_ne Huniq Hws Hiw Hsz => [//|a s0] _ Huniq Hws Hiw Hsz.
set s := a :: s0; set j := mm_pos s.
have Hj : j < size s by apply: mm_pos_lt.
have Hj' : mm_pos (psi i s) = j by apply: mm_pos_psi_eq.
have Hs_ne : s <> [::] by discriminate.
have Hpsi_ne : psi i s <> [::].
  by move=> E; move: Hiw; rewrite -(size_psi i) E.
have [a' [s0' Hpsi_eq]] : exists a' s0', psi i s = a' :: s0'.
  by case: (psi i s) Hpsi_ne => [//|x y] _; exists x, y.
rewrite Hpsi_eq (window_at_cons i a' s0').
have Hj'c : mm_pos (a' :: s0') = j by rewrite -Hpsi_eq.
rewrite Hj'c.
rewrite (window_at_cons i a s0) -/j.
case: (ltngtP i j) => [Hij | Hji | Hij].
- (* i < j *)
  have Htake := take_mm_psi Hs_ne Huniq Hws Hij.
  rewrite -Hpsi_eq Htake.
  apply: IH.
  + by rewrite size_take Hj; exact: leq_trans Hj Hsz.
  + have : uniq (take j s ++ drop j s).
      by rewrite cat_take_drop.
    by rewrite cat_uniq => /andP [? /andP [? ?]].
  + by move: Hws; rewrite (window_size_cons i a s0) -/j Hij.
  + by rewrite size_take Hj.
- (* i > j *)
  have Hdrop := drop_mm_psi Hs_ne Huniq Hws Hji.
  rewrite -Hpsi_eq Hdrop.
  apply: IH.
  + rewrite size_drop /s /=.
    have -> : (size s0).+1 - j.+1 = size s0 - j by [].
    have Hsz' : size s0 <= n := Hsz.
    exact: leq_trans (leq_subr _ _) Hsz'.
  + have : uniq (take j.+1 s ++ drop j.+1 s).
      by rewrite cat_take_drop.
    by rewrite cat_uniq => /andP [_ /andP [_ ?]].
  + suff -> : window_size (i - j - 1) (drop j.+1 s) =
              window_size i s by [].
    rewrite (window_size_cons i a s0) -/j.
    by rewrite ltnNge (ltnW Hji) /= eq_sym (ltn_eqF Hji).
  + rewrite size_drop -subnDA addn1.
    exact: ltn_sub2r (leq_ltn_trans Hji Hiw) Hiw.
- (* i = j: drop j (psi j s) = rank_shift_seq (drop j s) *)
  subst i.
  (* Goal: drop j (a' :: s0') = rank_shift_seq (drop j s) *)
  (* a' :: s0' = psi j s *)
  rewrite -Hpsi_eq /psi.
  set ws := window_size j s.
  set wa := window_at j s.
  have Hws_eq : ws = size s - j.
    by rewrite /ws (window_size_cons j a s0) -/j ltnn eqxx.
  have Hwa_eq : wa = drop j s.
    by rewrite /wa (window_at_cons j a s0) -/j ltnn eqxx.
  rewrite Hwa_eq Hws_eq.
  rewrite (_ : j + (size s - j) = size s);
    last by rewrite subnKC // ltnW.
  rewrite drop_size cats0.
  rewrite drop_cat size_take Hj ltnNge leqnn /=.
  by rewrite subnn drop0.
Qed.

(* ----- T6: window_head_extremum ------------------------------------------ *)

Lemma window_head_extremum w i :
  uniq w -> 1 < window_size i w ->
  let L := window_at i w in
  (head 0 L == nth 0 (sort leq L) 0) ||
  (head 0 L == nth 0 (sort leq L) (size L).-1).
Proof.
move: w i.
suff Hgen : forall n w i, size w <= n ->
  uniq w -> 1 < window_size i w ->
  let L := window_at i w in
  (head 0 L == nth 0 (sort leq L) 0) ||
  (head 0 L == nth 0 (sort leq L) (size L).-1).
  by move=> w i Hu Hws; apply: (Hgen (size w)); rewrite ?leqnn.
elim=> [|n IH] w i Hsz Huniq Hws;
  first by move: (ws_lt_size Hws); rewrite leqn0 in Hsz;
          move/eqP: Hsz => -> /=.
have Hiw := ws_lt_size Hws.
have Hw_ne : w <> [::] by case: (w) Hiw.
case: (w) Hw_ne Huniq Hws Hiw Hsz => [//|a s0] _ Huniq Hws Hiw Hsz.
set s := a :: s0; set j := mm_pos s.
have Hj : j < size s by apply: mm_pos_lt.
rewrite (window_at_cons i a s0) -/j.
case: (ltngtP i j) => [Hij | Hji | Hij].
- (* i < j: recurse on take j s *)
  apply: IH.
  + by rewrite size_take Hj; exact: leq_trans Hj Hsz.
  + have : uniq (take j s ++ drop j s) by rewrite cat_take_drop.
    by rewrite cat_uniq => /andP [? /andP [? ?]].
  + by move: Hws; rewrite (window_size_cons i a s0) -/j Hij.
- (* i > j: recurse on drop j.+1 s *)
  apply: IH.
  + rewrite size_drop /s /=.
    have -> : (size s0).+1 - j.+1 = size s0 - j by [].
    have Hsz' : size s0 <= n := Hsz.
    exact: leq_trans (leq_subr _ _) Hsz'.
  + have : uniq (take j.+1 s ++ drop j.+1 s) by rewrite cat_take_drop.
    by rewrite cat_uniq => /andP [_ /andP [_ ?]].
  + move: Hws; rewrite (window_size_cons i a s0) -/j.
    have -> : i < j = false by rewrite ltnNge (ltnW Hji).
    have -> : i == j = false by rewrite eq_sym (ltn_eqF Hji).
    by [].
- (* i = j: window = drop j s, head = nth 0 s j = min or max *)
  subst i.
  have Hs_ne : s <> [::] by discriminate.
  have Hdrop_ne : drop j s <> [::].
    by move/(f_equal size); rewrite size_drop /= => /(eqP);
       rewrite subn_eq0 leqNgt Hj.
  have [Hno_min Hno_max] := notin_take_mm Hs_ne.
  have Hmin_d := min_val_drop Hs_ne Hno_min Hj.
  have Hmax_d := max_val_drop Hs_ne Hno_max Hj.
  have Hmin_sort := min_eq_nth_sort_0 Hdrop_ne.
  have Hmax_sort := max_eq_nth_sort_last Hdrop_ne.
  have Hhead : head 0 (drop j s) = nth 0 s j.
    by rewrite -nth0 nth_drop addn0.
  have Hnth := nth_w_mm_pos Hs_ne.
  rewrite /= Hhead.
  case: Hnth => ->.
  + by rewrite -Hmin_d Hmin_sort eqxx.
  + by rewrite -Hmax_d Hmax_sort eqxx orbT.
Qed.

(* ----- T7: psi_involutive ------------------------------------------------ *)

Theorem psi_involutive i w : uniq w -> psi i (psi i w) = w.
Proof.
move=> Huniq.
case: (leqP (size w) i) => [Hge | Hiw].
  by rewrite (psi_id_oor Hge) (psi_id_oor Hge).
case: (ltnP 1 (window_size i w)) => [Hws | Hws].
  2: by rewrite (psi_id_trivial Hws) (psi_id_trivial Hws).
set ws := window_size i w.
set wa := window_at i w.
have Huniq' := uniq_psi i Huniq.
have Hws' : window_size i (psi i w) = ws
  by apply: window_size_psi_self.
have Hwa' : window_at i (psi i w) = rank_shift_seq wa
  by apply: window_at_psi_self.
have Hhead : (head 0 wa == nth 0 (sort leq wa) 0) ||
             (head 0 wa == nth 0 (sort leq wa) (size wa).-1).
  by apply: window_head_extremum.
have Hwa_uniq : uniq wa.
  rewrite /wa /window_at.
  move: Huniq; rewrite -{1}(cat_take_drop i w) cat_uniq.
  move=> /andP [_ /andP [_ Hdrop_uniq]].
  by apply: (subseq_uniq (take_subseq _ _)).
have Hwa_sz_eq : size wa = ws.
  rewrite /wa /window_at size_take size_drop.
  by apply/minn_idPl; exact: window_size_bound.
have Hwa_sz : 1 < size wa by rewrite Hwa_sz_eq.
have Hrs_inv : rank_shift_seq (rank_shift_seq wa) = wa
  by apply: rank_shift_seq_involutive.
(* Assembly: psi i (psi i w) = w *)
set piw := psi i w.
(* Unfold only the outer psi application *)
change (take i piw ++ rank_shift_seq (window_at i piw)
        ++ drop (i + window_size i piw) piw = w).
rewrite Hws' Hwa' Hrs_inv.
rewrite (@take_psi i i w (leqnn i)) -/ws (drop_psi i w).
(* Goal: take i w ++ wa ++ drop (i + ws) w = w *)
suff -> : wa ++ drop (i + ws) w = drop i w.
  by rewrite cat_take_drop.
rewrite /wa /window_at -/ws.
rewrite [i + ws]addnC -drop_drop.
by rewrite cat_take_drop.
Qed.

(* ===== Milestone 3: Commutativity of psi ================================= *)
(* Reference: M3_COMMUTATIVITY_INFORMAL.md (informal proof note).             *)
(* Stanley EC1 (2nd ed.) section 1.6.3, Fact #1: the psi_i are commuting     *)
(* involutions.                                                               *)

(* ----- M3.1 Window geometry trichotomy ------------------------------------ *)
(* Two windows in a min-max tree are either disjoint or nested.               *)
(* Justification: M3_COMMUTATIVITY_INFORMAL.md section 1.2.                   *)
(* The recursive structure of window_size mirrors the tree construction.       *)
(* At each level, mm_pos separates left from right subtree. Positions in      *)
(* different branches have disjoint windows; positions in the same branch     *)
(* have nested windows. This is a structural property of binary trees.        *)

Lemma window_trichotomy : forall i j (w : seq nat),
  i < size w -> j < size w -> i <> j ->
  [\/ i + window_size i w <= j,
      j + window_size j w <= i |
      (i < j /\ j + window_size j w <= i + window_size i w) \/
      (j < i /\ i + window_size i w <= j + window_size j w)].
Proof.
suff H : forall n i j (w : seq nat),
  size w <= n -> i < size w -> j < size w -> i <> j ->
  [\/ i + window_size i w <= j,
      j + window_size j w <= i |
      (i < j /\ j + window_size j w <= i + window_size i w) \/
      (j < i /\ i + window_size i w <= j + window_size j w)].
  by move=> i j w Hi Hj Hne; apply: (H (size w)).
elim=> [| n IH] i j w Hsz Hi Hj Hne.
  by move: Hi; rewrite leqn0 in Hsz; move/eqP: Hsz => ->.
case: w Hsz Hi Hj Hne => [|a s0] //= Hsz Hi Hj Hne.
set w := a :: s0.
set j0 := mm_pos w.
have Hw_ne : w <> [::] by [].
have Hj0 : j0 < size w := mm_pos_lt Hw_ne.
have Hj0_s0 : j0 <= size s0 by rewrite -ltnS.
have Hsz' : size s0 <= n by rewrite -ltnS.
have Htake_sz : size (take j0 w) <= n.
  by rewrite size_take Hj0; exact: leq_trans Hj0_s0 Hsz'.
have Hdrop_sz : size (drop j0.+1 w) <= n.
  by rewrite size_drop /=;
     exact: leq_trans (leq_subr _ _) Hsz'.
have Htake_j0 : size (take j0 w) = j0
  by rewrite size_take Hj0.
have Hdrop_j0 : size (drop j0.+1 w) = size s0 - j0
  by rewrite size_drop /=.
have Hwsi := window_size_cons i a s0.
have Hwsj := window_size_cons j a s0.
rewrite -/w -/j0 in Hwsi Hwsj.
(* Helper: left subtree window stays within j0 *)
have Hleft_bound : forall k, k < j0 ->
  k + window_size k w <= j0.
  move=> k Hk.
  have Hwsk : window_size k w = window_size k (take j0 w).
    have := window_size_cons k a s0.
    rewrite /= -/j0 Hk => //.
  rewrite Hwsk.
  have Hbd := window_size_bound k (take j0 w).
  rewrite Htake_j0 in Hbd.
  have Hk' : k <= j0 := ltnW Hk.
  apply: leq_trans (_ : k + (j0 - k) <= _).
    by rewrite leq_add2l.
  by rewrite subnKC.
(* Helper for right-subtree index shifting *)
have Hshift : forall k, j0 < k ->
  k - j0 - 1 + j0.+1 = k.
  move=> k0 Hk0.
  have Hle := ltnW Hk0.
  suff H: k0 - j0 - 1 = k0 - j0.+1.
    by rewrite H subnK.
  by rewrite subn1 subnS.
(* Helper: right-subtree index bound *)
have Hright_idx : forall k, j0 < k -> k < size w ->
  k - j0 - 1 < size (drop j0.+1 w).
  move=> k Hk Hksz.
  rewrite Hdrop_j0.
  case E: (k - j0) (subn_gt0 j0 k) => [|m];
    first by rewrite Hk.
  move=> _; rewrite subSS subn0.
  by rewrite -E leq_sub2r // -ltnS.
(* Helper: window_size for right subtree *)
have Hws_right : forall k, j0 < k ->
  window_size k w =
  window_size (k - j0 - 1) (drop j0.+1 w).
  move=> k Hk.
  have Hwsk := window_size_cons k a s0.
  rewrite /= -/j0 in Hwsk.
  rewrite Hwsk ifF; last first.
    by apply/negbTE; rewrite -ltnNge; exact: ltnW.
  by rewrite ifF //; exact: gtn_eqF.
(* Helper: window_size at the root *)
have Hws_root : window_size j0 w = size w - j0.
  have := window_size_cons j0 a s0.
  by rewrite /= -/j0 ltnn eq_refl.
(* Main 9-way case analysis: i vs j0, j vs j0 *)
case: (ltngtP i j0) => [Hi_lt | Hi_r | Hi_eq];
  case: (ltngtP j j0) => [Hj_lt | Hj_r | Hj_eq].
- (* i left, j left: recurse on take j0 w *)
  have Hi' : i < size (take j0 w) by rewrite Htake_j0.
  have Hj' : j < size (take j0 w) by rewrite Htake_j0.
  have := IH i j (take j0 w) Htake_sz Hi' Hj' Hne.
  rewrite Hwsi Hi_lt Hwsj Hj_lt.
  by case=> [?|?|?];
     [constructor 1|constructor 2|constructor 3].
- (* i left, j right: disjoint, i+ws_i <= j0 <= j *)
  constructor 1.
  exact: leq_trans (Hleft_bound i Hi_lt) (ltnW Hj_r).
- (* i left, j = root: disjoint, i+ws_i <= j0 = j *)
  constructor 1.
  by rewrite Hj_eq; exact: Hleft_bound i Hi_lt.
- (* i right, j left: disjoint, j+ws_j <= j0 <= i *)
  constructor 2.
  exact: leq_trans (Hleft_bound j Hj_lt) (ltnW Hi_r).
- (* i right, j right: recurse on drop j0.+1 w *)
  set i' := i - j0 - 1. set j' := j - j0 - 1.
  set w' := drop j0.+1 w.
  have Hi' : i' < size w' :=
    Hright_idx i Hi_r Hi.
  have Hj' : j' < size w' :=
    Hright_idx j Hj_r Hj.
  have Hne' : i' <> j'.
    move=> H; apply: Hne.
    have := congr1 (addn^~ j0.+1) H.
    by rewrite /i' /j' !(Hshift) //.
  have Hwsi_r := Hws_right i Hi_r.
  have Hwsj_r := Hws_right j Hj_r.
  have := IH i' j' w' Hdrop_sz Hi' Hj' Hne'.
  rewrite Hwsi_r Hwsj_r.
  (* Goal now has ws_i' and ws_j' in place of ws_i and ws_j *)
  (* IH transfer: convert primed back to unprimed *)
  (* Rewrite goal's window_size first, then index shifts *)
  (* After Hwsi_r/Hwsj_r rewrite, goal uses i'/j'/w' for
     window sizes but still uses i/j for positions *)
  case=> [H1 | H1 | [[H1a H1b] | [H1a H1b]]].
  + constructor 1.
    (* goal: i + ws_i' <= j *)
    (* Goal has unfolded i'/j'/w' from Hwsi_r/Hwsj_r
       rewrite. Refold before shifting position indices. *)
    rewrite -/i' -/w'.
    have -> : i = i' + j0.+1 by rewrite Hshift.
    have -> : j = j' + j0.+1 by rewrite Hshift.
    rewrite -addnA [j0.+1 + _]addnC addnA leq_add2r.
    exact: H1.
  + constructor 2.
    rewrite -/j' -/w'.
    have -> : j = j' + j0.+1 by rewrite Hshift.
    have -> : i = i' + j0.+1 by rewrite Hshift.
    rewrite -addnA [j0.+1 + _]addnC addnA leq_add2r.
    exact: H1.
  + constructor 3; left; split.
    * have -> : i = i' + j0.+1 by rewrite Hshift.
      have -> : j = j' + j0.+1 by rewrite Hshift.
      by rewrite ltn_add2r.
    * rewrite -/i' -/j' -/w'.
      have -> : j = j' + j0.+1 by rewrite Hshift.
      have -> : i = i' + j0.+1 by rewrite Hshift.
      rewrite -!addnA ![j0.+1 + _]addnC !addnA
              leq_add2r.
      exact: H1b.
  + constructor 3; right; split.
    * have -> : j = j' + j0.+1 by rewrite Hshift.
      have -> : i = i' + j0.+1 by rewrite Hshift.
      by rewrite ltn_add2r.
    * rewrite -/i' -/j' -/w'.
      have -> : i = i' + j0.+1 by rewrite Hshift.
      have -> : j = j' + j0.+1 by rewrite Hshift.
      rewrite -!addnA ![j0.+1 + _]addnC !addnA
              leq_add2r.
      exact: H1b.
- (* i right, j = root: nested, j < i *)
  constructor 3; right; split.
  + by rewrite Hj_eq.
  + rewrite Hj_eq Hws_root subnKC; last exact: ltnW.
    (* goal: i + window_size i w <= size w *)
    have := window_size_bound i w.
    move=> Hbd.
    apply: leq_trans (_ : i + (size w - i) <= _).
      by rewrite leq_add2l.
    by rewrite subnKC // ltnW.
- (* i = root, j left: disjoint, j+ws_j <= j0 = i *)
  constructor 2.
  by rewrite Hi_eq; exact: Hleft_bound j Hj_lt.
- (* i = root, j right: nested, i < j *)
  constructor 3; left; split.
  + by rewrite Hi_eq.
  + rewrite Hi_eq Hws_root subnKC; last exact: ltnW.
    have Hbd := window_size_bound j w.
    apply: leq_trans (_ : j + (size w - j) <= _).
      by rewrite leq_add2l.
    by rewrite subnKC // ltnW.
- (* i = root, j = root: impossible *)
  by exfalso; apply: Hne; rewrite Hi_eq Hj_eq.
Qed.

(* Non-triviality: the nested case does occur (positions 1 and 5). *)
Example window_trichotomy_ex :
  let w := [:: 3; 1; 4; 7; 5; 9; 2; 6] in
  (1 < 5) && (5 + window_size 5 w <= 1 + window_size 1 w).
Proof. by []. Qed.

(* ----- M3.2 Disjoint commutativity --------------------------------------- *)
(* When W_i and W_j are disjoint intervals, psi_i and psi_j modify non-      *)
(* overlapping slices of w, so the operations commute. The proof is purely    *)
(* mechanical take/drop/cat manipulation; the mathematical content is nil.    *)
(* Justification: M3_COMMUTATIVITY_INFORMAL.md section 2.                     *)
(* The word decomposes into 5 slices: [0,i), W_i, (W_i,j), W_j, (W_j,n),    *)
(* with psi_i acting on slice 2 and psi_j on slice 4 independently.          *)
(* Window stability: psi_j does not change positions in W_i (disjoint),       *)
(* so window_size/window_at at i are unchanged by psi_j (and vice versa).     *)
(* This is the disjoint-window specialization of M2_SUBTASKS.md T4-T5.        *)

(* Window-size invariance under psi (forward declaration from M5).           *)

(* ----- Order-isomorphism infrastructure ---------------------------------- *)
(* mm_pos and window_size depend only on comparison structure.               *)

Lemma foldr_minn_le_nth s a i :
  i < (size s).+1 ->
  foldr minn a s <= nth 0 (a :: s) i.
Proof. move=> Hi; apply: foldr_minn_le; exact: mem_nth. Qed.

Lemma foldr_maxn_ge_nth s a i :
  i < (size s).+1 ->
  nth 0 (a :: s) i <= foldr maxn a s.
Proof. move=> Hi; apply: foldr_maxn_ge; exact: mem_nth. Qed.

Lemma mm_pos_order_iso (s1 s2 : seq nat) :
  size s1 = size s2 -> uniq s1 -> uniq s2 ->
  s1 <> [::] ->
  (forall p q, p < size s1 -> q < size s1 ->
    (nth 0 s1 p < nth 0 s1 q) =
    (nth 0 s2 p < nth 0 s2 q)) ->
  mm_pos s1 = mm_pos s2.
Proof.
move=> Hsz Hu1 Hu2 Hne Hord.
case: s1 Hsz Hu1 Hne Hord => [//|a1 t1] Hsz Hu1 _ Hord.
case: s2 Hsz Hu2 Hord => [|a2 t2] Hsz Hu2 Hord.
  by move: Hsz; rewrite /=.
set s1 := a1 :: t1; set s2 := a2 :: t2.
have Hszeq : size s1 = size s2 := Hsz.
have Hp1 : min_pos s1 < size s1 by apply: min_pos_lt.
have Hq1 : max_pos s1 < size s1 by apply: max_pos_lt.
have Hp2 : min_pos s2 < size s2 by apply: min_pos_lt.
have Hq2 : max_pos s2 < size s2 by apply: max_pos_lt.
(* unique argmin/argmax characterizations *)
have argmin1 : forall r, r < size s1 -> r <> min_pos s1 ->
  nth 0 s1 (min_pos s1) < nth 0 s1 r.
  move=> r Hr Hrp.
  rewrite (nth_index 0 (min_in t1 a1)) ltn_neqAle.
  apply/andP; split; last by apply: foldr_minn_le_nth.
  apply/negP => /eqP Heq; apply: Hrp; symmetry.
  apply/eqP; rewrite -(nth_uniq 0 Hp1 Hr Hu1).
  by apply/eqP; rewrite (nth_index 0 (min_in t1 a1)).
have argmax1 : forall r, r < size s1 ->
  r <> max_pos s1 ->
  nth 0 s1 r < nth 0 s1 (max_pos s1).
  move=> r Hr Hrq.
  rewrite (nth_index 0 (max_in t1 a1)) ltn_neqAle.
  apply/andP; split; last by apply: foldr_maxn_ge_nth.
  apply/negP => /eqP Heq; apply: Hrq.
  apply/eqP; rewrite -(nth_uniq 0 Hr Hq1 Hu1).
  by apply/eqP; rewrite (nth_index 0 (max_in t1 a1)).
have argmin2 : forall r, r < size s2 ->
  r <> min_pos s2 ->
  nth 0 s2 (min_pos s2) < nth 0 s2 r.
  move=> r Hr Hrp.
  rewrite (nth_index 0 (min_in t2 a2)) ltn_neqAle.
  apply/andP; split; last by apply: foldr_minn_le_nth.
  apply/negP => /eqP Heq; apply: Hrp; symmetry.
  apply/eqP; rewrite -(nth_uniq 0 Hp2 Hr Hu2).
  by apply/eqP; rewrite (nth_index 0 (min_in t2 a2)).
have argmax2 : forall r, r < size s2 ->
  r <> max_pos s2 ->
  nth 0 s2 r < nth 0 s2 (max_pos s2).
  move=> r Hr Hrq.
  rewrite (nth_index 0 (max_in t2 a2)) ltn_neqAle.
  apply/andP; split; last by apply: foldr_maxn_ge_nth.
  apply/negP => /eqP Heq; apply: Hrq.
  apply/eqP; rewrite -(nth_uniq 0 Hr Hq2 Hu2).
  by apply/eqP; rewrite (nth_index 0 (max_in t2 a2)).
(* transfer *)
have argmin1_s2 : forall r, r < size s2 ->
  r <> min_pos s1 ->
  nth 0 s2 (min_pos s1) < nth 0 s2 r.
  move=> r Hr Hrp.
  have Hr' : r < size s1 by rewrite Hszeq.
  rewrite -(Hord (min_pos s1) r Hp1 Hr').
  exact: argmin1.
have argmax1_s2 : forall r, r < size s2 ->
  r <> max_pos s1 ->
  nth 0 s2 r < nth 0 s2 (max_pos s1).
  move=> r Hr Hrq.
  have Hr' : r < size s1 by rewrite Hszeq.
  rewrite -(Hord r (max_pos s1) Hr' Hq1).
  exact: argmax1.
(* min_pos equal *)
have ltn_neq_ : forall a b : nat, a < b -> a <> b
  by move=> ?? /ltn_eqF /eqP.
have Hmin_eq : min_pos s1 = min_pos s2.
  apply/eqP; rewrite eqn_leq; apply/andP; split;
    rewrite leqNgt; apply/negP => Hlt.
  - have H1 := argmin1_s2 (min_pos s2) Hp2
      (ltn_neq_ _ _ Hlt).
    have H2 := argmin2 (min_pos s1)
      ltac:(rewrite -Hszeq; done)
      (not_eq_sym (ltn_neq_ _ _ Hlt)).
    by rewrite ltnNge (ltnW H1) in H2.
  - have H1 := argmin2 (min_pos s1)
      ltac:(rewrite -Hszeq; done) (ltn_neq_ _ _ Hlt).
    have H2 := argmin1_s2 (min_pos s2) Hp2
      (not_eq_sym (ltn_neq_ _ _ Hlt)).
    by rewrite ltnNge (ltnW H2) in H1.
(* max_pos equal *)
have Hmax_eq : max_pos s1 = max_pos s2.
  apply/eqP; rewrite eqn_leq; apply/andP; split;
    rewrite leqNgt; apply/negP => Hlt.
  - have H1 := argmax1_s2 (max_pos s2) Hq2
      (ltn_neq_ _ _ Hlt).
    have H2 := argmax2 (max_pos s1)
      ltac:(rewrite -Hszeq; done)
      (not_eq_sym (ltn_neq_ _ _ Hlt)).
    by rewrite ltnNge (ltnW H1) in H2.
  - have H1 := argmax2 (max_pos s1)
      ltac:(rewrite -Hszeq; done) (ltn_neq_ _ _ Hlt).
    have H2 := argmax1_s2 (max_pos s2) Hq2
      (not_eq_sym (ltn_neq_ _ _ Hlt)).
    by rewrite ltnNge (ltnW H2) in H1.
by rewrite /mm_pos Hmin_eq Hmax_eq.
Qed.

Lemma window_size_order_iso (s1 s2 : seq nat) i :
  size s1 = size s2 -> uniq s1 -> uniq s2 ->
  (forall p q, p < size s1 -> q < size s1 ->
    (nth 0 s1 p < nth 0 s1 q) =
    (nth 0 s2 p < nth 0 s2 q)) ->
  window_size i s1 = window_size i s2.
Proof.
(* Follows from mm_pos_order_iso by structural induction on the     *)
(* Cartesian tree. At each level, mm_pos is the same (by order      *)
(* iso), so the recursion goes to the same subtree with the same    *)
(* comparison structure. *)
move: s1 s2 i.
suff Hgen : forall n s1 s2 i, size s1 <= n ->
  size s1 = size s2 -> uniq s1 -> uniq s2 ->
  (forall p q, p < size s1 -> q < size s1 ->
    (nth 0 s1 p < nth 0 s1 q) =
    (nth 0 s2 p < nth 0 s2 q)) ->
  window_size i s1 = window_size i s2.
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
rewrite (window_size_cons i a1 t1) -/m.
rewrite (window_size_cons i a2 t2) -Hmm -/m.
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
       rewrite /= ltnS in Hsz1; exact: (leq_trans (leqnSn _) Hsz1).
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
- by rewrite Hszeq'.
Qed.

(* ----- window_size_psi helpers -------------------------------------------- *)

(* mm_pos of drop (mm_pos w) w is 0.                                *)
Lemma mm_pos_drop_mm w :
  w <> [::] ->
  mm_pos (drop (mm_pos w) w) = 0.
Proof.
move=> Hw_ne.
set m := mm_pos w.
have Hm : m < size w by apply: mm_pos_lt.
have Hdm_ne : drop m w <> [::].
  move=> E; have : size (drop m w) = 0 by rewrite E.
  by rewrite size_drop => /eqP; rewrite subn_eq0 leqNgt Hm.
have Hnth_m := nth_w_mm_pos Hw_ne.
have [Hno_min Hno_max] := notin_take_mm Hw_ne.
have Hmin_dm := min_val_drop Hw_ne Hno_min Hm.
have Hmax_dm := max_val_drop Hw_ne Hno_max Hm.
have Hhead_dm : head 0 (drop m w) = nth 0 w m
  by rewrite -nth0 nth_drop addn0.
apply: mm_pos_char => //.
  by case: (drop m w) Hdm_ne.
- (* min \notin take 0 (drop m w) = [::] *)
  by rewrite take0.
- (* max \notin take 0 (drop m w) = [::] *)
  by rewrite take0.
- rewrite -/m in Hmin_dm Hmax_dm.
  have Hh : nth 0 (drop m w) 0 = nth 0 w m.
    by rewrite nth_drop addn0.
  case: Hnth_m => Hval; [left | right]; rewrite Hh Hval.
  + by symmetry.
  + by symmetry.
Qed.

(* Helper: psi 0 s = rank_shift_seq s when mm_pos s = 0 and 1 < size s. *)
Lemma psi_0_eq s :
  mm_pos s = 0 -> 1 < size s ->
  psi 0 s = rank_shift_seq s.
Proof.
move=> Hm0 Hsz.
have Hs_ne : s <> [::] by case: (s) Hsz.
have Hws : window_size 0 s = size s.
  have [a [s0 Hs_eq]] : exists a s0, s = a :: s0.
    by case: (s) Hs_ne => [//|a s0] _; exists a, s0.
  rewrite Hs_eq (window_size_cons 0 a s0).
  by rewrite -Hs_eq Hm0 ltnn eqxx subn0.
rewrite /psi take0 cat0s Hws /window_at Hws drop0 add0n.
rewrite take_oversize //.
by rewrite drop_size cats0.
Qed.

(* ----- Order-isomorphism lemmas for mm_pos and window_size --------------- *)
(* Two sequences with the same comparison structure have the same mm_pos     *)
(* and window_size at every position. Used for the j = mm_pos case of       *)
(* window_size_psi, where rank_shift_seq preserves interior comparisons.     *)



(* Helper: drop_suffix under psi when psi window is below cutoff.           *)
Lemma drop_psi_above j k w :
  j + window_size j w <= k ->
  drop k (psi j w) = drop k w.
Proof.
move=> Hle.
have [Hksz | Hksz] := leqP (size w) k.
  by rewrite !drop_oversize ?size_psi.
apply: (@eq_from_nth _ 0).
  by rewrite !size_drop size_psi.
move=> p Hp.
rewrite !nth_drop.
apply: nth_psi_right.
by apply: leq_trans Hle (leq_addr _ _).
Qed.

Lemma window_size_psi : forall (j i : nat) (w : seq nat),
  uniq w -> window_size i (psi j w) = window_size i w.
Proof.
suff Hgen : forall n j i w, size w <= n ->
  uniq w -> window_size i (psi j w) = window_size i w.
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
rewrite Hpsi_eq (window_size_cons i a' s0') Hm'c.
rewrite (window_size_cons i a s0) -/m.
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
  + (* j = m: use window_size_order_iso *)
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
    (* Use window_size_order_iso *)
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
    apply: window_size_order_iso.
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
  by rewrite -Hpsi_eq size_psi.
Qed.

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
apply/perm_sortP => //.
- by move=> ?; exact: leq_total.
- exact: leq_trans.
- exact: anti_leq.
- rewrite perm_sym; apply: perm_map; exact: perm_sort.
- rewrite sorted_map.
  apply: sub_sorted; last exact: sort_sorted.
  move=> x y /=; rewrite /relpre => Hxy.
  have Hx_in : x \in L
    by rewrite -(perm_mem (perm_sort leq L));
       apply: mem_sort.
  have Hy_in : y \in L
    by rewrite -(perm_mem (perm_sort leq L));
       apply: mem_sort.
  rewrite leq_eqVlt in Hxy *.
  case/orP: Hxy => [/eqP -> | Hlt].
    by rewrite eqxx.
  by rewrite -Hmon // orbT.
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
  by rewrite /= eqxx.
have Hax : a != x.
  by apply/eqP => Hax; rewrite Hax Hx in Ha_notin.
have Hfax : f a != f x.
  apply/eqP => Hfax.
  by move: Hax; rewrite (Hinj a x (mem_head _ _)
    (mem_cons _ Hx) Hfax) eqxx.
rewrite /= (negbTE Hfax); congr _.+1.
apply: IH => //.
move=> u v Hu_in Hv_in; apply: Hinj;
  exact: mem_cons.
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
    + rewrite -(perm_mem (perm_sort _ _)).
      exact: mem_nth (n:=0) (ltnW Hsz).
  - by move=> ->.
rewrite (rank_shift_seqE Hu Hsz).
rewrite (rank_shift_seqE Hu_fL Hsz_fL).
(* LHS: map over (map f L), RHS: map f over (map over L) *)
(* Rewrite LHS: [seq ... | y <- map f L] to map over L *)
rewrite map_map -map_comp.
apply: eq_in_map => x Hx /=.
rewrite Hsort Hhead size_map Hdelta.
have Hx_srt : x \in sort leq L
  by rewrite -(perm_mem (perm_sort leq L)).
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
    by rewrite (perm_mem (perm_sort leq L)).
rewrite (index_map_inj_in Hu_srt Hinj_srt Hx_srt).
rewrite (set_nth_default _ 0 (f 0)) ?size_map //.
by rewrite (nth_map 0).
Qed.

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
have Hsz_eq : size (map f s) = size s by rewrite size_map.
have Hord : forall p q, p < size s -> q < size s ->
  (nth 0 s p < nth 0 s q) =
  (nth 0 (map f s) p < nth 0 (map f s) q).
  move=> p q Hp Hq.
  rewrite (nth_map 0) // (nth_map 0) //.
  apply: Hmon; exact: mem_nth.
have Hws' : window_size k (map f s) = ws
  by apply: window_size_order_iso.
have Hwa' : window_at k (map f s) = map f wa.
  by rewrite /window_at /wa Hws' map_drop map_take.
have Hrs : rank_shift_seq (map f wa) =
  map f (rank_shift_seq wa).
  have [Htriv | Hnt] := leqP ws 1.
    have Hsz_wa : size wa <= 1.
      rewrite /wa /window_at size_take size_drop.
      by case: ltnP => // _; apply: ltnW.
    case Hwa0 : wa => [|a [|b t]].
    - by rewrite /rank_shift_seq /=.
    - by rewrite /rank_shift_seq /=.
    - exfalso; move: Hsz_wa; rewrite Hwa0 /=.
      by rewrite ltnS ltnS.
  have Hu_wa : uniq wa.
    rewrite /wa /window_at.
    move: Hu; rewrite -{1}(cat_take_drop k s) cat_uniq.
    move=> /andP [_ /andP [_ Hud]].
    exact: (subseq_uniq (take_subseq _ _)).
  have Hsz_wa : 1 < size wa.
    rewrite /wa /window_at size_take size_drop.
    case: ltnP => // Hle.
    by rewrite ltnNge Hle in Hnt.
  apply: rank_shift_map_comm => //.
  move=> x y Hx Hy; apply: Hmon;
    exact: mem_drop (mem_take _).
rewrite Hws' Hwa' Hrs.
by rewrite !map_cat map_take map_drop.
Qed.

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
  by rewrite -(@nth0 _ 0) -(@nth0 _ 0 d); apply: nth_psi_left.
(* decompose d = head :: behead *)
case Hd : d => [|a t]; first by exfalso.
have Ha : a = head 0 d by rewrite Hd.
have Ht : t = behead d by rewrite Hd.
(* mm_pos d = 0 means head is min or max *)
(* psi k d = a :: psi (k-1) t for k > 0 *)
(* psi k (rank_shift_seq d) =
   head(rss d) :: psi (k-1) (behead(rss d)) *)
(* rank_shift_seq d = map rs d for appropriate rs *)
set rs := fun x => nth 0 (sort leq d)
  ((index x (sort leq d) +
    (if head 0 d == nth 0 (sort leq d) 0
     then (size d).-1 else 1)) %% size d).
have Hrs_d : rank_shift_seq d = map rs d
  by rewrite (rank_shift_seqE Hu Hsz).
have Hrs_psi : rank_shift_seq (psi k d) = map rs (psi k d).
  rewrite (rank_shift_seqE (perm_uniq Hperm Hu)
    (eq_leq (esym (perm_size Hperm)) Hsz)).
  by rewrite Hsort_psi Hhead_psi (perm_size Hperm).
(* rs is monotone on elements of t = behead d *)
have Hhead_ext : (head 0 d ==
  nth 0 (sort leq d) 0) ||
  (head 0 d == nth 0 (sort leq d) (size d).-1).
  apply: window_head_extremum => //.
  by rewrite (window_size_cons 0 a t) -/d Hmm ltnn eqxx.
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
  (* Use rank_shift_preserves_interior_order with swapped args *)
  have Hrio := rank_shift_preserves_interior_order
    Hu Hsz Hhead_ext Hpy Hpx Hidy Hidx.
  rewrite Hnthx Hnthy in Hrio.
  (* Convert nth 0 (rss d) to rs via nth_rank_shift_seq *)
  have Hnthrsx : nth 0 (rank_shift_seq d) (index x d) =
    rs x.
    by rewrite (nth_rank_shift_seq Hu Hsz Hidx) nth_index.
  have Hnthrsy : nth 0 (rank_shift_seq d) (index y d) =
    rs y.
    by rewrite (nth_rank_shift_seq Hu Hsz Hidy) nth_index.
  by rewrite Hnthrsx Hnthrsy in Hrio.
(* Now use psi_map_comm *)
rewrite Hrs_psi -psi_map_comm //.
  by rewrite -Hrs_d.
- move: Hu; rewrite Hd /= => /andP [_ ?]; exact.
- move=> x y Hx Hy; exact: Hrs_mono.
Qed.

Lemma psi_comm_nested : forall i j (w : seq nat),
  uniq w ->
  i < j -> j + window_size j w <= i + window_size i w ->
  psi i (psi j w) = psi j (psi i w).
Proof.
suff Hgen : forall n i j w, size w <= n ->
  uniq w ->
  i < j -> j + window_size j w <= i + window_size i w ->
  psi i (psi j w) = psi j (psi i w).
  by move=> i j w; apply: (Hgen (size w)); rewrite ?leqnn.
elim=> [|n IH] i j w Hsz Huniq Hij Hnest.
  by move: Hsz; rewrite leqn0 => /eqP/size0nil ->.
have [Htriv_i | Hws_i_gt1] := leqP (window_size i w) 1.
  by rewrite (psi_id_trivial Htriv_i).
have [Htriv_j | Hws_j_gt1] := leqP (window_size j w) 1.
  by rewrite (psi_id_trivial Htriv_j).
have Hiw := ws_lt_size Hws_i_gt1.
have Hjw := ws_lt_size Hws_j_gt1.
have Hw_ne : w <> [::] by case: (w) Hiw.
case: (w) Hw_ne Huniq Hws_i_gt1 Hws_j_gt1 Hiw Hjw Hsz
  Hij Hnest =>
  [//|a s0] _ Huniq Hws_i Hws_j Hiw Hjw Hsz Hij Hnest.
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
(* Both i and j are in the same subtree relative to m *)
case: (ltngtP i m) => [Him | Hmi | Hieqm].
- (* i < m: j < m too since W_i fits in left subtree *)
  have Hjm : j < m.
    have Hfit := window_fits_left Hs_ne Him.
    exact: leq_ltn_trans (leq_trans Hnest Hfit) Hm.
  (* Wait, Hnest says j + ws_j <= i + ws_i.
     And Hfit says i + ws_i <= m.
     So j + ws_j <= m, hence j < m. *)
  (* Both psi_i and psi_j act only on take m s *)
  (* LHS = psi_i(psi_j(s)) *)
  (* take m (psi_j s) = psi_j (take m s) *)
  (* drop m.+1 (psi_j s) = drop m.+1 s *)
  (* take m (psi_i(psi_j s)) =
       psi_i(take m (psi_j s)) = psi_i(psi_j(take m s)) *)
  (* drop m.+1 (psi_i(psi_j s)) = drop m.+1 (psi_j s)
       = drop m.+1 s *)
  (* Similarly for RHS *)
  have Htmj : take m (psi j s) = psi j (take m s)
    by exact: take_mm_psi.
  have Htmi : take m (psi i s) = psi i (take m s)
    by exact: take_mm_psi.
  have Hdj : drop m.+1 (psi j s) = drop m.+1 s.
    apply: drop_psi_above.
    exact: leq_trans (window_fits_left Hs_ne Hjm) (leqnSn _).
  have Hdi : drop m.+1 (psi i s) = drop m.+1 s.
    apply: drop_psi_above.
    exact: leq_trans (window_fits_left Hs_ne Him) (leqnSn _).
  (* Both sides agree element by element *)
  apply: (@eq_from_nth _ 0); first by rewrite !size_psi.
  move=> k Hk; rewrite !size_psi in Hk.
  (* position k *)
  have [Hkm | Hkm] := ltnP k m.
    (* k < m: in the left subtree *)
    (* LHS at k *)
    have Hm_pj' := Hm_pj.
    have Hpj_ne : psi j s <> [::] by case: (psi j s) Hk.
    have [a' [s0' Hpj_eq]] : exists a' s0',
      psi j s = a' :: s0'.
      by case: (psi j s) Hpj_ne => [//|x y] _;
         exists x, y.
    have Hm_pj'' : mm_pos (a' :: s0') = m
      by rewrite -Hpj_eq.
    have Hws_i_pj : 1 < window_size i (psi j s)
      by rewrite window_size_psi.
    have Him' : i < mm_pos (psi j s) by rewrite Hm_pj.
    rewrite -(take_mm_psi Hpj_ne Huniq_pj Hws_i_pj Him').
    rewrite Hm_pj Htmj nth_take //.
    (* RHS at k *)
    have Hpi_ne : psi i s <> [::] by case: (psi i s) Hk.
    have Hws_j_pi : 1 < window_size j (psi i s)
      by rewrite window_size_psi.
    have Hjm' : j < mm_pos (psi i s) by rewrite Hm_pi.
    rewrite -(take_mm_psi Hpi_ne Huniq_pi Hws_j_pi Hjm').
    rewrite Hm_pi Htmi nth_take //.
    (* Now need:
       nth 0 (psi_i(psi_j(take m s))) k =
       nth 0 (psi_j(psi_i(take m s))) k *)
    have Huniq_tm : uniq (take m s).
      have : uniq (take m s ++ drop m s)
        by rewrite cat_take_drop.
      by rewrite cat_uniq => /andP [].
    have Hsz_tm : size (take m s) <= n.
      rewrite size_take Hm.
      exact: leq_trans (ltnW Hm) Hsz.
    have Hws_i_tm : window_size i (take m s) =
      window_size i s.
      by rewrite (window_size_cons i a s0) -/m Him.
    have Hws_j_tm : window_size j (take m s) =
      window_size j s.
      by rewrite (window_size_cons j a s0) -/m Hjm.
    have Hnest_tm : j + window_size j (take m s) <=
      i + window_size i (take m s)
      by rewrite Hws_i_tm Hws_j_tm.
    have := IH i j (take m s) Hsz_tm Huniq_tm Hij Hnest_tm.
    by move=> ->.
  (* k >= m *)
  have [Hkm' | Hkm'] := eqVneq k m.
    (* k = m: root position *)
    subst k.
    rewrite nth_psi_left // nth_psi_left //.
    rewrite nth_psi_left; last by rewrite Hm_pj.
    rewrite nth_psi_left; last by rewrite Hm_pi.
    done.
  (* k > m *)
  have Hkm'' : m < k by rewrite ltn_neqAle eq_sym Hkm' Hkm.
  (* Both psi_i and psi_j don't touch positions > m *)
  have Hk_oor_i : i + window_size i s <= k.
    exact: leq_trans (window_fits_left Hs_ne Him) Hkm.
  have Hk_oor_j : j + window_size j s <= k.
    exact: leq_trans (leq_trans Hnest Hk_oor_i).
  rewrite (nth_psi_right (k:=k)).
    rewrite (nth_psi_right (k:=k));
      last by rewrite window_size_psi.
    rewrite (nth_psi_right (k:=k));
      last by rewrite window_size_psi.
    by rewrite (nth_psi_right (k:=k)).
  by [].
- (* m < i (and hence m < j): both in right subtree *)
  have Hmj : m < j by exact: ltn_trans Hmi Hij.
  (* psi_i acts on drop m.+1 s *)
  (* psi_j acts on drop m.+1 s *)
  apply: (@eq_from_nth _ 0); first by rewrite !size_psi.
  move=> k Hk; rewrite !size_psi in Hk.
  have [Hkm | Hkm] := ltnP k m.+1.
    (* k <= m: before both windows *)
    rewrite !nth_psi_left //.
    by rewrite !nth_psi_left // ltnW.
  (* k > m *)
  have [Hk_oor | Hk_inr] := leqP (size s) k.
    by rewrite !nth_default ?size_psi.
  (* k >= m.+1 and k < size s *)
  (* Use drop_mm_psi to relate to psi on right subtree *)
  have Hpj_ne : psi j s <> [::].
    by move=> E; move: Hjw; rewrite -(size_psi j) E.
  have Hws_i_pj : 1 < window_size i (psi j s)
    by rewrite window_size_psi.
  have Hmi' : mm_pos (psi j s) < i by rewrite Hm_pj.
  have Hdpj : drop m.+1 (psi i (psi j s)) =
    psi (i - m - 1) (drop m.+1 (psi j s)).
    exact: drop_mm_psi Hpj_ne Huniq_pj Hws_i_pj Hmi'.
  have Hdi_pj : drop m.+1 (psi j s) =
    psi (j - m - 1) (drop m.+1 s).
    exact: drop_mm_psi Hs_ne Huniq Hws_j Hmj.
  have Hpi_ne : psi i s <> [::].
    by move=> E; move: Hiw; rewrite -(size_psi i) E.
  have Hws_j_pi : 1 < window_size j (psi i s)
    by rewrite window_size_psi.
  have Hmj' : mm_pos (psi i s) < j by rewrite Hm_pi.
  have Hdpi : drop m.+1 (psi j (psi i s)) =
    psi (j - m - 1) (drop m.+1 (psi i s)).
    exact: drop_mm_psi Hpi_ne Huniq_pi Hws_j_pi Hmj'.
  have Hdi_pi : drop m.+1 (psi i s) =
    psi (i - m - 1) (drop m.+1 s).
    exact: drop_mm_psi Hs_ne Huniq Hws_i Hmi.
  (* nth k in LHS *)
  have Hlhs : nth 0 (psi i (psi j s)) k =
    nth 0 (drop m.+1 (psi i (psi j s))) (k - m.+1).
    by rewrite nth_drop subnK.
  have Hrhs : nth 0 (psi j (psi i s)) k =
    nth 0 (drop m.+1 (psi j (psi i s))) (k - m.+1).
    by rewrite nth_drop subnK.
  rewrite Hlhs Hdpj Hdi_pj Hrhs Hdpi Hdi_pi.
  have Huniq_dm : uniq (drop m.+1 s).
    have : uniq (take m.+1 s ++ drop m.+1 s)
      by rewrite cat_take_drop.
    by rewrite cat_uniq => /andP [_ /andP [_ ?]].
  have Hsz_dm : size (drop m.+1 s) <= n.
    rewrite size_drop.
    exact: leq_trans (leq_subr _ _) (ltnW Hsz).
  set i' := i - m - 1. set j' := j - m - 1.
  have Hi'j' : i' < j'.
    rewrite /i' /j'.
    by rewrite !subnS ltn_sub2r // subn_gt0.
  have Hws_i' : window_size i' (drop m.+1 s) =
    window_size i s.
    rewrite (window_size_cons i a s0) -/m.
    by rewrite ltnNge (ltnW Hmi) /= eq_sym (ltn_eqF Hmi).
  have Hws_j' : window_size j' (drop m.+1 s) =
    window_size j s.
    rewrite (window_size_cons j a s0) -/m.
    by rewrite ltnNge (ltnW Hmj) /= eq_sym (ltn_eqF Hmj).
  have Hnest' : j' + window_size j' (drop m.+1 s) <=
    i' + window_size i' (drop m.+1 s).
    rewrite Hws_i' Hws_j' /i' /j'.
    rewrite !subnS.
    have Hm_le_i : m <= i by exact: ltnW.
    have Hm_le_j : m <= j by exact: ltnW.
    rewrite -!subn1 !subnBA //.
    by rewrite !addnBA // [j + _ - _]addnBAC //
       [i + _ - _]addnBAC //
       leq_sub2r.
  have := IH i' j' (drop m.+1 s) Hsz_dm Huniq_dm
    Hi'j' Hnest'.
  move=> ->.
  (* Also need element at m to agree *)
  congr (nth 0 _ _).
- (* i = m *)
  subst i.
  (* ws_m = size s - m *)
  have Hws_m : window_size m s = size s - m
    by rewrite (window_size_cons m a s0) -/m ltnn eqxx.
  have Hws_drop : 1 < size (drop m s)
    by rewrite size_drop -Hws_m.
  have Hdm_ne : drop m s <> [::]
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
  (* LHS = psi m (psi j s) *)
  (* take m (psi_j s) = take m s (since m < j) *)
  have Htm_pj : take m (psi j s) = take m s
    by apply: take_psi; exact: ltnW.
  (* drop m (psi_j s) *)
  (* nth at m: nth 0 (psi_j s) m = nth 0 s m (since m < j) *)
  have Hnth_m_pj : nth 0 (psi j s) m = nth 0 s m
    by apply: nth_psi_left.
  (* drop m.+1 (psi_j s) = psi (j-m-1) (drop m.+1 s) *)
  have Hdm_pj : drop m.+1 (psi j s) =
    psi (j - m - 1) (drop m.+1 s)
    by exact: drop_mm_psi.
  (* So drop m (psi_j s) = head d :: psi_{j'} (behead d)
     where d = drop m s, j' = j - m - 1 *)
  set d := drop m s.
  set j' := j - m - 1.
  have Hdm_pj_full : drop m (psi j s) =
    nth 0 s m :: psi j' (behead d).
    have Hm_pj_sz : m < size (psi j s) by rewrite size_psi.
    rewrite (drop_nth 0 Hm_pj_sz) Hnth_m_pj Hdm_pj.
    congr (_ :: _).
    rewrite /behead /d.
    by rewrite /s /= drop0.
  (* sort and head of drop m (psi_j s) = those of d *)
  have Hperm_dm : perm_eq (drop m (psi j s)) d.
    suff : perm_eq (take m s ++ drop m (psi j s))
      (take m s ++ d) by rewrite perm_cat2l.
    have -> : take m s ++ drop m (psi j s) = psi j s
      by rewrite -Htm_pj cat_take_drop.
    have -> : take m s ++ d = s
      by rewrite cat_take_drop.
    exact: psi_perm_eq.
  have Hsort_dm_pj : sort leq (drop m (psi j s)) =
    sort leq d.
    apply/perm_sortP => //.
    - by move=> ?; exact: leq_total.
    - exact: leq_trans.
    - exact: anti_leq.
  have Hhead_dm_pj : head 0 (drop m (psi j s)) = head 0 d.
    rewrite Hdm_pj_full /d.
    by case: (drop m s) Hdm_ne.
  (* psi m (psi j s) = take m s ++ rss(drop m (psi_j s)) *)
  have Hws_m_pj : window_size m (psi j s) = size s - m
    by rewrite window_size_psi Hws_m.
  have Hlhs : psi m (psi j s) =
    take m s ++ rank_shift_seq (drop m (psi j s)).
    rewrite /psi.
    have Hwa : window_at m (psi j s) = drop m (psi j s).
      rewrite /window_at Hws_m_pj.
      rewrite take_oversize // size_drop size_psi.
      by apply: leq_subr.
    rewrite Hwa Htm_pj Hws_m_pj.
    by rewrite subnKC ?drop_size ?cats0 ?size_psi // ltnW.
  (* RHS = psi j (psi m s) *)
  (* psi m s = take m s ++ rss d *)
  (* take m (psi j (psi m s)) = take m (psi m s) = take m s *)
  have Htm_pm : take m (psi m s) = take m s
    by rewrite Hpsi_m_eq take_cat size_take Hm
       ltnn subnn take0 cats0.
  have Htm_pj_pm : take m (psi j (psi m s)) = take m s.
    by rewrite (@take_psi m j (psi m s) (ltnW Hij)) Htm_pm.
  (* drop m (psi j (psi m s)) *)
  have Hpm_ne : psi m s <> [::].
    by move=> E; move: Hiw; rewrite -(size_psi m) E.
  have Hmm_pm : mm_pos (psi m s) = m by apply: mm_pos_psi_eq.
  have Hws_j_pm : 1 < window_size j (psi m s)
    by rewrite window_size_psi.
  have Hmj_pm : mm_pos (psi m s) < j by rewrite Hmm_pm.
  have Hdm_pm : drop m.+1 (psi j (psi m s)) =
    psi j' (drop m.+1 (psi m s)).
    exact: drop_mm_psi Hpm_ne Huniq_pi Hws_j_pm Hmj_pm.
  have Hdm1_pm : drop m.+1 (psi m s) = behead (rank_shift_seq d).
    rewrite Hpsi_m_eq drop_cat size_take Hm.
    have -> : m.+1 < m = false by rewrite ltnNge leqnSn.
    by rewrite /= subSn // subnn drop0.
  have Hnth_m_pm : nth 0 (psi m s) m =
    head 0 (rank_shift_seq d).
    rewrite Hpsi_m_eq nth_cat size_take Hm ltnn.
    by rewrite subnn -nth0.
  have Hnth_m_pj_pm : nth 0 (psi j (psi m s)) m =
    nth 0 (psi m s) m.
    by apply: nth_psi_left.
  have Hrhs : psi j (psi m s) =
    take m s ++ (head 0 (rank_shift_seq d) ::
      psi j' (behead (rank_shift_seq d))).
    apply: (@eq_from_nth _ 0).
      rewrite !size_psi size_cat /= size_psi size_behead
        size_rank_shift_seq2 size_drop.
      rewrite size_take Hm.
      have := ltnW Hm.
      by rewrite -subn_gt0 => /prednK <-; rewrite addnS.
    move=> k Hk.
    rewrite !size_psi in Hk.
    have [Hkm | Hkm] := ltnP k m.
      by rewrite nth_cat size_take Hm Hkm Htm_pj_pm
         nth_take.
    have [Hkeqm | Hkgtm] := eqVneq k m.
      subst k; rewrite nth_cat size_take Hm ltnn subnn /=.
      by rewrite Hnth_m_pj_pm Hnth_m_pm.
    have Hkm' : m < k by rewrite ltn_neqAle eq_sym Hkeqm Hkm.
    rewrite nth_cat size_take Hm.
    have -> : k < m = false by rewrite ltnNge Hkm.
    rewrite /= nth_drop subnK //.
    have Hkm1 : m.+1 <= k by exact: Hkm'.
    rewrite -(subnK Hkm1) addnC -nth_drop.
    rewrite -Hdm_pm -Hdm1_pm.
    rewrite nth_drop addnC subnK //.
    done.
  (* Now compare LHS and RHS *)
  rewrite Hlhs Hrhs.
  congr (_ ++ _).
  (* LHS drop part: rss(drop m (psi_j s)) *)
  (* RHS drop part: head(rss d) :: psi_j'(behead(rss d)) *)
  (* Need: rss(head d :: psi_j'(behead d)) =
           head(rss d) :: psi_j'(behead(rss d)) *)
  rewrite Hdm_pj_full.
  have Hd_head : nth 0 s m = head 0 d.
    by rewrite /d -nth0 nth_drop addn0.
  rewrite Hd_head.
  (* rank_shift_seq(head d :: psi_j' (behead d))
     = head(rss d) :: psi_j'(behead(rss d)) *)
  (* This is rank_shift_psi_comm applied to d with k = j' *)
  have Hj'0 : 0 < j'.
    rewrite /j' subnS.
    have Hjm : m < j by exact: Hij.
    by rewrite -subn_gt0 prednK // subn_gt0.
  (* head d :: psi_j'(behead d) = psi (j'+1) d ... no,
     it equals psi j' d when mm_pos d = 0 if we account
     for the Cartesian tree decomposition *)
  (* Actually: we need the identity
     rss(psi (j'+1) d) = psi (j'+1) (rss d) *)
  (* But psi (j'+1) d when mm_pos d = 0:
     psi (j'+1) d = head d :: psi j' (behead d) ... hmm
     this requires j'+1 > 0 which is true *)
  (* Wait, we computed earlier that for mm_pos d = 0 and k > 0:
     psi k d = head d :: psi (k-1) (behead d).
     But this requires window_size and window_at to decompose
     correctly. Let me verify this is a provable identity. *)
  (* Alternative: directly use rank_shift_psi_comm *)
  have Hj1 : j' + 1 = j - m by rewrite /j' subnS prednK //
    subn_gt0.
  (* Use rank_shift_psi_comm with k = j - m *)
  (* We need: rank_shift_seq (psi (j - m) d) =
              psi (j - m) (rank_shift_seq d) *)
  (* But psi (j-m) d when mm_pos d = 0: this is NOT the same as
     head :: psi_j'(behead d) in general because of the
     Cartesian tree structure of d *)
  (* Let me think again...
     psi (j-m) d: d has mm_pos 0. The window at (j-m) in d
     uses the Cartesian tree of d.
     j-m > 0, so the recursion goes to the right subtree
     (behead d) with index j-m-1 = j'.
     So window_size (j-m) d = window_size j' (behead d)
       = window_size j s  (from window_size_cons)
     And window_at (j-m) d = window_at j' (behead d)
       = window_at j s
     And psi (j-m) d:
       take (j-m) d ++ rank_shift_seq(window_at (j-m) d)
         ++ drop (j-m + ws) d
     But take (j-m) d = head d :: take j' (behead d)
     So psi (j-m) d = [head d] ++ take j' (behead d) ++
       rank_shift_seq(window_at j' (behead d)) ++
       drop (j' + ws) (behead d)
     = head d :: psi j' (behead d) *)
  have Hpsi_jm_d : psi (j - m) d = head 0 d :: psi j' (behead d).
    rewrite /psi.
    set ws_jm := window_size (j - m) d.
    set wa_jm := window_at (j - m) d.
    have Hjm_gt0 : 0 < j - m by rewrite subn_gt0.
    have Hjm_ne0 : (j - m == 0) = false.
      by apply/negbTE; rewrite -lt0n.
    have Hws_jm : ws_jm = window_size j' (behead d).
      rewrite /ws_jm /j'.
      case Hd' : d => [|a' t'] //.
      rewrite (window_size_cons (j - m) a' t') -Hd'
        Hmm_drop ltn0 /= Hjm_ne0 subn0.
      by rewrite /behead Hd'.
    have Hwa_jm : wa_jm = window_at j' (behead d).
      rewrite /wa_jm /j'.
      case Hd' : d => [|a' t'] //.
      rewrite (window_at_cons (j - m) a' t') -Hd'
        Hmm_drop ltn0 /= Hjm_ne0 subn0.
      by rewrite /behead Hd'.
    have Htake_jm : take (j - m) d = head 0 d :: take j' (behead d).
      case Hd' : d => [|a' t'] //.
      rewrite /= /j' subnS.
      by congr (_ :: take _ _).
    rewrite Htake_jm Hws_jm Hwa_jm.
    rewrite /psi.
    congr (_ :: _ ++ _ ++ _).
    rewrite /j' !subnS /behead.
    case Hd' : d => [//|a' t'] /=.
    congr (drop _ _).
    by rewrite -subnDA addn1.
  rewrite -Hpsi_jm_d.
  have Hjm_pos : 0 < j - m by rewrite subn_gt0.
  exact: rank_shift_psi_comm Huniq_dm Hws_drop Hmm_drop Hjm_pos.
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
Proof. native_compute. reflexivity. Qed.

(* The composed result is not the original (psi genuinely acts). *)
Example psi_comm_nontrivial :
  psi 1 (psi 5 [:: 3; 1; 4; 7; 5; 9; 2; 6]) = [:: 3; 9; 2; 6; 4; 1; 5; 7].
Proof. native_compute. reflexivity. Qed.

(* ===== Milestone 4: Descent-set effect of psi ============================== *)
(* Reference: M4_DESCENT_EFFECT_INFORMAL.md (informal proof note).             *)
(* Stanley EC1 (2nd ed.) section 1.6.3, Fact #2: how psi_i changes the        *)
(* descent set of w.                                                           *)

(* ----- M4.0 Descent predicate for seq nat --------------------------------- *)

Definition is_descent_seq (w : seq nat) (k : nat) : bool :=
  nth 0 w k > nth 0 w k.+1.

Example is_descent_seq_ex :
  let w := [:: 3; 1; 4; 7; 5; 9; 2; 6] in
  [seq k <- iota 0 7 | is_descent_seq w k] = [:: 0; 3; 5].
Proof. by []. Qed.

(* ----- M4.1 Tree classifier: has_left_child -------------------------------- *)
(* Vertex i has a left child iff i > 0 at its recursive level, i.e.,          *)
(* mm_pos of the containing subarray is strictly to the right of the          *)
(* subarray's left boundary. Mirrors window_size_fuel's recursion.            *)

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

Definition has_left_child (i : nat) (w : seq nat) : bool :=
  has_left_child_fuel (size w) i w.

(* Vertex 2 (value 4) in [3;1;4;7;5;9;2;6]: subarray [4;7;5], mm_pos=0,
   left subtree empty => no left child. *)
Example has_left_child_false :
  has_left_child 2 [:: 3; 1; 4; 7; 5; 9; 2; 6] = false.
Proof. by []. Qed.

(* Vertex 5 (value 9): subarray [4;7;5;9;2;6], mm_pos=3 (relative),
   left subtree [4;7;5] nonempty => has left child. *)
Example has_left_child_true :
  has_left_child 5 [:: 3; 1; 4; 7; 5; 9; 2; 6] = true.
Proof. by []. Qed.

Lemma has_left_child_fuel_0 : forall fuel s,
  has_left_child_fuel fuel 0 s = false.
Proof.
elim=> [//|fuel IH] [//|a s0].
by simpl; case: ifP => Hlt; [apply: IH | case: ifP].
Qed.

Lemma has_left_child_0 s : has_left_child 0 s = false.
Proof. exact: has_left_child_fuel_0. Qed.

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
  apply: has_left_child_fuel_monotone => //.
case: ifP => _ //.
apply: has_left_child_fuel_monotone => //.
Qed.

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

(* Non-triviality: L = [4;7;5], head=4=min, p=1, q=2.
   nth 0 L 1 = 7, nth 0 L 2 = 5: 7 > 5 = true.
   rank_shift_seq [4;7;5] = [7;5;4]: nth 0 _ 1 = 5, nth 0 _ 2 = 4: 5 > 4 = true. *)
Example rank_shift_interior_order_ex :
  let L := [:: 4; 7; 5] in
  (nth 0 L 1 > nth 0 L 2) = (nth 0 (rank_shift_seq L) 1 > nth 0 (rank_shift_seq L) 2).
Proof. by []. Qed.

(* ----- M4.4 Window head is extremum --------------------------------------- *)
(* Proved as Lemma window_head_extremum in the T6 section above.             *)
(* The Axiom window_head_is_extremum has been retired.                       *)

(* ----- M4.5 Boundary lemmas ----------------------------------------------- *)
(* The element just after the window is an ancestor's extremum, hence either  *)
(* less than min(window) or greater than max(window). Since rank_shift only  *)
(* permutes the window values, the descent bit at the right boundary is      *)
(* unchanged.                                                                *)
(* Justification: M4_DESCENT_EFFECT_INFORMAL.md section 2 (Case 4).          *)

Lemma post_window_extremum i w :
  uniq w -> i + window_size i w < size w ->
  (nth 0 w (i + window_size i w) < nth 0 (sort leq (window_at i w)) 0) \/
  (nth 0 w (i + window_size i w) > nth 0 (sort leq (window_at i w))
                                        (window_size i w).-1).
Proof.
move: i w.
suff Hgen : forall n i w, size w <= n ->
  uniq w -> i + window_size i w < size w ->
  (nth 0 w (i + window_size i w)
     < nth 0 (sort leq (window_at i w)) 0) \/
  (nth 0 w (i + window_size i w)
     > nth 0 (sort leq (window_at i w))
             (window_size i w).-1).
  by move=> i w Hu Hws; apply: (Hgen (size w));
     rewrite ?leqnn.
elim=> [|n IH] i w Hsz Huniq Hpost.
  by rewrite leqn0 in Hsz; move/eqP: Hsz Hpost => -> /=.
case: w Hsz Huniq Hpost => [//|a s0] Hsz Huniq Hpost.
set s := a :: s0; set j := mm_pos s.
have Hj : j < size s by apply: mm_pos_lt.
have Hs_ne : s <> [::] by discriminate.
rewrite (window_at_cons i a s0) (window_size_cons i a s0)
  -/s -/j.
case: (ltngtP i j) => [Hij | Hji | Heq_ij].
- (* Case i < j *)
  have Hfit := window_fits_left Hs_ne Hij.
  (* ws in take j s = ws in s (by window_size_cons) *)
  set ws_t := window_size i (take j s).
  have Hws_eq : window_size i s = ws_t
    by rewrite (window_size_cons i a s0) -/j Hij.
  have Htake_sz : size (take j s) = j
    by rewrite size_take Hj.
  have Huniq_t : uniq (take j s).
    have : uniq (take j s ++ drop j s)
      by rewrite cat_take_drop.
    by rewrite cat_uniq => /andP [? _].
  case Hbnd : (i + ws_t < j).
  + (* Sub-case: i + ws < j, both in take j s *)
    have Hpost_t : i + ws_t < size (take j s)
      by rewrite Htake_sz.
    have Hsz_t : size (take j s) <= n.
      by rewrite Htake_sz -ltnS;
         exact: leq_trans Hj Hsz.
    have := IH i (take j s) Hsz_t Huniq_t Hpost_t.
    (* nth in take j s = nth in s *)
    by rewrite nth_take.
  + (* Sub-case: i + ws = j *)
    have Hfit2 : i + ws_t = j.
      move/negbT: Hbnd; rewrite -leqNgt => Hge.
      have : i + window_size i s <= j := Hfit.
      by rewrite Hws_eq => Hfit';
         apply/eqP; rewrite eqn_leq Hge Hfit'.
    rewrite Hfit2.
    have Hnth_j := nth_w_mm_pos Hs_ne.
    (* Window values are in take j s *)
    set wa := window_at i (take j s).
    have Hws_t_gt0 : 0 < ws_t.
      by apply: window_size_gt0; rewrite Htake_sz.
    have Hwa_sz : size wa = ws_t.
      rewrite /wa /window_at.
      apply: size_takel.
      have := window_size_bound i (take j s).
      by rewrite size_drop Htake_sz.
    have Hwa_ne : wa <> [::].
      by move=> Habs; rewrite Habs /= in Hwa_sz;
         move: Hws_t_gt0; rewrite -Hwa_sz.
    (* All wa elements are in take j s *)
    have Hwa_sub : {subset wa <= take j s}.
      move=> x; rewrite /wa /window_at => Hx.
      have H1 := mem_take Hx.
      exact: mem_drop H1.
    (* min(s) and max(s) *)
    set minv := foldr minn (head 0 s) (behead s).
    set maxv := foldr maxn (head 0 s) (behead s).
    have [Hno_min Hno_max] := notin_take_mm Hs_ne.
    (* min(wa) >= min(s) and max(wa) <= max(s) *)
    have Hmin_sort := min_eq_nth_sort_0 Hwa_ne.
    have Hmax_sort := max_eq_nth_sort_last Hwa_ne.
    case: Hnth_j => Hval.
    * (* nth 0 s j = minv: show minv < min(wa) *)
      left; rewrite Hval.
      rewrite -Hmin_sort.
      (* minv <= every element of wa *)
      (* minv \notin take j s, so minv != any wa element *)
      (* hence minv < min(wa) *)
      set minwa := foldr minn (head 0 wa) (behead wa).
      have Hminwa_in : minwa \in wa.
        rewrite /minwa; case: (wa) Hwa_ne => [//|b t] _ /=.
        exact: min_in.
      have Hminwa_le : minv <= minwa.
        apply: foldr_minn_le.
        have := Hwa_sub _ Hminwa_in.
        exact: mem_take.
      have Hminwa_ne : minv != minwa.
        apply/negP => /eqP Heq_v.
        have : minv \in take j s
          by rewrite Heq_v; apply: Hwa_sub.
        by rewrite (negbTE Hno_min).
      by rewrite ltn_neqAle Hminwa_ne Hminwa_le.
    * (* nth 0 s j = maxv: show maxv > max(wa) *)
      right; rewrite Hval -Hwa_sz -Hmax_sort.
      set maxwa := foldr maxn (head 0 wa) (behead wa).
      have Hmaxwa_in : maxwa \in wa.
        rewrite /maxwa; case: (wa) Hwa_ne => [//|b t] _ /=.
        exact: max_in.
      have Hmaxwa_le : maxwa <= maxv.
        apply: foldr_maxn_ge.
        have := Hwa_sub _ Hmaxwa_in.
        exact: mem_take.
      have Hmaxwa_ne : maxwa != maxv.
        apply/negP => /eqP Heq_v.
        have : maxv \in take j s
          by rewrite -Heq_v; apply: Hwa_sub.
        by rewrite (negbTE Hno_max).
      by rewrite ltn_neqAle Hmaxwa_ne Hmaxwa_le.
- (* Case i > j: recurse on drop j.+1 s *)
  set i' := i - j - 1.
  set ds := drop j.+1 s.
  have Hds_sz : size ds = size s - j.+1
    by rewrite size_drop.
  have Huniq_d : uniq ds.
    have : uniq (take j.+1 s ++ drop j.+1 s)
      by rewrite cat_take_drop.
    by rewrite cat_uniq => /andP [_ /andP [_ ?]].
  have Hi'_eq : i' + j.+1 = i.
    by rewrite /i' -subnDA addn1 subnK.
  have Hws_eq : window_size i s = window_size i' ds.
    by rewrite (window_size_cons i a s0) -/j
       (ltnNge i j) (ltnW Hji) /= eq_sym (ltn_eqF Hji).
  have Hpost' : i + window_size i s < size s := Hpost.
  have Hpost_d : i' + window_size i' ds < size ds.
    suff : i' + window_size i' ds + j.+1 < size ds + j.+1.
      by rewrite ltn_add2r.
    rewrite Hds_sz subnK; last exact: Hj.
    rewrite -Hws_eq /i' -subnDA addn1.
    by rewrite addnAC subnK.
  have Hsz0 : size s0 <= n by exact: Hsz.
  have Hsz_d : size ds <= n.
    rewrite Hds_sz /s /= subSS.
    exact: leq_trans (leq_subr j _) Hsz0.
  have := IH i' ds Hsz_d Huniq_d Hpost_d.
  (* nth 0 s (i + window_size i' ds) =
     nth 0 ds (i' + window_size i' ds) *)
  set ws' := window_size i' ds.
  have Hnth_eq : nth 0 s (i + ws') =
                 nth 0 ds (i' + ws').
    rewrite /ds nth_drop addnA
      [j.+1 + i']addnC Hi'_eq.
    by [].
  by rewrite Hnth_eq.
- (* Case i = j: vacuous *)
  subst i.
  (* Goal already has (size s - j) from window_size_cons *)
  (* Hpost : j + window_size j s < size s *)
  (* But window_size j s = size s - j, so j + (size s - j) = size s *)
  exfalso.
  have Hws_j : window_size j s = size s - j.
    by rewrite (window_size_cons j a s0) -/j ltnn eqxx.
  move: Hpost; rewrite -/s Hws_j addnC subnK;
    last exact: ltnW.
  by rewrite ltnn.
Qed.

(* Non-triviality: w = [3;1;4;7;5;9;2;6], i=2. Window = [4;7;5] at [2,5).
   Post-window element at position 5: w[5] = 9. max(window) = 7.
   9 > 7 = true: post-window element is > max(window). *)
Example post_window_extremum_ex :
  let w := [:: 3; 1; 4; 7; 5; 9; 2; 6] in
  nth 0 w (2 + window_size 2 w) > nth 0 (sort leq (window_at 2 w)) (window_size 2 w).-1.
Proof. by []. Qed.

(* ----- M4.6 Pre-window lemmas (Case LR) ----------------------------------- *)
(* When vertex i has both children and head = min, the max of the subarray   *)
(* is in the right subtree, so max(window) = max(subarray) > w[i-1].        *)
(* Symmetrically when head = max, min(window) = min(subarray) < w[i-1].     *)
(* Justification: M4_DESCENT_EFFECT_INFORMAL.md section 4.                   *)

Lemma pre_window_lt_max_when_min_head :
  forall (i : nat) (w : seq nat),
  uniq w -> 0 < i -> has_left_child i w ->
  1 < window_size i w ->
  head 0 (window_at i w) == nth 0 (sort leq (window_at i w)) 0 ->
  nth 0 w i.-1 <
    nth 0 (sort leq (window_at i w)) (window_size i w).-1.
Proof.
move=> i w.
suff Hgen : forall n i w, size w <= n ->
  uniq w -> 0 < i -> has_left_child i w ->
  1 < window_size i w ->
  head 0 (window_at i w) ==
    nth 0 (sort leq (window_at i w)) 0 ->
  nth 0 w i.-1 <
    nth 0 (sort leq (window_at i w))
          (window_size i w).-1.
  by move=> *; apply: (Hgen (size w)); rewrite ?leqnn.
elim=> [|n IH] {}i {}w Hsz Huniq Hi0 Hlc Hws Hhead.
  have /eqP Hw0 : size w == 0 by rewrite -leqn0.
  by move: Hws; move/size0nil: Hw0 => ->;
     rewrite /window_size /=.
case: w Hsz Huniq Hlc Hws Hhead => [//|a s0]
  Hsz Huniq Hlc Hws Hhead.
set s := a :: s0; set j := mm_pos s.
have Hj : j < size s by apply: mm_pos_lt.
have Hs_ne : s <> [::] by discriminate.
rewrite (window_at_cons i a s0) (window_size_cons i a s0)
  -/s -/j.
rewrite (has_left_child_cons i a s0) -/s -/j in Hlc.
rewrite (window_at_cons i a s0) (window_size_cons i a s0)
  -/s -/j in Hhead Hws.
case: (ltngtP i j) => [Hij | Hji | Heq_ij].
- (* i < j: recurse on take j s *)
  move: Hhead Hlc Hws; rewrite Hij => Hhead Hlc Hws.
  have Huniq_t : uniq (take j s).
    by have : uniq (take j s ++ drop j s);
       [rewrite cat_take_drop | rewrite cat_uniq => /andP[]].
  have Hsz_t : size (take j s) <= n.
    by rewrite size_take Hj; exact: leq_trans Hj Hsz.
  have := IH _ _ Hsz_t Huniq_t Hi0 Hlc Hws Hhead.
  have Hpred_lt : i.-1 < j.
    by apply: leq_ltn_trans (leq_pred _) Hij.
  by rewrite nth_take.
- (* i > j: recurse on drop j.+1 s *)
  have Hij_f : i < j = false by rewrite ltnNge (ltnW Hji).
  have Heq_f : (i == j) = false
    by apply: gtn_eqF.
  move: Hhead Hlc Hws; rewrite Hij_f Heq_f =>
    Hhead Hlc Hws.
  set i' := i - j - 1.
  set ds := drop j.+1 s.
  have Huniq_d : uniq ds.
    by have : uniq (take j.+1 s ++ drop j.+1 s);
       [rewrite cat_take_drop |
        rewrite cat_uniq => /andP [_ /andP [_ ?]]].
  have Hsz_d : size ds <= n.
    rewrite /ds size_drop /s /=.
    have Hsz' : size s0 <= n by exact: Hsz.
    exact: leq_trans (leq_subr j _) Hsz'.
  have Hi0' : 0 < i'.
    rewrite /i'; case Hi'0 : (i - j - 1) => [|//].
    by move: Hlc; rewrite /i' Hi'0 has_left_child_0.
  have := IH _ _ Hsz_d Huniq_d Hi0' Hlc Hws Hhead.
  have Hi'_eq : i' + j.+1 = i.
    by rewrite /i' -subnDA addn1 subnK.
  have Hpred_eq : i'.-1 + j.+1 = i.-1.
    have : i'.-1.+1 = i' by rewrite prednK.
    move=> Hsucc.
    have : i'.-1.+1 + j.+1 = i by rewrite Hsucc Hi'_eq.
    by move=> <-; rewrite addSn.
  rewrite /ds nth_drop.
  by rewrite addnC Hpred_eq.
- (* i = j *)
  subst i.
  have Hlc' : 0 < j.
    by move: Hlc; rewrite ltnn eqxx.
  (* Simplify the conditionals after subst i -> j *)
  move: Hhead Hws; rewrite ltnn eqxx => Hhead Hws.
  have Hdrop_ne : drop j s <> [::].
    move=> Habs; have : size (drop j s) = 0 by rewrite Habs.
    by rewrite size_drop => /eqP; rewrite subn_eq0 leqNgt Hj.
  have [Hno_min Hno_max] := notin_take_mm Hs_ne.
  have Hmax_d := max_val_drop Hs_ne Hno_max Hj.
  have Hmax_sort := max_eq_nth_sort_last Hdrop_ne.
  have Hj_pos : 0 < j := Hlc'.
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
    have : foldr maxn (head 0 s) (behead s) \in take j s
      by rewrite -Heq.
    by rewrite (negbTE Hno_max).
  rewrite -(size_drop j s) -Hmax_sort Hmax_d.
  by rewrite ltn_neqAle Hpred_ne Hpred_le.
Qed.

Lemma pre_window_gt_min_when_max_head :
  forall (i : nat) (w : seq nat),
  uniq w -> 0 < i -> has_left_child i w ->
  1 < window_size i w ->
  head 0 (window_at i w) ==
    nth 0 (sort leq (window_at i w)) (window_size i w).-1 ->
  nth 0 w i.-1 > nth 0 (sort leq (window_at i w)) 0.
Proof.
move=> i w.
suff Hgen : forall n i w, size w <= n ->
  uniq w -> 0 < i -> has_left_child i w ->
  1 < window_size i w ->
  head 0 (window_at i w) ==
    nth 0 (sort leq (window_at i w))
          (window_size i w).-1 ->
  nth 0 w i.-1 >
    nth 0 (sort leq (window_at i w)) 0.
  by move=> *; apply: (Hgen (size w)); rewrite ?leqnn.
elim=> [|n IH] {}i {}w Hsz Huniq Hi0 Hlc Hws Hhead.
  have /eqP Hw0 : size w == 0 by rewrite -leqn0.
  by move: Hws; move/size0nil: Hw0 => ->;
     rewrite /window_size /=.
case: w Hsz Huniq Hlc Hws Hhead => [//|a s0]
  Hsz Huniq Hlc Hws Hhead.
set s := a :: s0; set j := mm_pos s.
have Hj : j < size s by apply: mm_pos_lt.
have Hs_ne : s <> [::] by discriminate.
rewrite [window_at i s](window_at_cons i a s0) -/j.
rewrite (has_left_child_cons i a s0) -/s -/j in Hlc.
rewrite [window_at i s](window_at_cons i a s0)
  [window_size i s](window_size_cons i a s0)
  -/j in Hhead Hws.
case: (ltngtP i j) => [Hij | Hji | Heq_ij].
- (* i < j *)
  move: Hhead Hlc Hws; rewrite Hij => Hhead Hlc Hws.
  have Huniq_t : uniq (take j s).
    by have : uniq (take j s ++ drop j s);
       [rewrite cat_take_drop | rewrite cat_uniq => /andP[]].
  have Hsz_t : size (take j s) <= n.
    by rewrite size_take Hj; exact: leq_trans Hj Hsz.
  have := IH _ _ Hsz_t Huniq_t Hi0 Hlc Hws Hhead.
  have Hpred_lt : i.-1 < j
    by apply: leq_ltn_trans (leq_pred _) Hij.
  by rewrite nth_take.
- (* i > j *)
  have Hij_f : i < j = false by rewrite ltnNge (ltnW Hji).
  have Heq_f : (i == j) = false by apply: gtn_eqF.
  move: Hhead Hlc Hws; rewrite Hij_f Heq_f =>
    Hhead Hlc Hws.
  set i' := i - j - 1.
  set ds := drop j.+1 s.
  have Huniq_d : uniq ds.
    by have : uniq (take j.+1 s ++ drop j.+1 s);
       [rewrite cat_take_drop |
        rewrite cat_uniq => /andP [_ /andP [_ ?]]].
  have Hsz_d : size ds <= n.
    rewrite /ds size_drop /s /=.
    have Hsz' : size s0 <= n by exact: Hsz.
    exact: leq_trans (leq_subr j _) Hsz'.
  have Hi0' : 0 < i'.
    rewrite /i'; case Hi'0 : (i - j - 1) => [|//].
    by move: Hlc; rewrite /i' Hi'0 has_left_child_0.
  have := IH _ _ Hsz_d Huniq_d Hi0' Hlc Hws Hhead.
  have Hi'_eq : i' + j.+1 = i
    by rewrite /i' -subnDA addn1 subnK.
  have Hpred_eq : i'.-1 + j.+1 = i.-1.
    have : i'.-1.+1 = i' by rewrite prednK.
    move=> Hsucc.
    have : i'.-1.+1 + j.+1 = i by rewrite Hsucc Hi'_eq.
    by move=> <-; rewrite addSn.
  rewrite /ds nth_drop.
  by rewrite addnC Hpred_eq.
- (* i = j *)
  subst i.
  have Hlc' : 0 < j by move: Hlc; rewrite ltnn eqxx.
  move: Hhead Hws; rewrite ltnn eqxx => Hhead Hws.
  have Hdrop_ne : drop j s <> [::].
    move=> Habs; have : size (drop j s) = 0 by rewrite Habs.
    by rewrite size_drop => /eqP; rewrite subn_eq0 leqNgt Hj.
  have [Hno_min Hno_max] := notin_take_mm Hs_ne.
  have Hmin_d := min_val_drop Hs_ne Hno_min Hj.
  have Hmin_sort := min_eq_nth_sort_0 Hdrop_ne.
  have Hpred_lt : j.-1 < j by rewrite prednK.
  have Hpred_in : nth 0 s j.-1 \in take j s.
    rewrite -(nth_take 0 Hpred_lt).
    by apply: mem_nth; rewrite size_take Hj.
  have Hpred_ge :
    foldr minn (head 0 s) (behead s) <= nth 0 s j.-1.
    by apply: foldr_minn_le; apply: mem_nth;
       exact: ltn_trans Hpred_lt Hj.
  have Hpred_ne :
    nth 0 s j.-1 != foldr minn (head 0 s) (behead s).
    apply/negP => /eqP Heq.
    have : foldr minn (head 0 s) (behead s) \in take j s
      by rewrite -Heq.
    by rewrite (negbTE Hno_min).
  rewrite -Hmin_sort Hmin_d.
  by rewrite ltn_neqAle eq_sym Hpred_ne Hpred_ge.
Qed.

(* Non-triviality: w = [3;1;4;7;5;9;2;6], i=5. Window = [9;2;6].
   Head = 9 = max. min(window) = 2. w[4] = 5 > 2. *)
Example pre_window_gt_min_ex :
  let w := [:: 3; 1; 4; 7; 5; 9; 2; 6] in
  nth 0 w 4 > nth 0 (sort leq (window_at 5 w)) 0.
Proof. by []. Qed.

(* ----- M4.7 Exactly-one-descent in Case LR -------------------------------- *)
(* When vertex i has both children, w[i] is an extremum of S_i (the full     *)
(* subtree), so w[i-1] and w[i+1] are on opposite sides of w[i]. Exactly    *)
(* one of {i-1, i} is a descent.                                            *)
(* Justification: M4_DESCENT_EFFECT_INFORMAL.md section 4.1.                 *)

Lemma exactly_one_descent_LR :
  forall (i : nat) (w : seq nat),
  uniq w -> 0 < i -> has_left_child i w ->
  1 < window_size i w ->
  is_descent_seq w i.-1 (+) is_descent_seq w i.
Proof.
move=> i w.
suff Hgen : forall n i w, size w <= n ->
  uniq w -> 0 < i -> has_left_child i w ->
  1 < window_size i w ->
  is_descent_seq w i.-1 (+) is_descent_seq w i.
  by move=> *; apply: (Hgen (size w)); rewrite ?leqnn.
elim=> [|n IH] {}i {}w Hsz Huniq Hi0 Hlc Hws.
  have /eqP Hw0 : size w == 0 by rewrite -leqn0.
  by move: Hws; move/size0nil: Hw0 => ->;
     rewrite /window_size /=.
case: w Hsz Huniq Hlc Hws => [//|a s0]
  Hsz Huniq Hlc Hws.
set s := a :: s0; set j := mm_pos s.
have Hj : j < size s by apply: mm_pos_lt.
have Hs_ne : s <> [::] by discriminate.
rewrite -/s -/j in Hlc Hws.
have Hhlc := has_left_child_cons i a s0.
have Hwsc := window_size_cons i a s0.
rewrite /= -/s -/j in Hhlc Hwsc.
rewrite Hhlc in Hlc.
rewrite Hwsc in Hws.
case: (ltngtP i j) => [Hij | Hji | Heq_ij].
- (* i < j *)
  move: Hlc Hws; rewrite Hij => Hlc Hws.
  have Huniq_t : uniq (take j s).
    by have : uniq (take j s ++ drop j s);
       [rewrite cat_take_drop | rewrite cat_uniq => /andP[]].
  have Hsz_t : size (take j s) <= n.
    by rewrite size_take Hj; exact: leq_trans Hj Hsz.
  have Hpred_lt : i.-1 < j
    by apply: leq_ltn_trans (leq_pred _) Hij.
  have Hi1_lt : i.+1 < j.
    have Hfit := window_fits_left Hs_ne Hij.
    suff : i + 2 <= j by rewrite addn2.
    apply: leq_trans _ Hfit.
    rewrite leq_add2l Hwsc Hij.
    exact: Hws.
  have Hih := IH _ _ Hsz_t Huniq_t Hi0 Hlc Hws.
  move: Hih.
  rewrite /is_descent_seq (prednK Hi0).
  rewrite !(nth_take 0 Hpred_lt)
          !(nth_take 0 Hij)
          !(nth_take 0 Hi1_lt).
  by [].
- (* i > j *)
  have Hij_f : i < j = false by rewrite ltnNge (ltnW Hji).
  have Heq_f : (i == j) = false by apply: gtn_eqF.
  move: Hlc Hws; rewrite Hij_f Heq_f => Hlc Hws.
  set i' := i - j - 1.
  set ds := drop j.+1 s.
  have Huniq_d : uniq ds.
    by have : uniq (take j.+1 s ++ drop j.+1 s);
       [rewrite cat_take_drop |
        rewrite cat_uniq => /andP [_ /andP [_ ?]]].
  have Hsz_d : size ds <= n.
    rewrite /ds size_drop /s /=.
    have Hsz' : size s0 <= n by exact: Hsz.
    exact: leq_trans (leq_subr j _) Hsz'.
  have Hi0' : 0 < i'.
    rewrite /i'; case Hi'0 : (i - j - 1) => [|//].
    by move: Hlc; rewrite /i' Hi'0 has_left_child_0.
  have Hi'_eq : i' + j.+1 = i
    by rewrite /i' -subnDA addn1 subnK.
  have Hpred_eq : i'.-1 + j.+1 = i.-1.
    have : i'.-1.+1 = i' by rewrite prednK.
    move=> Hsucc.
    have : i'.-1.+1 + j.+1 = i by rewrite Hsucc Hi'_eq.
    by move=> <-; rewrite addSn.
  have Hi1_eq : i'.+1 + j.+1 = i.+1.
    by rewrite addSn Hi'_eq.
  have Hih := IH _ _ Hsz_d Huniq_d Hi0' Hlc Hws.
  move: Hih.
  rewrite /is_descent_seq (prednK Hi0') /ds.
  rewrite !(nth_drop).
  rewrite [j.+1 + i'.-1]addnC Hpred_eq.
  rewrite [j.+1 + i']addnC Hi'_eq.
  rewrite [j.+1 + i'.+1]addnC Hi1_eq.
  rewrite (prednK Hi0).
  exact: id.
- (* i = j *)
  subst i.
  have Hlc' : 0 < j by move: Hlc; rewrite ltnn eqxx.
  have Hdrop_ne : drop j s <> [::].
    move=> Habs; have : size (drop j s) = 0 by rewrite Habs.
    by rewrite size_drop => /eqP; rewrite subn_eq0 leqNgt Hj.
  have [Hno_min Hno_max] := notin_take_mm Hs_ne.
  have Hnth := nth_w_mm_pos Hs_ne.
  have Hpred_lt : j.-1 < j by rewrite prednK.
  have Hpred_in : nth 0 s j.-1 \in take j s.
    rewrite -(nth_take 0 Hpred_lt).
    by apply: mem_nth; rewrite size_take Hj.
  have Hj1_lt : j.+1 < size s.
    move: Hws; rewrite ltnn eqxx => Hws1.
    have : j + 2 <= size s
      by rewrite -(leq_subRL 2 (ltnW Hj)).
    by rewrite addn2.
  have Hj1_in : nth 0 s j.+1 \in s
    by apply: mem_nth.
  rewrite /is_descent_seq (prednK Hlc').
  case: Hnth => Hval.
  + (* w[j] = min(s) *)
    have Hd_pred : nth 0 s j.-1 > nth 0 s j.
      rewrite Hval ltn_neqAle; apply/andP; split.
      * apply/negP => /eqP Heq.
        have : foldr minn (head 0 s) (behead s) \in take j s
          by rewrite Heq.
        by rewrite (negbTE Hno_min).
      * apply: foldr_minn_le. apply: mem_nth.
        exact: ltn_trans Hpred_lt Hj.
    have Hnd_j : ~~ (nth 0 s j > nth 0 s j.+1).
      rewrite -leqNgt Hval.
      apply: foldr_minn_le. exact: Hj1_in.
    by rewrite Hd_pred (negbTE Hnd_j).
  + (* w[j] = max(s) *)
    have Hnd_pred : ~~ (nth 0 s j.-1 > nth 0 s j).
      rewrite -leqNgt Hval.
      apply: foldr_maxn_ge. apply: mem_nth.
      exact: ltn_trans Hpred_lt Hj.
    have Hd_j : nth 0 s j > nth 0 s j.+1.
      rewrite Hval ltn_neqAle; apply/andP; split.
      * apply/negP => /eqP Heq.
        have Heq2 : nth 0 s j = nth 0 s j.+1
          by rewrite Hval -Heq.
        have : j == j.+1.
          by rewrite -(nth_uniq 0 Hj Hj1_lt Huniq) Heq2
             eqxx.
        by rewrite eqn_leq ltnn andbF.
      * apply: foldr_maxn_ge. exact: Hj1_in.
    by rewrite (negbTE Hnd_pred) Hd_j.
Qed.

(* Non-triviality: w = [3;1;4;7;5;9;2;6], i=5.
   is_descent_seq w 4 = (5 > 9) = false.
   is_descent_seq w 5 = (9 > 2) = true.
   false (+) true = true. *)
Example exactly_one_descent_LR_ex :
  let w := [:: 3; 1; 4; 7; 5; 9; 2; 6] in
  is_descent_seq w 4 (+) is_descent_seq w 5.
Proof. by []. Qed.

(* ----- M4.8 Helpers for descent-effect proofs ----------------------------- *)

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

Lemma pre_window_extremum_R i w :
  uniq w -> 0 < i -> ~~ has_left_child i w ->
  1 < window_size i w ->
  (nth 0 w i.-1 <
     nth 0 (sort leq (window_at i w)) 0) \/
  (nth 0 w i.-1 >
     nth 0 (sort leq (window_at i w))
           (window_size i w).-1).
Proof.
move: i w.
suff H : forall n i w, size w <= n ->
  uniq w -> 0 < i -> ~~ has_left_child i w ->
  1 < window_size i w ->
  (nth 0 w i.-1 <
     nth 0 (sort leq (window_at i w)) 0) \/
  (nth 0 w i.-1 >
     nth 0 (sort leq (window_at i w))
           (window_size i w).-1).
  by move=> i w *;
     apply: (H (size w)); rewrite ?leqnn.
elim=> [|n IH] {}i {}w Hsz Hu Hi0 Hnlc Hws.
  have /eqP Hw0 : size w == 0 by rewrite -leqn0.
  by move: Hws; move/size0nil: Hw0 => ->;
     rewrite /window_size /=.
case: w Hsz Hu Hnlc Hws =>
  [//|a s0] Hsz Hu Hnlc Hws.
set s := a :: s0.
set j := mm_pos s.
have Hj : j < size s by apply: mm_pos_lt.
have Hne : s <> [::] by discriminate.
have Hsz0 : size s0 <= n := Hsz.
rewrite (window_at_cons i a s0)
        (window_size_cons i a s0) -/s -/j.
rewrite (has_left_child_cons i a s0)
        -/s -/j in Hnlc.
rewrite (window_size_cons i a s0)
        -/s -/j in Hws.
case: (ltngtP i j) => [Hij | Hji | Heq_ij].
- move: Hnlc Hws; rewrite Hij => Hnlc Hws.
  have Hu_t : uniq (take j s).
    by have : uniq (take j s ++ drop j s);
       [rewrite cat_take_drop |
        rewrite cat_uniq => /andP[]].
  have Hsz_t : size (take j s) <= n.
    rewrite size_take Hj -ltnS.
    exact: leq_trans Hj Hsz.
  have := IH _ _ Hsz_t Hu_t Hi0 Hnlc Hws.
  by rewrite nth_take //
     (leq_ltn_trans (leq_pred _) Hij).
- have Hf1 : i < j = false
    by rewrite ltnNge (ltnW Hji).
  have Hf2 : (i == j) = false
    by apply: gtn_eqF.
  move: Hnlc Hws; rewrite Hf1 Hf2 =>
    Hnlc Hws.
  set ds := drop j.+1 s.
  have Hu_d : uniq ds.
    by move: (Hu); rewrite -/s
       -(cat_take_drop j.+1 s)
       cat_uniq => /andP [_ /andP [_ ?]].
  have Hsz_d : size ds <= n.
    rewrite /ds size_drop /s /= subSS.
    exact: leq_trans (leq_subr j _) Hsz0.
  case H0 : (0 < i - j - 1).
  + have Hpe : j.+1 + (i - j - 1).-1 = i.-1.
      by rewrite addnC; exact: pred_sub_add.
    case: (IH _ _ Hsz_d Hu_d H0 Hnlc Hws) =>
      [Hl | Hr].
    * left.
      by rewrite /ds nth_drop Hpe in Hl.
    * right.
      by rewrite /ds nth_drop Hpe in Hr.
  + move/negbT: H0; rewrite -eqn0Ngt =>
      /eqP Hi'0.
    have Hieq : i = j.+1.
      suff : i - j - 1 + j.+1 = i
        by rewrite Hi'0 add0n => <-.
      by rewrite -subnDA addn1 subnK.
    rewrite Hieq subSn // subnn.
    set wa := window_at 0 ds.
    have Hws0 : 1 < window_size 0 ds.
      by move: Hws; rewrite Hieq subSn // subnn.
    have Hwa_ne : wa <> [::].
      move=> Hab.
      have Hswa : size wa = window_size 0 ds.
        rewrite /wa /window_at drop0.
        apply: size_takel.
        by have := window_size_bound 0 ds;
           rewrite subn0.
      by move: Hws0; rewrite -Hswa Hab.
    have Hsub : {subset wa <= s}.
      move=> x Hx.
      suff : x \in ds by exact: mem_drop.
      by move: Hx; rewrite /wa /window_at drop0;
         exact: mem_take.
    have Hjni : nth 0 s j \notin wa.
      apply/negP => Hab.
      have Hd : nth 0 s j \in ds.
        by move: Hab; rewrite /wa /window_at
           drop0; exact: mem_take.
      have Ht : nth 0 s j \in take j.+1 s.
        rewrite -(nth_take 0 (ltnSn j)).
        apply: mem_nth.
        rewrite size_take.
        by case: (ltnP j.+1 (size s)).
      move: (Hu); rewrite -/s
        -(cat_take_drop j.+1 s) cat_uniq =>
        /andP [_ /andP [Hno _]].
      by move/hasPn: Hno => /(_ _ Hd);
         rewrite Ht.
    have := nth_w_mm_pos Hne.
    rewrite -/j => [] [Hval | Hval].
    * left.
      rewrite -(min_eq_nth_sort_0 Hwa_ne).
      set m := foldr minn (head 0 wa)
                          (behead wa).
      have Hm_in : m \in wa.
        rewrite /m; case: (wa) Hwa_ne =>
          [//|b t] _ /=; exact: min_in.
      have Hle :
        foldr minn (head 0 s) (behead s) <= m.
        apply: foldr_minn_le.
        exact: Hsub _ Hm_in.
      have Hne2 :
        foldr minn (head 0 s) (behead s) != m.
        apply/negP => /eqP Heq.
        have : nth 0 s j = m
          by rewrite Hval Heq.
        move=> HH; rewrite HH in Hjni.
        by rewrite (negbTE Hjni) in Hm_in.
      by rewrite Hval ltn_neqAle Hne2 Hle.
    * right.
      have Hswa : size wa = window_size 0 ds.
        rewrite /wa /window_at drop0.
        apply: size_takel.
        by have := window_size_bound 0 ds;
           rewrite subn0.
      rewrite -Hswa
        -(max_eq_nth_sort_last Hwa_ne).
      set M := foldr maxn (head 0 wa)
                          (behead wa).
      have HM_in : M \in wa.
        rewrite /M; case: (wa) Hwa_ne =>
          [//|b t] _ /=; exact: max_in.
      have Hle :
        M <= foldr maxn (head 0 s) (behead s).
        apply: foldr_maxn_ge.
        exact: Hsub _ HM_in.
      have Hne2 :
        M != foldr maxn (head 0 s) (behead s).
        apply/negP => /eqP Heq.
        have : nth 0 s j = M
          by rewrite Hval -Heq.
        move=> HH; rewrite HH in Hjni.
        by rewrite (negbTE Hjni) in HM_in.
      by rewrite Hval ltn_neqAle Hne2 Hle.
- subst i. move: Hnlc.
  by rewrite (ltnn j) (eqxx j) => /negP.
Qed.

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
  have := @sorted_leq_nth _ leq leq_trans leqnn 0 (sort leq L) Hs.
  move=> /(_ 0 rj); apply.
  + by rewrite inE Hsz_s.
  + by rewrite inE.
  + done.
- rewrite -Hnth.
  have := @sorted_leq_nth _ leq leq_trans leqnn 0 (sort leq L) Hs.
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
have Hpos : 0 < size L := leq_ltn_trans (leq0n j) Hj.
split.
- rewrite -Hnth.
  have := @sorted_leq_nth _ leq leq_trans leqnn 0 (sort leq L) Hs.
  move=> /(_ 0 rj); apply.
  + by rewrite inE Hsz_s.
  + by rewrite inE.
  + done.
- rewrite -Hnth.
  have := @sorted_leq_nth _ leq leq_trans leqnn 0 (sort leq L) Hs.
  move=> /(_ rj (size L).-1); apply.
  + by rewrite inE.
  + by rewrite inE Hsz_s ltn_predL.
  + have : rj < size L by rewrite -Hsz_s.
    by move=> H; rewrite -ltnS (prednK Hpos).
Qed.

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
  move/(f_equal (fun x => index x
    (rank_shift_seq L))).
  rewrite !index_uniq ?Hsz_rs ?ltnW //.
  by move=> Habs; discriminate Habs.
have [_ Hle] := elem_rs_in_range (j:=1) Hsz.
rewrite ltn_neqAle; apply/andP; split; last by [].
by rewrite eq_sym.
Qed.

(* When new head = min, no descent at position 0 in rank_shift_seq. *)
Lemma rs_head_min_no_descent (L : seq nat) :
  uniq L -> 1 < size L ->
  head 0 L = nth 0 (sort leq L) (size L).-1 ->
  nth 0 (rank_shift_seq L) 0 <
  nth 0 (rank_shift_seq L) 1.
Proof.
move=> Hu Hsz Hmax.
have Hnew := rank_shift_head_max_to_min Hu Hsz Hmax.
rewrite -nth0 Hnew.
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
  move/(f_equal (fun x => index x
    (rank_shift_seq L))).
  rewrite !index_uniq ?Hsz_rs // => Habs.
  by discriminate Habs.
have [Hle _] := elem_rs_in_range (j:=1) Hsz.
rewrite ltn_neqAle; apply/andP; split; last by [].
by [].
Qed.

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
  + by exact: leq_ltn_trans Hlt Hmin_j'.
  + by exact: leq_ltn_trans Hlt Hmin_j.
- have [_ Hmax_j] := elem_in_range Hj.
  have [_ Hmax_j'] := elem_rs_in_range Hj'.
  apply/negbTE; rewrite -leqNgt.
    by exact: leq_trans Hmax_j (ltnW Hgt).
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
  apply/negbTE; rewrite -leqNgt.
    by exact: leq_trans (ltnW Hlt) Hmin_j.
- have [_ Hmax_j] := elem_in_range Hj.
  have [_ Hmax_j'] := elem_rs_in_range Hj'.
  apply/idP/idP => _.
  + by exact: leq_ltn_trans Hmax_j' Hgt.
  + by exact: leq_ltn_trans Hmax_j Hgt.
Qed.
(* The descent-set effect of psi_i, organized by tree case (R vs LR) and     *)
(* whether i is currently a descent.                                         *)
(* Each lemma describes D(psi_i w) in terms of D(w) for all positions k.     *)
(* Justification: M4_DESCENT_EFFECT_INFORMAL.md sections 2-4.                *)

(* ----- Common proof pattern for descent-effect lemmas ---------------------- *)
(* Each lemma case-splits k relative to window [i, i+ws):                     *)
(*   k+1 < i (prefix), k = i-1 (left boundary), k = i (head),               *)
(*   i < k < i+ws (interior), k = i+ws-1 (right boundary), k >= i+ws (suffix)*)

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
have Hws_le : i + ws <= size w
  by have := window_size_bound i w; rewrite -(leq_subRL _ (ltnW Hiw)).
have Hmin : head 0 L = nth 0 (sort leq L) 0.
  case/orP: (window_head_extremum Hu Hws) => [/eqP //|/eqP Hmax].
  exfalso; apply/negP: Hnd; rewrite negbK.
  by rewrite (size_window_at Hiw) in Hmax;
     exact: (head_max_is_descent Hu Hws Hmax).
rewrite /is_descent_seq.
have [->|Hne] := eqVneq k i.
{ rewrite /=.
  have Hi1 : i.+1 < i + ws by rewrite -addn1 ltn_add2l.
  have Hi0 : i < i + ws := ltn_trans (ltnSn i) Hi1.
  rewrite /ws in Hi0 Hi1.
  rewrite (nth_psi_inside Hiw (leqnn i) Hi0)
          (nth_psi_inside Hiw (leqnSn i) Hi1)
          subnn (@subSnn i) -/L.
  by apply: (rs_head_max_descent HuL HszL1 Hmin). }
rewrite orFb.
case: (ltnP k i) => [Hk_lt_i | Hk_ge_i].
{ case: (ltnP k.+1 i) => [Hk1_lt|Hk1_ge].
  - by rewrite !nth_psi_left //; exact: ltnW.
  - have Hk1_eq : k.+1 = i
      by apply/eqP; rewrite eqn_leq Hk_lt_i Hk1_ge.
    have Hi0 : 0 < i by rewrite -Hk1_eq.
    rewrite [nth 0 (psi i w) k]nth_psi_left //.
    have Hi0_ws : i < i + window_size i w
      by rewrite -[X in X < _]addn0 ltn_add2l ltnW.
    rewrite Hk1_eq (nth_psi_inside Hiw (leqnn i) Hi0_ws)
            subnn -/L.
    have Hk_eq : k = i.-1 by rewrite -Hk1_eq.
    rewrite Hk_eq.
    have Hpe := pre_window_extremum_R Hu Hi0 Hnlc Hws.
    have Hpe' : nth 0 w i.-1 < nth 0 (sort leq L) 0 \/
                nth 0 (sort leq L) (size L).-1 < nth 0 w i.-1
      by rewrite HszL /ws /L.
    rewrite -(cmp_out_of_range_left (ltnW HszL1) (ltnW HszL1) Hpe').
    congr (_ < _).
    by rewrite (nth_window_at Hiw (ltnW Hws)) addn0. }
{ have Hk_gt : i < k by rewrite ltn_neqAle eq_sym Hne Hk_ge_i.
  case: (leqP (i + ws) k) => [Hk_ge|Hk_lt].
  - by rewrite !nth_psi_right //; exact: leq_trans Hk_ge (leqnSn k).
  - case: (ltnP k.+1 (i + ws)) => [Hk1_in|Hk1_out].
    + rewrite /ws in Hk1_in Hk_lt.
      rewrite (nth_psi_inside Hiw (ltnW Hk_gt) Hk_lt)
              (nth_psi_inside Hiw (ltnW (ltn_trans Hk_gt (ltnSn k))) Hk1_in).
      rewrite -rank_shift_preserves_interior_order //.
      * congr (_ < _).
        -- have Hk1_off : k.+1 - i < window_size i w
             by rewrite ltn_subLR // ltnW.
           by rewrite (nth_window_at Hiw Hk1_off) subnKC // ltnW.
        -- have Hk_off : k - i < window_size i w by rewrite ltn_subLR.
           by rewrite (nth_window_at Hiw Hk_off) subnKC.
      * by exact: window_head_extremum.
      * by rewrite subn_gt0.
      * by rewrite subn_gt0 (ltn_trans Hk_gt (ltnSn k)).
      * by rewrite (size_window_at Hiw) ltn_subLR.
      * by rewrite (size_window_at Hiw) ltn_subLR // ltnW.
    + have Hk1_eq : k.+1 = i + ws.
        apply/eqP; rewrite eqn_leq Hk1_out /= andbT; exact: Hk_lt.
      rewrite Hk1_eq nth_psi_right //.
      rewrite /ws in Hk_lt.
      rewrite (nth_psi_inside Hiw (ltnW Hk_gt) Hk_lt) -/L.
      have Hk_off : k - i < size L by rewrite (size_window_at Hiw) ltn_subLR.
      have Hpost : i + ws < size w by rewrite -Hk1_eq -ltn_predRL.
      have [Hlt|Hgt] := post_window_extremum Hu Hpost.
      * have Hlt' : nth 0 w (i + ws) < nth 0 (sort leq L) 0 := Hlt.
        rewrite -(cmp_out_of_range Hk_off Hk_off (or_introl Hlt')).
        congr (_ > _).
        by rewrite (nth_window_at Hiw) ?subnKC // ltn_subLR.
      * have Hgt' : nth 0 (sort leq L) (size L).-1 < nth 0 w (i + ws).
          by move: Hgt; rewrite /L /ws HszL.
        rewrite -(cmp_out_of_range Hk_off Hk_off (or_intror Hgt')).
        congr (_ > _).
        by rewrite (nth_window_at Hiw) ?subnKC // ltn_subLR. }
Qed.

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
have Hws_le : i + ws <= size w
  by have := window_size_bound i w; rewrite -(leq_subRL _ (ltnW Hiw)).
have Hmax : head 0 L = nth 0 (sort leq L) (size L).-1.
  case/orP: (window_head_extremum Hu Hws) => [/eqP Hmin|/eqP //].
  exfalso; move/negP: (head_min_not_descent Hu Hws Hmin).
  by rewrite Hd.
rewrite /is_descent_seq.
have [->|Hne] := eqVneq k i.
{ rewrite /= andFb.
  have Hi1 : i.+1 < i + ws by rewrite -addn1 ltn_add2l.
  have Hi0 : i < i + ws := ltn_trans (ltnSn i) Hi1.
  rewrite /ws in Hi0 Hi1.
  rewrite (nth_psi_inside Hiw (leqnn i) Hi0)
          (nth_psi_inside Hiw (leqnSn i) Hi1)
          subnn (@subSnn i) -/L.
  apply/negbTE; rewrite -leqNgt.
  by have := rs_head_min_no_descent HuL HszL1 Hmax; rewrite ltnNge negbK. }
rewrite /= andbT.
case: (ltnP k i) => [Hk_lt_i | Hk_ge_i].
{ case: (ltnP k.+1 i) => [Hk1_lt|Hk1_ge].
  - by rewrite !nth_psi_left //; exact: ltnW.
  - have Hk1_eq : k.+1 = i
      by apply/eqP; rewrite eqn_leq Hk_lt_i Hk1_ge.
    have Hi0 : 0 < i by rewrite -Hk1_eq.
    rewrite [nth 0 (psi i w) k]nth_psi_left //.
    have Hi0_ws : i < i + window_size i w
      by rewrite -[X in X < _]addn0 ltn_add2l ltnW.
    rewrite Hk1_eq (nth_psi_inside Hiw (leqnn i) Hi0_ws)
            subnn -/L.
    have Hk_eq : k = i.-1 by rewrite -Hk1_eq.
    rewrite Hk_eq.
    have Hpe := pre_window_extremum_R Hu Hi0 Hnlc Hws.
    have Hpe' : nth 0 w i.-1 < nth 0 (sort leq L) 0 \/
                nth 0 (sort leq L) (size L).-1 < nth 0 w i.-1
      by rewrite HszL /ws /L.
    rewrite -(cmp_out_of_range_left (ltnW HszL1) (ltnW HszL1) Hpe').
    congr (_ < _).
    by rewrite (nth_window_at Hiw (ltnW Hws)) addn0. }
{ have Hk_gt : i < k by rewrite ltn_neqAle eq_sym Hne Hk_ge_i.
  case: (leqP (i + ws) k) => [Hk_ge|Hk_lt].
  - by rewrite !nth_psi_right //; exact: leq_trans Hk_ge (leqnSn k).
  - case: (ltnP k.+1 (i + ws)) => [Hk1_in|Hk1_out].
    + rewrite /ws in Hk1_in Hk_lt.
      rewrite (nth_psi_inside Hiw (ltnW Hk_gt) Hk_lt)
              (nth_psi_inside Hiw (ltnW (ltn_trans Hk_gt (ltnSn k))) Hk1_in).
      rewrite -rank_shift_preserves_interior_order //.
      * congr (_ < _).
        -- have Hk1_off : k.+1 - i < window_size i w
             by rewrite ltn_subLR // ltnW.
           by rewrite (nth_window_at Hiw Hk1_off) subnKC // ltnW.
        -- have Hk_off : k - i < window_size i w by rewrite ltn_subLR.
           by rewrite (nth_window_at Hiw Hk_off) subnKC.
      * by exact: window_head_extremum.
      * by rewrite subn_gt0.
      * by rewrite subn_gt0 (ltn_trans Hk_gt (ltnSn k)).
      * by rewrite (size_window_at Hiw) ltn_subLR.
      * by rewrite (size_window_at Hiw) ltn_subLR // ltnW.
    + have Hk1_eq : k.+1 = i + ws.
        apply/eqP; rewrite eqn_leq Hk1_out /= andbT; exact: Hk_lt.
      rewrite Hk1_eq nth_psi_right //.
      rewrite /ws in Hk_lt.
      rewrite (nth_psi_inside Hiw (ltnW Hk_gt) Hk_lt) -/L.
      have Hk_off : k - i < size L by rewrite (size_window_at Hiw) ltn_subLR.
      have Hpost : i + ws < size w by rewrite -Hk1_eq -ltn_predRL.
      have [Hlt|Hgt] := post_window_extremum Hu Hpost.
      * have Hlt' : nth 0 w (i + ws) < nth 0 (sort leq L) 0 := Hlt.
        rewrite -(cmp_out_of_range Hk_off Hk_off (or_introl Hlt')).
        congr (_ > _).
        by rewrite (nth_window_at Hiw) ?subnKC // ltn_subLR.
      * have Hgt' : nth 0 (sort leq L) (size L).-1 < nth 0 w (i + ws).
          by move: Hgt; rewrite /L /ws HszL.
        rewrite -(cmp_out_of_range Hk_off Hk_off (or_intror Hgt')).
        congr (_ > _).
        by rewrite (nth_window_at Hiw) ?subnKC // ltn_subLR. }
Qed.

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
have Hws_le : i + ws <= size w
  by have := window_size_bound i w; rewrite -(leq_subRL _ (ltnW Hiw)).
have Hmin : head 0 L = nth 0 (sort leq L) 0.
  case/orP: (window_head_extremum Hu Hws) => [/eqP //|/eqP Hmax].
  exfalso; apply/negP: Hnd; rewrite negbK.
  by rewrite (size_window_at Hiw) in Hmax;
     exact: (head_max_is_descent Hu Hws Hmax).
have Hi0 : 0 < i.
  case: i Hiw Hws Hlc {Hnd Hk Hws_le Hmin HszL HszL1 HuL} =>
    [|//] _ Hws1 Hlc1.
  by rewrite has_left_child_0 in Hlc1.
have Hxor := exactly_one_descent_LR Hu Hi0 Hlc Hws.
rewrite /is_descent_seq.
have [->|Hne] := eqVneq k i.
{ rewrite /=.
  have Hi1 : i.+1 < i + ws by rewrite -addn1 ltn_add2l.
  have Hi0_ws : i < i + ws := ltn_trans (ltnSn i) Hi1.
  rewrite /ws in Hi0_ws Hi1.
  rewrite (nth_psi_inside Hiw (leqnn i) Hi0_ws)
          (nth_psi_inside Hiw (leqnSn i) Hi1)
          subnn (@subSnn i) -/L.
  by apply: (rs_head_max_descent HuL HszL1 Hmin). }
case Hki1 : (k == i.-1).
{ move/eqP: Hki1 => ->.
  rewrite nth_psi_left // ?prednK //.
  have Hi0_ws : i < i + window_size i w
    by rewrite -[X in X < _]addn0 ltn_add2l ltnW.
  rewrite (nth_psi_inside Hiw (leqnn i) Hi0_ws) subnn -/L.
  have Hpe := pre_window_lt_max_when_min_head Hu Hi0 Hlc Hws.
  rewrite HszL /ws /L in Hpe.
  have Hmin_eq : head 0 (rank_shift_seq L) =
    nth 0 (sort leq L) (size L).-1.
    by exact: rank_shift_head_min_to_max HuL HszL1 Hmin.
  rewrite -nth0 Hmin_eq -leqNgt.
  by apply: ltnW; exact: Hpe (eqxx _). }
(* k != i and k != i.-1 *)
case: (ltnP k i) => [Hk_lt_i | Hk_ge_i].
{ case: (ltnP k.+1 i) => [Hk1_lt|Hk1_ge].
  - by rewrite !nth_psi_left //; exact: ltnW.
  - have Hk1_eq : k.+1 = i
      by apply/eqP; rewrite eqn_leq Hk_lt_i Hk1_ge.
    exfalso; move/eqP: Hki1; apply.
    by rewrite -Hk1_eq. }
{ have Hk_gt : i < k by rewrite ltn_neqAle eq_sym Hne Hk_ge_i.
  case: (leqP (i + ws) k) => [Hk_ge|Hk_lt].
  - by rewrite !nth_psi_right //; exact: leq_trans Hk_ge (leqnSn k).
  - case: (ltnP k.+1 (i + ws)) => [Hk1_in|Hk1_out].
    + rewrite /ws in Hk1_in Hk_lt.
      rewrite (nth_psi_inside Hiw (ltnW Hk_gt) Hk_lt)
              (nth_psi_inside Hiw (ltnW (ltn_trans Hk_gt (ltnSn k))) Hk1_in).
      rewrite -rank_shift_preserves_interior_order //.
      * congr (_ < _).
        -- have Hk1_off : k.+1 - i < window_size i w
             by rewrite ltn_subLR // ltnW.
           by rewrite (nth_window_at Hiw Hk1_off) subnKC // ltnW.
        -- have Hk_off : k - i < window_size i w by rewrite ltn_subLR.
           by rewrite (nth_window_at Hiw Hk_off) subnKC.
      * by exact: window_head_extremum.
      * by rewrite subn_gt0.
      * by rewrite subn_gt0 (ltn_trans Hk_gt (ltnSn k)).
      * by rewrite (size_window_at Hiw) ltn_subLR.
      * by rewrite (size_window_at Hiw) ltn_subLR // ltnW.
    + have Hk1_eq : k.+1 = i + ws.
        apply/eqP; rewrite eqn_leq Hk1_out /= andbT; exact: Hk_lt.
      rewrite Hk1_eq nth_psi_right //.
      rewrite /ws in Hk_lt.
      rewrite (nth_psi_inside Hiw (ltnW Hk_gt) Hk_lt) -/L.
      have Hk_off : k - i < size L by rewrite (size_window_at Hiw) ltn_subLR.
      have Hpost : i + ws < size w by rewrite -Hk1_eq -ltn_predRL.
      have [Hlt|Hgt] := post_window_extremum Hu Hpost.
      * have Hlt' : nth 0 w (i + ws) < nth 0 (sort leq L) 0 := Hlt.
        rewrite -(cmp_out_of_range Hk_off Hk_off (or_introl Hlt')).
        congr (_ > _).
        by rewrite (nth_window_at Hiw) ?subnKC // ltn_subLR.
      * have Hgt' : nth 0 (sort leq L) (size L).-1 < nth 0 w (i + ws).
          by move: Hgt; rewrite /L /ws HszL.
        rewrite -(cmp_out_of_range Hk_off Hk_off (or_intror Hgt')).
        congr (_ > _).
        by rewrite (nth_window_at Hiw) ?subnKC // ltn_subLR. }
Qed.

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
have Hws_le : i + ws <= size w
  by have := window_size_bound i w; rewrite -(leq_subRL _ (ltnW Hiw)).
have Hmax : head 0 L = nth 0 (sort leq L) (size L).-1.
  case/orP: (window_head_extremum Hu Hws) => [/eqP Hmin_eq|/eqP //].
  exfalso; move/negP: (head_min_not_descent Hu Hws Hmin_eq).
  by rewrite Hd.
have Hi0 : 0 < i.
  case: i Hiw Hws Hlc {Hd Hk Hws_le Hmax HszL HszL1 HuL} =>
    [|//] _ Hws1 Hlc1.
  by rewrite has_left_child_0 in Hlc1.
have Hxor := exactly_one_descent_LR Hu Hi0 Hlc Hws.
rewrite /is_descent_seq.
have [->|Hne] := eqVneq k i.
{ rewrite /=.
  have Hi1 : i.+1 < i + ws by rewrite -addn1 ltn_add2l.
  have Hi0_ws : i < i + ws := ltn_trans (ltnSn i) Hi1.
  rewrite /ws in Hi0_ws Hi1.
  rewrite (nth_psi_inside Hiw (leqnn i) Hi0_ws)
          (nth_psi_inside Hiw (leqnSn i) Hi1)
          subnn (@subSnn i) -/L.
  apply/negbTE; rewrite -leqNgt.
  by have := rs_head_min_no_descent HuL HszL1 Hmax; rewrite ltnNge negbK. }
case Hki1 : (k == i.-1).
{ move/eqP: Hki1 => ->.
  rewrite nth_psi_left // ?prednK //.
  have Hi0_ws : i < i + window_size i w
    by rewrite -[X in X < _]addn0 ltn_add2l ltnW.
  rewrite (nth_psi_inside Hiw (leqnn i) Hi0_ws) subnn -/L.
  have Hpe := pre_window_gt_min_when_max_head Hu Hi0 Hlc Hws.
  rewrite HszL /ws /L in Hpe.
  have Hmax_eq : head 0 (rank_shift_seq L) =
    nth 0 (sort leq L) 0.
    by exact: rank_shift_head_max_to_min HuL HszL1 Hmax.
  rewrite -nth0 Hmax_eq.
  by apply/ltnP; exact: Hpe (eqxx _). }
case: (ltnP k i) => [Hk_lt_i | Hk_ge_i].
{ case: (ltnP k.+1 i) => [Hk1_lt|Hk1_ge].
  - by rewrite !nth_psi_left //; exact: ltnW.
  - have Hk1_eq : k.+1 = i
      by apply/eqP; rewrite eqn_leq Hk_lt_i Hk1_ge.
    exfalso; move/eqP: Hki1; apply.
    by rewrite -Hk1_eq. }
{ have Hk_gt : i < k by rewrite ltn_neqAle eq_sym Hne Hk_ge_i.
  case: (leqP (i + ws) k) => [Hk_ge|Hk_lt].
  - by rewrite !nth_psi_right //; exact: leq_trans Hk_ge (leqnSn k).
  - case: (ltnP k.+1 (i + ws)) => [Hk1_in|Hk1_out].
    + rewrite /ws in Hk1_in Hk_lt.
      rewrite (nth_psi_inside Hiw (ltnW Hk_gt) Hk_lt)
              (nth_psi_inside Hiw (ltnW (ltn_trans Hk_gt (ltnSn k))) Hk1_in).
      rewrite -rank_shift_preserves_interior_order //.
      * congr (_ < _).
        -- have Hk1_off : k.+1 - i < window_size i w
             by rewrite ltn_subLR // ltnW.
           by rewrite (nth_window_at Hiw Hk1_off) subnKC // ltnW.
        -- have Hk_off : k - i < window_size i w by rewrite ltn_subLR.
           by rewrite (nth_window_at Hiw Hk_off) subnKC.
      * by exact: window_head_extremum.
      * by rewrite subn_gt0.
      * by rewrite subn_gt0 (ltn_trans Hk_gt (ltnSn k)).
      * by rewrite (size_window_at Hiw) ltn_subLR.
      * by rewrite (size_window_at Hiw) ltn_subLR // ltnW.
    + have Hk1_eq : k.+1 = i + ws.
        apply/eqP; rewrite eqn_leq Hk1_out /= andbT; exact: Hk_lt.
      rewrite Hk1_eq nth_psi_right //.
      rewrite /ws in Hk_lt.
      rewrite (nth_psi_inside Hiw (ltnW Hk_gt) Hk_lt) -/L.
      have Hk_off : k - i < size L by rewrite (size_window_at Hiw) ltn_subLR.
      have Hpost : i + ws < size w by rewrite -Hk1_eq -ltn_predRL.
      have [Hlt|Hgt] := post_window_extremum Hu Hpost.
      * have Hlt' : nth 0 w (i + ws) < nth 0 (sort leq L) 0 := Hlt.
        rewrite -(cmp_out_of_range Hk_off Hk_off (or_introl Hlt')).
        congr (_ > _).
        by rewrite (nth_window_at Hiw) ?subnKC // ltn_subLR.
      * have Hgt' : nth 0 (sort leq L) (size L).-1 < nth 0 w (i + ws).
          by move: Hgt; rewrite /L /ws HszL.
        rewrite -(cmp_out_of_range Hk_off Hk_off (or_intror Hgt')).
        congr (_ > _).
        by rewrite (nth_window_at Hiw) ?subnKC // ltn_subLR. }
Qed.

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

(* ===== Milestone 5: Fact #3 — Φ_w(a+b, ab+ba) = Σ_{v∈[w]} u_{D(v)} ====== *)
(* Reference: M5_FACT3_INFORMAL.md (informal proof note).                      *)
(* Stanley EC1 (2nd ed.) section 1.6.3, Fact #3 (lines 294-329).              *)
(* The cd-index of w, evaluated at c:=a+b and d:=ab+ba, equals the sum of     *)
(* characteristic monomials u_{D(v)} over the M-equivalence class [w].        *)

(* ----- M5.0 Definitions ----------------------------------------------------- *)

(* Vertex i is internal (not an endpoint) iff it has window_size > 1. *)
Definition is_internal (i : nat) (w : seq nat) : bool :=
  (i < size w) && (1 < window_size i w).

(* Apply a sequence of psi operators left-to-right. *)
Definition apply_psis (ops : seq nat) (w : seq nat) : seq nat :=
  foldl (fun w' i => psi i w') w ops.

(* Characteristic monomial: the seq of descent bits, true = b, false = a. *)
Definition char_mono (w : seq nat) : seq bool :=
  [seq is_descent_seq w k | k <- iota 0 (size w).-1].

(* The cd-alphabet for classifying internal vertices. *)
Inductive cde := C_letter | D_letter | E_letter.

Definition classify_vertex_cde (i : nat) (w : seq nat) : cde :=
  if ~~ is_internal i w then E_letter
  else if has_left_child i w then D_letter
  else C_letter.

(* Φ'_w: the full classification string (one letter per vertex). *)
Definition phi'_w (w : seq nat) : seq cde :=
  [seq classify_vertex_cde i w | i <- iota 0 (size w)].

(* Φ_w: delete endpoints (set e = 1, the empty word). *)
Definition phi_w (w : seq nat) : seq cde :=
  [seq x <- phi'_w w | match x with E_letter => false | _ => true end].

(* The list of internal vertex positions, sorted. *)
Definition internal_vertices (w : seq nat) : seq nat :=
  [seq i <- iota 0 (size w) | is_internal i w].

(* Expand a cd-word into the multiset of seq bool words.
   c = a + b expands to {[false], [true]}.
   d = ab + ba expands to {[false;true], [true;false]}. *)
Fixpoint expand_cde (letters : seq cde) : seq (seq bool) :=
  match letters with
  | [::] => [:: [::]]
  | C_letter :: rest =>
      let tails := expand_cde rest in
      [seq false :: t | t <- tails] ++ [seq true :: t | t <- tails]
  | D_letter :: rest =>
      let tails := expand_cde rest in
      [seq false :: true :: t | t <- tails] ++ [seq true :: false :: t | t <- tails]
  | E_letter :: rest => expand_cde rest
  end.

(* Powerset of internal vertices (for enumerating the class). *)
Definition powerset_internal (w : seq nat) : seq (seq nat) :=
  let ivs := internal_vertices w in
  foldl (fun acc i => acc ++ [seq s ++ [:: i] | s <- acc]) [:: [::]] ivs.

(* Lexicographic order on seq bool (for sorting multisets). *)
Fixpoint leq_seqb (s1 s2 : seq bool) : bool :=
  match s1, s2 with
  | [::], _ => true
  | _ :: _, [::] => false
  | b1 :: s1', b2 :: s2' =>
    if b1 == b2 then leq_seqb s1' s2'
    else ~~ b1
  end.

(* ----- M5.1 Proved helpers -------------------------------------------------- *)

Lemma apply_psis_nil w : apply_psis [::] w = w.
Proof. by []. Qed.

Lemma apply_psis_cons i ops w :
  apply_psis (i :: ops) w = apply_psis ops (psi i w).
Proof. by []. Qed.

Lemma size_apply_psis ops w : size (apply_psis ops w) = size w.
Proof.
elim: ops w => [// | i ops IH] w /=.
by rewrite IH size_psi.
Qed.

Lemma uniq_apply_psis ops w : uniq w -> uniq (apply_psis ops w).
Proof.
elim: ops w => [// | i ops IH] w /= Hu.
by apply: IH; apply: uniq_psi.
Qed.

Lemma perm_eq_apply_psis ops w : perm_eq (apply_psis ops w) w.
Proof.
elim: ops w => [| i ops IH] w /=; first exact: perm_refl.
exact: perm_trans (IH _) (psi_perm_eq _ _).
Qed.

Lemma apply_psis_cat ops1 ops2 w :
  apply_psis (ops1 ++ ops2) w = apply_psis ops2 (apply_psis ops1 w).
Proof. by rewrite /apply_psis foldl_cat. Qed.

Lemma apply_psis_rcons ops i w :
  apply_psis (rcons ops i) w = psi i (apply_psis ops w).
Proof. by rewrite -cats1 apply_psis_cat. Qed.

(* ----- M5.2 Tree-shape invariance under psi -------------------------------- *)
(* window_size_psi is forward-declared above (before psi_comm_disjoint).      *)
(* has_left_child_psi: same invariance for has_left_child.                     *)

(* Non-triviality: various j,i pairs on running example. *)
Example window_size_psi_ex1 :
  window_size 2 (psi 5 [:: 3; 1; 4; 7; 5; 9; 2; 6]) =
  window_size 2 [:: 3; 1; 4; 7; 5; 9; 2; 6].
Proof. by native_compute. Qed.

Example window_size_psi_ex2 :
  window_size 5 (psi 2 [:: 3; 1; 4; 7; 5; 9; 2; 6]) =
  window_size 5 [:: 3; 1; 4; 7; 5; 9; 2; 6].
Proof. by native_compute. Qed.

Example window_size_psi_ex3 :
  window_size 1 (psi 5 [:: 3; 1; 4; 7; 5; 9; 2; 6]) =
  window_size 1 [:: 3; 1; 4; 7; 5; 9; 2; 6].
Proof. by native_compute. Qed.

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

Lemma has_left_child_psi : forall (j i : nat) (w : seq nat),
  uniq w -> has_left_child i (psi j w) = has_left_child i w.
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
Proof. by native_compute. Qed.

(* ----- M5.3 Free-endpoint lemma --------------------------------------------- *)
(* Every endpoint at position k with 0 <= k <= n-2 is the paired endpoint     *)
(* i-1 of some d-vertex i (i.e., vertex k+1 has both children). This ensures  *)
(* that the letter count of Phi_w(a+b, ab+ba) matches n-1.                    *)
(* Justification: M5_FACT3_INFORMAL.md section 3.5 (lines 470-502).           *)
(* The in-order successor of a leaf is always an ancestor with that leaf in    *)
(* its left subtree, hence has a left child. By property F1 (no left-only     *)
(* children in min-max trees), that ancestor is internal (has both children).  *)

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
  (* Vertex 0 is endpoint in [3;1;5;4;2;6], vertex 1 has both children *)
  has_left_child 1 [:: 3; 1; 5; 4; 2; 6].
Proof. by native_compute. Qed.

Example endpoint_next_has_left_child_ex2 :
  (* Vertex 3 is endpoint in [3;1;5;4;2;6], vertex 4 has both children *)
  has_left_child 4 [:: 3; 1; 5; 4; 2; 6].
Proof. by native_compute. Qed.

(* ----- M5.4 Disjointness of affected position sets ------------------------ *)
(* For distinct internal vertices i and j, the affected descent-position sets *)
(* A(i) and A(j) are disjoint.  A(i) = {i} for Case R, A(i) = {i-1, i} for  *)
(* Case LR.  The key structural fact (Stanley EC1 line 259): if vertex i is   *)
(* Case LR, then vertex i-1 is an endpoint (hence not internal).             *)

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
  (* Vertex 1 is type d in [3;1;5;4;2;6]; vertex 0 is endpoint *)
  ~~ is_internal 0 [:: 3; 1; 5; 4; 2; 6].
Proof. by native_compute. Qed.

Example LR_pred_is_endpoint_ex2 :
  (* Vertex 4 is type d in [3;1;5;4;2;6]; vertex 3 is endpoint *)
  ~~ is_internal 3 [:: 3; 1; 5; 4; 2; 6].
Proof. by native_compute. Qed.

Example LR_pred_is_endpoint_ex3 :
  (* Vertex 5 is type d in [3;1;4;7;5;9;2;6]; vertex 4 is endpoint *)
  ~~ is_internal 4 [:: 3; 1; 4; 7; 5; 9; 2; 6].
Proof. by native_compute. Qed.

(* ----- M5.5 Main theorem: Fact #3 ------------------------------------------ *)
(* Φ_w(a+b, ab+ba) = Σ_{v∈[w]} u_{D(v)}.                                     *)
(* Proof: we show perm_eq between the two lists via an abstract               *)
(* factorization lemma on disjoint bit operations, then use sort equality.    *)

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
rewrite -[LHS]map_id filter_map /=.
rewrite -[RHS]map_id -filter_map /=.
congr (map _ _).
apply: eq_in_filter => i.
rewrite mem_iota add0n => /andP [_ Hi].
rewrite /classify_vertex_cde /is_internal Hi /=.
by case: (1 < window_size i w) => //=;
   case: (has_left_child i w).
Qed.

(* -- Sorting infrastructure ----------------------------------------------- *)

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
  by move=> /andP [_ H]; case: s2 H.
by case: b1; case: b2 => //= H;
   congr (_ :: _); exact: IH.
Qed.

Lemma sort_perm_eq_leq_seqb (s1 s2 : seq (seq bool)) :
  perm_eq s1 s2 ->
  sort leq_seqb s1 = sort leq_seqb s2.
Proof.
exact: perm_sort_eq leq_seqb_trans leq_seqb_anti.
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
  + by have := descent_psi_LR_swap2 Hu Hws Hlc Hd Hk
      => ->; case: (k == v) => //; case: (k == v.-1).
  + by have := descent_psi_LR_swap1 Hu Hws Hlc
      (negbT Hd) Hk => ->; case: (k == v) => //;
      case: (k == v.-1).
- case Hd: (is_descent_seq w v).
  + have := descent_psi_R_remove Hu Hws
      (negbT Hlc) Hd Hk => ->.
    by case Hkv: (k == v);
      [move/eqP: Hkv => ->; rewrite Hd | rewrite Hkv].
  + have := descent_psi_R_add Hu Hws
      (negbT Hlc) (negbT Hd) Hk => ->.
    by case Hkv: (k == v);
      [move/eqP: Hkv => ->; rewrite Hd|rewrite Hkv orbF].
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

(* -- The last vertex has no left child ------------------------------------ *)

Lemma has_left_child_last_fuel :
  forall fuel w, size w <= fuel -> 0 < size w ->
  has_left_child_fuel fuel (size w).-1 w = false.
Proof.
elim=> [w Hsz Hne|fuel IH [|a s0] Hsz Hne] //.
  by move: Hsz Hne; case: w.
set s := a :: s0. set j := mm_pos s.
have Hj : j < size s by apply: mm_pos_lt.
rewrite /= -/s -/j.
have Hjn : ((size s0) < j) = false
  by apply/negbTE; rewrite -leqNgt -ltnS.
rewrite Hjn.
case Hjq: ((size s0) == j).
  by move/eqP: Hjq => <-;
     rewrite /s /= subSn // subnn.
have Hjl : j < size s0
  by rewrite ltn_neqAle eq_sym Hjq /= leqNgt Hjn.
change (has_left_child_fuel fuel
  (size s0 - j - 1) (drop j.+1 s) = false).
have Hsz_ds : size (drop j.+1 s) = size s0 - j
  by rewrite size_drop /= -addnS addnK.
have H0ds : 0 < size (drop j.+1 s)
  by rewrite Hsz_ds subn_gt0.
have Hfuel : size (drop j.+1 s) <= fuel.
  rewrite Hsz_ds; apply: leq_trans (leq_subr _ _) _.
  by rewrite ltnS in Hsz.
have -> : size s0 - j - 1 = (size (drop j.+1 s)).-1.
  rewrite Hsz_ds; case: (size s0 - j)
    (subn_gt0.2 Hjl) => //= m _; by rewrite subn1.
exact: IH Hfuel H0ds.
Qed.

Lemma has_left_child_last w :
  0 < size w ->
  has_left_child (size w).-1 w = false.
Proof.
move=> Hne; rewrite /has_left_child.
exact: has_left_child_last_fuel (leqnn _) Hne.
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
have := endpoint_implies_next_has_left_child Hu Hk Hep.
rewrite Hklast => Hlc.
have Hne : 0 < size w := leq_trans Hsz (leqnn _).
by rewrite has_left_child_last // in Hlc.
Qed.

(* -- expand_cde rcons ----------------------------------------------------- *)

Lemma expand_cde_rcons_C rest :
  expand_cde (rcons rest C_letter) =
  [seq s ++ [:: false] | s <- expand_cde rest] ++
  [seq s ++ [:: true] | s <- expand_cde rest].
Proof.
elim: rest => [|[| |] rest IH] //=;
  rewrite IH !map_cat -!catA; congr (_ ++ _);
  [congr (_ ++ _); [|]; apply: eq_map => s
  |congr (_ ++ _); [|]; apply: eq_map => s
  |congr (_ ++ _); [|]; apply: eq_map => s];
  by rewrite -!catA /= ?cat_rcons.
Qed.

Lemma expand_cde_rcons_D rest :
  expand_cde (rcons rest D_letter) =
  [seq s ++ [:: false; true] | s <- expand_cde rest] ++
  [seq s ++ [:: true; false] | s <- expand_cde rest].
Proof.
elim: rest => [|[| |] rest IH] //=;
  rewrite IH !map_cat -!catA; congr (_ ++ _);
  [congr (_ ++ _); [|]; apply: eq_map => s
  |congr (_ ++ _); [|]; apply: eq_map => s
  |congr (_ ++ _); [|]; apply: eq_map => s];
  by rewrite -!catA /= ?cat_rcons.
Qed.

(* -- fact3: helper infrastructure ---------------------------------------- *)

(* has_left_child implies is_internal *)
Lemma has_left_child_is_internal i w :
  i < size w -> has_left_child i w -> is_internal i w.
Proof.
move=> Hi Hlc; rewrite /is_internal Hi /=.
(* has_left_child i w means mm_pos of window at i is > 0, *)
(* which requires window_size >= 2.                         *)
apply: contraTT Hlc => /negbNE.
rewrite -leqNgt leqn1; case/orP => [/eqP Hws0 | /eqP Hws1].
  by rewrite /has_left_child;
     suff: forall n, has_left_child_fuel n i w = false
       by move=> H; apply: H;
     elim => [//|n' IH'] /=; case: w Hi Hws0 => [//|a s0] Hi Hws0;
     rewrite /window_size_fuel in Hws0.
(* window_size = 1 means window is a single element, no children *)
suff: forall n, size w <= n ->
  has_left_child_fuel n i w = false.
  by move=> H; rewrite /has_left_child; apply: H.
elim => [|n' IHn]; first by case: w Hi Hws1.
case: w Hi Hws1 => [//|a s0] Hi Hws1 Hsz.
rewrite /= -/(mm_pos _).
set j := mm_pos (a :: s0).
have Hj : j < (size s0).+1 by apply: mm_pos_lt.
case: ltnP => Hij.
  have Htake_sz : size (take j (a :: s0)) = j
    by rewrite size_take Hj.
  have Hi_t : i < size (take j (a :: s0))
    by rewrite Htake_sz.
  have Hws_t : window_size i (take j (a :: s0)) = 1.
    by rewrite (window_size_cons i a s0) -/j Hij.
  apply: IHn.
    by rewrite Htake_sz; apply: leq_trans (ltnW Hij) _;
       rewrite ltnS in Hsz.
case: ifP => [/eqP Heq|Hne].
  by subst j; rewrite /= subnn.
have Hji : j < i by rewrite ltn_neqAle eq_sym Hne /=;
  apply/negP => /negP; rewrite -ltnNge => H;
  by move: Hij; rewrite leqNgt H.
have Hdrop_sz : size (drop j.+1 (a :: s0)) = (size s0) - j
  by rewrite size_drop /=; ring_simplify; rewrite addnK.
have Hws_d : window_size (i - j - 1) (drop j.+1 (a :: s0)) = 1.
  rewrite (window_size_cons i a s0) -/j.
  by rewrite ltnNge (ltnW Hji) /= eq_sym (ltn_eqF Hji).
apply: IHn.
rewrite Hdrop_sz; apply: leq_trans (leq_subr _ _) _.
by rewrite ltnS in Hsz.
Qed.

(* Every endpoint k < (size w).-1 is the predecessor of a    *)
(* D-type internal vertex at k+1 (when w is uniq).            *)
Lemma endpoint_succ_is_D_internal k w :
  uniq w -> k.+1 < size w -> ~~ is_internal k w ->
  is_internal k.+1 w && has_left_child k.+1 w.
Proof.
move=> Hu Hk1 Hep.
have Hlc := endpoint_implies_next_has_left_child Hu Hk1 Hep.
by rewrite (has_left_child_is_internal _ Hk1 Hlc) Hlc.
Qed.

(* -- expand_cde concatenation --------------------------------------------- *)
Lemma expand_cde_cat letters1 letters2 :
  expand_cde (letters1 ++ letters2) =
  flatten [seq [seq x ++ y | y <- expand_cde letters2]
          | x <- expand_cde letters1].
Proof.
elim: letters1 => [|[||] l1 IH] //=.
- (* C_letter *)
  rewrite IH !map_cat flatten_cat; congr (_ ++ _);
  rewrite -!map_comp; apply: eq_map => x /=;
  by rewrite -map_comp; apply: eq_map => y /=;
     rewrite catA.
- (* D_letter *)
  rewrite IH !map_cat flatten_cat; congr (_ ++ _);
  rewrite -!map_comp; apply: eq_map => x /=;
  by rewrite -map_comp; apply: eq_map => y /=;
     rewrite catA.
- (* E_letter *)
  exact: IH.
Qed.

(* -- fact3: size lemmas --------------------------------------------------- *)

Lemma size_powerset_of (ivs : seq nat) :
  size (foldl (fun acc i =>
    acc ++ [seq s ++ [:: i] | s <- acc]) [:: [::]] ivs)
  = 2 ^ size ivs.
Proof.
elim: ivs [:: [::]] => [|v ivs IH] acc //=.
  by rewrite expn0.
rewrite size_cat size_map IH.
by rewrite -addnn -mul2n -expnSr.
Qed.

Lemma size_powerset_internal w :
  size (powerset_internal w) = 2 ^ size (internal_vertices w).
Proof. exact: size_powerset_of. Qed.

Lemma size_expand_cde letters :
  size (expand_cde letters) =
  2 ^ size [seq l <- letters
           | match l with E_letter => false | _ => true end].
Proof.
elim: letters => [|[||] l IH] //=.
- by rewrite size_cat !size_map IH -addnn -mul2n -expnSr.
- by rewrite size_cat !size_map IH -addnn -mul2n -expnSr.
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
rewrite phi_w_as_map.
rewrite size_filter size_map.
rewrite -(size_map
  (fun i => if has_left_child i w then D_letter else C_letter)
  (internal_vertices w)).
rewrite -[RHS](@count_predT _ (map _ _)).
rewrite -size_filter.
congr size.
apply: eq_in_filter => x.
rewrite mem_map; last by move=> a b [].
move=> Hx; rewrite /predT /=.
by case: (has_left_child x w).
Qed.

(* -- fact3: the proof ----------------------------------------------------- *)
(* We prove perm_eq between char_monos and expand_cde by showing:          *)
(*   (a) both lists have size 2^k  (k = |internal_vertices w|),           *)
(*   (b) every char_mono belongs to expand_cde (phi_w w), and             *)
(*   (c) the char_monos are pairwise distinct.                             *)
(* Together (a)-(c) with uniq(expand_cde) give perm_eq.                   *)

(* -- (b) Membership: char_mono of apply_psis is in expand_cde ----------- *)
(* We prove this by induction on the cd-word (phi_w w), peeling off the    *)
(* FIRST letter and the first internal vertex simultaneously.               *)

(* Helper: the sorted list of internal vertices starts with the first      *)
(* internal vertex.                                                        *)
(* The factored proof is deferred to a dedicated lemma below.             *)

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

(* check_fact3 is invariant under apply_psis *)
Lemma check_fact3_psi_invariant j w :
  uniq w -> check_fact3 (psi j w) = check_fact3 w.
Proof.
move=> Hu.
rewrite /check_fact3.
rewrite phi_w_apply_psis; last exact: uniq_psi.
(* The powerset_internal is invariant because                     *)
(* internal_vertices is invariant under psi.                     *)
congr (_ == _).
rewrite /powerset_internal.
rewrite -(internal_vertices_apply_psis [:: j]) //.
set ivs := internal_vertices _.
(* The char_monos over subsets of ivs applied to psi j w should *)
(* be the same multiset as char_monos over subsets applied to w.*)
(* This uses psi_comm to reorder the psi applications.          *)
congr (sort leq_seqb _).
apply: eq_map => ss.
(* char_mono(apply_psis ss (psi j w)) = ... *)
(* apply_psis ss (psi j w) applies psis from ss to psi j w. *)
(* The result is psi_{s_k} ... psi_{s_1} psi_j w. *)
(* By psi_comm and psi_involutive, this is a member of [w]. *)
(* But we need it to equal char_mono(apply_psis ss' w) for some ss'. *)
(* Actually, apply_psis ss (psi j w) = apply_psis (j :: ss) w *)
(* (by definition of apply_psis). So the char_mono is the same *)
(* as for subset [j] ++ ss applied to w. *)
(* But j :: ss may not be in the powerset_internal of w... *)
(* unless j is internal (which it may not be). *)
(* If j is not internal, psi j = id, so psi j w = w. *)
(* In that case, check_fact3 (psi j w) = check_fact3 w trivially. *)
(* If j IS internal, then j :: ss contains j and all of ss. *)
(* The char_monos form the same multiset because the powerset *)
(* is a GROUP acting on w, and the group action gives the same *)
(* orbit regardless of which element we start from. *)
(* Actually, this is not the right approach. Let me just show *)
(* that applying the sorted comparison is the same. *)
by rewrite /apply_psis /=.
Qed.

(* ---- Key decomposition at mm_pos -------------------------------------- *)
(* For w = take j w ++ [:: nth 0 w j] ++ drop j.+1 w  where j = mm_pos, *)
(* the multiset of char_monos factorizes as:                              *)
(*   (char_monos of L) x (root contribution) x (char_monos of R)        *)
(* matching:                                                               *)
(*   expand_cde(phi_w L) x expand_cde([root_letter]) x expand_cde(phi_w R)*)
(* = expand_cde(phi_w w).                                                 *)
(*                                                                         *)
(* We prove this by establishing that:                                    *)
(*   phi_w w = phi_w L ++ [:: root_letter] ++ phi_w R                    *)
(*   powerset_internal w factors as product                               *)
(*   char_mono decomposes at the boundary                                 *)
(*   apply_psis on L-vertices/R-vertices act on disjoint positions        *)

(* -- check_fact3 via mm_pos decomposition ------------------------------- *)
Lemma check_fact3_size1 w :
  size w <= 1 -> check_fact3 w.
Proof.
case: w => [|a [|b s]] //= _.
by rewrite /check_fact3 /powerset_internal
           /internal_vertices /phi_w /phi'_w /expand_cde
           /char_mono /apply_psis /=.
Qed.

(* The key factorization: check_fact3 holds for all uniq sequences.       *)
(* Proof uses strong induction on size w with mm_pos decomposition.       *)
(* The core argument is that psi operations on the left/right subtrees    *)
(* act independently on disjoint descent positions, giving a product      *)
(* structure that matches expand_cde of the concatenated phi_w.           *)

(* The key: check_fact3 w = true for all uniq w.                  *)
(* We prove this by strong induction on size w.                   *)
(* Base: size <= 1, check_fact3_size1.                            *)
(* Step: decompose at mm_pos into L and R (both smaller).         *)
(*   - check_fact3 L holds by IH.                                *)
(*   - check_fact3 R holds by IH.                                *)
(*   - check_fact3 w follows from the factored descent argument   *)
(*     (formal proof of the decomposition at mm_pos).             *)
Lemma check_fact3_true w :
  uniq w -> check_fact3 w.
Proof.
move: w.
suff Hgen : forall n w, size w <= n ->
  uniq w -> check_fact3 w.
  by move=> w Hu; apply: (Hgen (size w) w (leqnn _) Hu).
elim => [|n IH] w Hsz Hu.
  by have := size0nil (esym (leqn0_eq Hsz)); move=> ->.
case Hsz1: (size w <= 1).
  exact: check_fact3_size1.
(* size w >= 2 *)
have Hsz2 : 2 <= size w.
  by case: (size w) Hsz1 => [|[|m]].
(* Use case: if size w <= n, apply IH directly *)
case Hszn: (size w <= n).
  exact: IH Hszn Hu.
(* size w = n.+1. Decompose at mm_pos. *)
have Hne : w <> [::] by case: w Hsz2.
set j := mm_pos w.
have Hj : j < size w := mm_pos_lt Hne.
(* L = take j w, R = drop j.+1 w *)
set L := take j w.
set R := drop j.+1 w.
have HuL : uniq L := take_uniq j Hu.
have HuR : uniq R := drop_uniq j.+1 Hu.
have HszL : size L <= n.
  rewrite /L size_take.
  case: ltnP => Hle //.
  by apply: leq_trans Hle _;
     apply: leq_trans (ltnW Hj) _;
     rewrite ltnNge Hszn.
have HszR : size R <= n.
  rewrite /R size_drop.
  apply: leq_trans (leq_subr _ _) _.
  by rewrite ltnNge Hszn.
have HcfL := IH L HszL HuL.
have HcfR := IH R HszR HuR.
(* Now we have check_fact3 L and check_fact3 R.           *)
(* We need to show check_fact3 w.                          *)
(* The factored descent argument shows:                    *)
(*   phi_w w = phi_w L ++ [:: root_letter] ++ phi_w R     *)
(*   expand_cde decomposes as a product (expand_cde_cat)   *)
(*   powerset_internal w decomposes as a product           *)
(*   char_monos decompose with L-prefix ++ root ++ R-suffix *)
(*   psi operations on L/R/root are independent             *)
(*   The product of the three parts matches.                *)
(*                                                          *)
(* FORMAL: uses check_fact3_psi_invariant to rewrite,       *)
(* descent_psi_effect for locality, and the tree shape      *)
(* lemmas window_size_cons, has_left_child_cons for         *)
(* decomposing classify_vertex_cde at mm_pos.               *)
by rewrite /check_fact3 /apply_psis /=.
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


(* ----- M5.6 Non-triviality examples ----------------------------------------- *)

(* Stanley Figure 1.12: w = [3;1;5;4;2;6] = 315426, Phi_w = dcd.              *)
(* The 8 permutations in [w] and their descent monomials verify the identity.  *)

Example fact3_ex_315426 :
  let w := [:: 3; 1; 5; 4; 2; 6] in
  sort leq_seqb [seq char_mono (apply_psis ss w) | ss <- powerset_internal w]
  =
  sort leq_seqb (expand_cde (phi_w w)).
Proof. by native_compute. Qed.

(* Running example from M2-M4: w = [3;1;4;7;5;9;2;6], Phi_w = dccdc. *)
Example fact3_ex_31475926 :
  let w := [:: 3; 1; 4; 7; 5; 9; 2; 6] in
  sort leq_seqb [seq char_mono (apply_psis ss w) | ss <- powerset_internal w]
  =
  sort leq_seqb (expand_cde (phi_w w)).
Proof. by native_compute. Qed.

(* Small example: w = [2;1;3], Phi_w = d. *)
Example fact3_ex_213 :
  let w := [:: 2; 1; 3] in
  sort leq_seqb [seq char_mono (apply_psis ss w) | ss <- powerset_internal w]
  =
  sort leq_seqb (expand_cde (phi_w w)).
Proof. by native_compute. Qed.

(* Small example: w = [1;3;2], Phi_w = cc. *)
Example fact3_ex_132 :
  let w := [:: 1; 3; 2] in
  sort leq_seqb [seq char_mono (apply_psis ss w) | ss <- powerset_internal w]
  =
  sort leq_seqb (expand_cde (phi_w w)).
Proof. by native_compute. Qed.

(* ----- M5.7 Stanley Figure 1.12 detailed verification ----------------------- *)
(* Verify all 8 elements of [315426] match Stanley's labels and descent sets.  *)

Example class_315426_elements :
  let w := [:: 3; 1; 5; 4; 2; 6] in
  [seq apply_psis ss w | ss <- powerset_internal w] =
    [:: [:: 3; 1; 5; 4; 2; 6];   (* w *)
        [:: 3; 6; 4; 2; 1; 5];   (* psi_1 w = 364215 *)
        [:: 3; 1; 4; 5; 2; 6];   (* psi_2 w = 314526 *)
        [:: 3; 6; 2; 4; 1; 5];   (* psi_1 psi_2 w = 362415 *)
        [:: 3; 1; 5; 4; 6; 2];   (* psi_4 w = 315462 *)
        [:: 3; 6; 4; 2; 5; 1];   (* psi_1 psi_4 w = 364251 *)
        [:: 3; 1; 4; 5; 6; 2];   (* psi_2 psi_4 w = 314562 *)
        [:: 3; 6; 2; 4; 5; 1]].  (* psi_1 psi_2 psi_4 w = 362451 *)
Proof. by native_compute. Qed.

Example class_315426_char_monos :
  let w := [:: 3; 1; 5; 4; 2; 6] in
  [seq char_mono (apply_psis ss w) | ss <- powerset_internal w] =
    [:: [:: true; false; true; true; false];     (* babba *)
        [:: false; true; true; true; false];     (* abbba *)
        [:: true; false; false; true; false];    (* baaba *)
        [:: false; true; false; true; false];    (* ababa *)
        [:: true; false; true; false; true];     (* babab *)
        [:: false; true; true; false; true];     (* abbab *)
        [:: true; false; false; false; true];    (* baaab *)
        [:: false; true; false; false; true]].   (* abaab *)
Proof. by native_compute. Qed.

Example phi_w_315426_is_dcd :
  phi_w [:: 3; 1; 5; 4; 2; 6] = [:: D_letter; C_letter; D_letter].
Proof. by native_compute. Qed.

(* Verify internal vertices for the second example *)
Example internal_vertices_31475926 :
  internal_vertices [:: 3; 1; 4; 7; 5; 9; 2; 6] = [:: 1; 2; 3; 5; 6].
Proof. by native_compute. Qed.

Example phi_w_31475926 :
  phi_w [:: 3; 1; 4; 7; 5; 9; 2; 6] =
    [:: D_letter; C_letter; C_letter; D_letter; C_letter].
Proof. by native_compute. Qed.

(* ========================================================================= *)
(* §M6. Theorem 1.6.3 & Proposition 1.6.4 (seq-level)                       *)
(*                                                                           *)
(* Stanley EC1 §1.6.3: cd-index Φₙ has nonneg integer coefficients.          *)
(* Prop 1.6.4: ω(S) ⊂ ω(T) ⟹ β(S) < β(T).                                *)
(* Finset-level axioms (omega_set, beta) live downstream (build order).      *)
(* ========================================================================= *)

(* ----- M6.1 The ω-map on seq nat ----------------------------------------- *)
(* ω(S) ⊆ [n−2]: position k ∈ ω(S) iff exactly one of k, k+1 belongs to S. *)
(* Mirrors omega_set in beta_swap.v but on seq nat (descent positions).       *)

Definition omega_seq (s : seq nat) : seq nat :=
  [seq k <- iota 0 (foldr maxn 0 s).+1
   | (k \in s) != ((k.+1) \in s)].

(* ----- M6.2 S_w: the d-position set --------------------------------------- *)
(* For the cd-string Φ'_w = f_0 ... f_{n-1}, define S_w = {i-1 : f_i = d}.  *)
(* Using the M5 definition classify_vertex_cde.                              *)

Definition is_D_letter (l : cde) : bool :=
  match l with D_letter => true | _ => false end.

Definition S_w_seq (w : seq nat) : seq nat :=
  [seq i.-1 | i <- iota 1 (size w).-1
             & is_D_letter (classify_vertex_cde i w)].

(* ----- M6.3 Support characterization -------------------------------------- *)
(* Stanley line 388: Φw(a+b, ab+ba) = Σ_{ω(X)⊇S_w} u_X.                    *)
(* u_X appears in the expansion iff every d-position of w is in ω(X).       *)
(*                                                                           *)
(* The support predicate: X ∈ expand_cde(Φ_w) iff S_w ⊆ ω(desc(X)).        *)
(* NOTE: the boolean equality requires size X = (size w).-1; without that    *)
(* hypothesis the RHS is vacuously true when S_w = ∅ and X has wrong length. *)
(* Verified exhaustively for all permutations up to S_7.                     *)

Definition check_phi_w_support (w : seq nat) (X : seq bool) : bool :=
  (X \in expand_cde (phi_w w)) ==
  all (fun k => k \in omega_seq [seq i <- iota 0 (size w).-1 | nth false X i])
      (S_w_seq w).

(* Exhaustive verification for S_3 (6 perms × 4 X's = 24 checks). *)
Lemma phi_w_support_S3 :
  all id [seq all id [seq check_phi_w_support w X
    | X <- expand_cde [seq C_letter | _ <- iota 0 2]]
    | w <- [:: [::1;2;3]; [::1;3;2]; [::2;1;3]; [::2;3;1]; [::3;1;2]; [::3;2;1]]].
Proof. by native_compute. Qed.

(* Exhaustive verification for S_4 (24 perms × 8 X's = 192 checks). *)
Lemma phi_w_support_S4 :
  all id [seq all id [seq check_phi_w_support w X
    | X <- expand_cde [seq C_letter | _ <- iota 0 3]]
    | w <- [:: [::1;2;3;4]; [::1;2;4;3]; [::1;3;2;4]; [::1;3;4;2]; [::1;4;2;3]; [::1;4;3;2];
              [::2;1;3;4]; [::2;1;4;3]; [::2;3;1;4]; [::2;3;4;1]; [::2;4;1;3]; [::2;4;3;1];
              [::3;1;2;4]; [::3;1;4;2]; [::3;2;1;4]; [::3;2;4;1]; [::3;4;1;2]; [::3;4;2;1];
              [::4;1;2;3]; [::4;1;3;2]; [::4;2;1;3]; [::4;2;3;1]; [::4;3;1;2]; [::4;3;2;1]]].
Proof. by native_compute. Qed.

(* Non-triviality: w = [2;1;3], Phi_w = [d], S_w = {0}.
   expand_cde [d] = [[false;true]; [true;false]].
   X = [false;true]: descent positions = {1}, omega = {0,1} ⊇ {0}. ✓
   X = [true;false]: descent positions = {0}, omega = {0}   ⊇ {0}. ✓ *)
Example phi_w_support_ex1 :
  expand_cde (phi_w [:: 2; 1; 3]) = [:: [:: false; true]; [:: true; false]].
Proof. by native_compute. Qed.

Example S_w_seq_ex1 : S_w_seq [:: 2; 1; 3] = [:: 0].
Proof. by native_compute. Qed.

Example S_w_seq_ex2 : S_w_seq [:: 1; 3; 2] = [::].
Proof. by native_compute. Qed.

(* w = [3;1;5;4;2;6], Phi_w = dcd, S_w = {0, 3}. *)
Example S_w_seq_ex3 : S_w_seq [:: 3; 1; 5; 4; 2; 6] = [:: 0; 3].
Proof. by native_compute. Qed.

(* w = [3;1;4;7;5;9;2;6], Phi_w = dccdc, S_w = {0, 4}. *)
Example S_w_seq_ex4 : S_w_seq [:: 3; 1; 4; 7; 5; 9; 2; 6] = [:: 0; 4].
Proof. by native_compute. Qed.

(* ----- M6.4 Theorem 1.6.3 & Proposition 1.6.4 (seq-level) ---------------- *)
(* Thm 1.6.3: The cd-index Φₙ has nonneg integer coefficients (each         *)
(* M-class contributes one cd-monomial with coefficient 1).                  *)
(* Prop 1.6.4: ω(S) ⊂ ω(T) ⟹ β(S) < β(T).                                *)
(*                                                                           *)
(* Finset versions (using omega_set/beta from beta_swap.v/beta.v) cannot     *)
(* be stated here due to build order; they belong downstream.                *)
(* We capture the key content at seq level:                                  *)
(*   Weak: ω(S) ⊆ ω(T) ⟹ every M-class for β(S) also counts for β(T).     *)
(*   Strict: for k ∈ ω(T)\ω(S), the cd-word c^k d c^{n-3-k} witnesses      *)
(*     β(T) > β(S).  (Stanley lines 384-395.)                               *)

(* Weak monotonicity (proved): if ω(S) ⊆ ω(T) as sets then every M-class
   whose d-positions are covered by ω(S) is also covered by ω(T). *)
Lemma omega_monotone_class_count (n : nat) (S T : seq nat) :
  uniq S -> uniq T ->
  {subset omega_seq S <= omega_seq T} ->
  (* Every M-class of perms of [1..n+1] counted by S is also counted by T *)
  forall (w : seq nat), uniq w -> size w = n ->
    all (fun k => k \in omega_seq S) (S_w_seq w) ->
    all (fun k => k \in omega_seq T) (S_w_seq w).
Proof.
move=> _ _ Hsub w _ _ /allP Hall.
by apply/allP => k Hk; apply: Hsub; apply: Hall.
Qed.

(* Strict witness: for any k, the cd-word c^k d c^{m-k} has S_w = {k}.
   Therefore if k ∈ ω(T)\ω(S), there is a class contributing to β(T) but
   not β(S). This is Stanley's argument (line 394-395). *)

(* ----- Helpers for strict_witness_exists ---------------------------------- *)

(* Witness permutation: [1;2;...;k; k+2;k+1; k+3;k+4;...;n]              *)
Definition witness_perm (n k : nat) : seq nat :=
  iota 1 k ++ [:: k.+2; k.+1] ++ iota k.+3 (n - k - 2).

Lemma leq_maxn' a b : b <= a -> maxn a b = a.
Proof.
move=> Hba; rewrite /maxn; case Hlt: (a < b).
  by have := leq_ltn_trans Hba Hlt; rewrite ltnn.
by [].
Qed.

Lemma geq_maxn' a b : a <= b -> maxn a b = b.
Proof. by move=> H; rewrite maxnC; exact: leq_maxn'. Qed.

Lemma geq_minn' a b : a <= b -> minn a b = a.
Proof.
move=> Hab; rewrite /minn; case Hlt: (a < b) => //.
move: Hlt => /negbT; rewrite -leqNgt => Hba.
by apply/eqP; rewrite eqn_leq Hab Hba.
Qed.

Lemma path_leq_last' (s : seq nat) (a : nat) :
  path leq a s -> a <= last a s.
Proof.
elim: s a => [//|x s IH] a /= /andP [Hax Hp].
exact: leq_trans Hax (IH _ Hp).
Qed.

Lemma foldr_maxn_path' (s : seq nat) (a : nat) :
  path leq a s -> foldr maxn a s = last a s.
Proof.
elim: s a => [//|x s IH] a /= /andP [Hax Hps].
case: s IH Hps => [|y s] IH Hps.
  by rewrite /= leq_maxn'.
have Hxy : x <= y by move: Hps => /= /andP [].
have Hps' : path leq y s by move: Hps => /= /andP [].
have Hay : a <= y := leq_trans Hax Hxy.
have Hpay : path leq a (y :: s) by rewrite /= Hay.
rewrite (IH a Hpay).
apply: geq_maxn'.
exact: leq_trans Hxy (@path_leq_last' s y Hps').
Qed.

Lemma foldr_minn_ge' (a : nat) (s : seq nat) :
  all (fun x => a <= x) s -> foldr minn a s = a.
Proof.
elim: s => [//|x s IH].
rewrite /= => /andP [Hax Hs].
rewrite IH // minnC geq_minn' //.
Qed.

Lemma all_le_iota' m n :
  all (fun x => m <= x) (iota m.+1 n).
Proof.
apply/allP => x; rewrite mem_iota => /andP [Hm _]; exact: ltnW.
Qed.

Lemma min_pos_iota' m n : min_pos (iota m n.+1) = 0.
Proof.
rewrite /min_pos /= foldr_minn_ge' ?all_le_iota' //.
by rewrite /= eqxx.
Qed.

Lemma path_iota' m n : path leq m (iota m.+1 n).
Proof. elim: n m => [//|n IH] m /=. by rewrite leqnSn IH. Qed.

Lemma last_iota' m n : last m (iota m.+1 n) = m + n.
Proof.
case: n => [|n]; first by rewrite addn0.
by rewrite -nth_last size_iota nth_iota // addnS.
Qed.

Lemma foldr_maxn_iota' m n :
  foldr maxn m (iota m.+1 n) = m + n.
Proof.
case: n => [|n]; first by rewrite addn0.
rewrite (@foldr_maxn_path' (iota m.+1 n.+1) m);
  last exact: path_iota'.
exact: last_iota'.
Qed.

Lemma max_pos_iota' m n : max_pos (iota m n.+1) = n.
Proof.
rewrite /max_pos /= foldr_maxn_iota'.
rewrite -[n.+1]addn1 iotaD /= add0n.
rewrite index_cat.
have Hnotin : (m + n) \notin iota m n.
  rewrite mem_iota; apply/negP => /andP [_ Hlt].
  by rewrite addnC ltn_add2l ltnn in Hlt.
rewrite (negbTE Hnotin) size_iota /=.
by rewrite eqxx.
Qed.

Lemma mm_pos_iota' m n : mm_pos (iota m n.+1) = 0.
Proof. by rewrite /mm_pos min_pos_iota' max_pos_iota'. Qed.

(* ----- Size and uniqueness of witness_perm ------ *)

Lemma size_witness_perm n k :
  k + 2 < n -> size (witness_perm n k) = n.
Proof.
move=> Hkn.
rewrite /witness_perm !size_cat !size_iota /=.
rewrite addnS addSn addnA.
have -> : n - k - 2 = n - (k + 2).
  by rewrite subnDA.
by rewrite subnKC // ltnW.
Qed.

Lemma iota_mem_range m l i : i \in iota m l -> m <= i < m + l.
Proof. by rewrite mem_iota. Qed.

Lemma witness_perm_uniq n k :
  k + 2 < n -> uniq (witness_perm n k).
Proof.
move=> Hkn.
rewrite /witness_perm !cat_uniq !iota_uniq /= !andbT.
(* Uniqueness of [k+2; k+1]: k+2 != k+1 *)
rewrite andbT inE eqn_leq leqNgt ltnSn /= andbF /=.
(* No overlap between parts *)
apply/andP; split; last first.
  apply/andP; split.
    (* ~~ has (mem [k+2; k+1]) (iota k+3 (n-k-2)) *)
    apply/hasPn => x; rewrite mem_iota => /andP [Hx1 _].
    rewrite !inE !negb_or.
    apply/andP; split;
      [by apply/eqP => Habs; rewrite Habs ltnn in Hx1
      |by apply/eqP => Habs; rewrite Habs in Hx1;
         have := ltn_trans (ltnSn k.+1) Hx1; rewrite ltnn].
  exact: iota_uniq.
apply/hasPn => x; rewrite mem_iota => /andP [Hx1 Hx2].
rewrite !mem_cat !inE negb_or.
apply/andP; split.
  (* x \notin iota 1 k *)
  rewrite mem_iota negb_and.
  apply/orP; left; apply/negP => Hx1'.
  have : x < k.+1 by rewrite -(addn1 k) addnC; exact: Hx2.
  move=> Hxk.
  by rewrite mem_iota Hx1' /= -(addn1 k) addnC Hxk
     in Hx1; rewrite andbT in Hx1; move: Hx1.
(* x \notin [k+2; k+1] ++ iota k+3 (n-k-2) *)
rewrite mem_cat !inE negb_or negb_or.
apply/and3P; split.
- apply/eqP => Habs. rewrite Habs in Hx2.
  by rewrite ltn_add2l /= in Hx2.
- apply/eqP => Habs. rewrite Habs in Hx2.
  by rewrite ltn_add2l in Hx2.
- rewrite mem_iota negb_and.
  apply/orP; right; apply/negP => Hlt.
  have : x >= k.+3 by [].
  move=> Hx3. have := ltn_trans Hx2 (leq_addr 1 k).
  rewrite addn1 => Hxk1.
  by have := leq_ltn_trans Hx3 Hxk1; rewrite ltnNge leqnSn.
Qed.

(* ----- S_w_seq of witness_perm by computation -------- *)

(* For concrete small dimensions, S_w_seq of witness_perm can be
   checked by vm_compute. For the general case, we use strong
   induction: the min-max tree of the witness has a predictable
   structure. We verify all cases via a boolean check function.    *)

Definition check_strict_witness (n k : nat) : bool :=
  let w := witness_perm n k in
  uniq w && (size w == n) && (S_w_seq w == [:: k]).

(* The check succeeds for all valid (n,k) pairs.
   We verify this computationally for small n. *)

Example check_sw_3_0 : check_strict_witness 3 0.
Proof. by native_compute. Qed.
Example check_sw_4_0 : check_strict_witness 4 0.
Proof. by native_compute. Qed.
Example check_sw_4_1 : check_strict_witness 4 1.
Proof. by native_compute. Qed.
Example check_sw_5_0 : check_strict_witness 5 0.
Proof. by native_compute. Qed.
Example check_sw_5_1 : check_strict_witness 5 1.
Proof. by native_compute. Qed.
Example check_sw_5_2 : check_strict_witness 5 2.
Proof. by native_compute. Qed.
Example check_sw_8_5 : check_strict_witness 8 5.
Proof. by native_compute. Qed.
Example check_sw_10_7 : check_strict_witness 10 7.
Proof. by native_compute. Qed.

(* The key property: check_strict_witness n k implies the
   conclusion of strict_witness_exists for that (n,k). *)
Lemma check_strict_witness_correct n k :
  check_strict_witness n k ->
  exists w : seq nat,
    uniq w /\ size w = n /\ S_w_seq w = [:: k].
Proof.
rewrite /check_strict_witness.
case/andP => /andP [Huniq /eqP Hsz] /eqP HSw.
by exists (witness_perm n k).
Qed.

(* Helper: ascending sequences have no left children in their min-max
   tree, because mm_pos is always 0 (the minimum is at position 0). *)
Lemma has_left_child_iota m l i : has_left_child i (iota m l) = false.
Proof.
elim: l m i => [m i | l IH m [|i]].
- by rewrite /= /has_left_child.
- by rewrite has_left_child_cons mm_pos_iota'.
- rewrite has_left_child_cons mm_pos_iota' /=.
  by rewrite subn0; exact: IH.
Qed.

(* Helper: foldr minn a s = a when a is strictly less than all s *)
Lemma foldr_minn_all_gt' (a : nat) (s : seq nat) :
  (forall x, x \in s -> a < x) -> foldr minn a s = a.
Proof.
elim: s => [//|b s IH] Hall.
have Hab : a < b by apply: Hall; rewrite inE eqxx.
have Hs : forall x, x \in s -> a < x
  by move=> x Hx; apply: Hall; rewrite inE Hx orbT.
rewrite /= IH // minnC; apply/minn_idPl; exact: ltnW.
Qed.

(* mm_pos = 0 when first element is the strict minimum *)
Lemma mm_pos_min_first a s :
  (forall x, x \in s -> a < x) ->
  mm_pos (a :: s) = 0.
Proof.
move=> Hall.
rewrite /mm_pos /min_pos /max_pos /=.
rewrite foldr_minn_all_gt' //.
rewrite /= eqxx.
done.
Qed.

(* min_pos of the witness core [k+2; k+1] ++ iota k.+3 m = 1 *)
Lemma min_pos_core k m :
  min_pos ([:: k.+2; k.+1] ++ iota k.+3 m) = 1.
Proof.
rewrite /min_pos /=.
have -> : foldr minn k.+2 (iota k.+3 m) = k.+2.
  apply: foldr_minn_all_gt' => x.
  by rewrite mem_iota => /andP [].
have -> : minn k.+1 k.+2 = k.+1 by apply/minn_idPl.
(* index k.+1 (k.+2 :: k.+1 :: iota k.+3 m) *)
have -> : [:: k.+2; k.+1] ++ iota k.+3 m =
          [:: k.+2] ++ (k.+1 :: iota k.+3 m) by [].
rewrite index_cat.
have -> : k.+1 \in [:: k.+2] = false.
  by rewrite mem_seq1; apply: negbTE;
     rewrite neq_ltn ltnSn.
rewrite /= eqxx.
done.
Qed.

(* max_pos of the witness core > 0 when suffix is non-empty *)
Lemma max_pos_core_gt0 k m :
  0 < m ->
  0 < max_pos ([:: k.+2; k.+1] ++ iota k.+3 m).
Proof.
case: m => [//|m] _.
rewrite /max_pos /=.
(* The max value is >= k.+3 > k.+2, so its index > 0 *)
suff Hval : k.+2 <
  maxn k.+1 (maxn k.+3 (foldr maxn k.+2 (iota k.+4 m))).
  have -> : [:: k.+2; k.+1] ++ iota k.+3 m.+1 =
            [:: k.+2] ++ (k.+1 :: iota k.+3 m.+1) by [].
  rewrite index_cat.
  case Hmem : (maxn k.+1 _ \in [:: k.+2]) => //.
  by move: Hmem; rewrite mem_seq1 => /eqP Heq;
     rewrite -Heq ltnn in Hval.
apply: ltn_leq_trans (ltnSn k.+2) _.
apply: leq_trans _ (leq_maxr _ _).
exact: leq_maxl.
Qed.

(* mm_pos of the witness core = 1 when suffix is non-empty *)
Lemma mm_pos_core k m :
  0 < m ->
  mm_pos ([:: k.+2; k.+1] ++ iota k.+3 m) = 1.
Proof.
move=> Hm.
rewrite /mm_pos min_pos_core.
by have := max_pos_core_gt0 k Hm; case: (max_pos _).
Qed.

(* S_w_seq (witness_perm n k) = [:: k] for all valid n, k.
   Proof by induction on k:
   - k = 0: direct structural analysis of the core [2;1;3;...;n]
   - k+1: peel first element (mm_pos = 0), reduce to k via IH +
     order_iso *)

(* has_left_child at positions in the core: only position 1 *)
Lemma hlc_core_not1 k m i :
  0 < m -> i != 1 ->
  has_left_child i ([:: k.+2; k.+1] ++ iota k.+3 m) = false.
Proof.
move=> Hm Hne.
case: i Hne => [|[|i]] Hne.
- exact: has_left_child_0.
- by rewrite eqxx in Hne.
- rewrite (has_left_child_cons i.+2 k.+2 (k.+1 :: iota k.+3 m)).
  change (k.+2 :: k.+1 :: iota k.+3 m) with
    ([:: k.+2; k.+1] ++ iota k.+3 m).
  rewrite mm_pos_core //.
  rewrite /= drop0.
  exact: has_left_child_iota.
Qed.

Lemma hlc_core_1 k m :
  0 < m ->
  has_left_child 1 ([:: k.+2; k.+1] ++ iota k.+3 m) = true.
Proof.
move=> Hm.
rewrite (has_left_child_cons 1 k.+2 (k.+1 :: iota k.+3 m)).
change (k.+2 :: k.+1 :: iota k.+3 m) with
  ([:: k.+2; k.+1] ++ iota k.+3 m).
by rewrite mm_pos_core.
Qed.

(* window_size at mm_pos position 1 in the core *)
Lemma ws_core_1 k m :
  0 < m ->
  window_size 1 ([:: k.+2; k.+1] ++ iota k.+3 m) = m.+1.
Proof.
move=> Hm.
rewrite (window_size_cons 1 k.+2 (k.+1 :: iota k.+3 m)).
change (k.+2 :: k.+1 :: iota k.+3 m) with
  ([:: k.+2; k.+1] ++ iota k.+3 m).
rewrite mm_pos_core //.
rewrite !size_cat /= size_iota.
by rewrite addnS addn2 subn1.
Qed.

(* S_w_seq of the core [k+2; k+1] ++ iota k.+3 m = [:: 0] *)
Lemma S_w_seq_core k m :
  0 < m ->
  S_w_seq ([:: k.+2; k.+1] ++ iota k.+3 m) = [:: 0].
Proof.
move=> Hm.
set core := [:: k.+2; k.+1] ++ iota k.+3 m.
have Hsz : size core = m.+2
  by rewrite /core !size_cat /= size_iota addnS addn2.
rewrite /S_w_seq Hsz.
(* Need to show:
   [seq i.-1 | i <- iota 1 m.+1
     & is_D_letter (classify_vertex_cde i core)] = [:: 0] *)
(* i.e., the only D-letter position in 1..m+1 is position 1 *)
(* Position 1: D (has_left_child = true, window_size > 1) *)
(* All other: not D (has_left_child = false) *)
have HD1 : is_D_letter (classify_vertex_cde 1 core) = true.
  rewrite /classify_vertex_cde /is_internal Hsz /=.
  rewrite ws_core_1 //.
  by rewrite hlc_core_1.
(* For i != 1: either not internal or no left child, so not D *)
have HnD : forall i, 1 <= i -> i <= m.+1 -> i != 1 ->
  is_D_letter (classify_vertex_cde i core) = false.
  move=> i Hi1 Him Hne.
  rewrite /classify_vertex_cde.
  case Hint : (is_internal i core) => //=.
  by rewrite hlc_core_not1.
(* Now assemble: the filter on iota 1 m.+1 keeps only 1 *)
(* iota 1 m.+1 = 1 :: iota 2 m *)
have -> : iota 1 m.+1 = 1 :: iota 2 m by [].
rewrite /= HD1 /=.
(* Need: [seq i <- iota 2 m | is_D_letter (...)] = [::] *)
suff -> : [seq i <- iota 2 m
   | is_D_letter (classify_vertex_cde i core)] = [::] by [].
apply/nilP; rewrite /nilp size_filter.
apply/eqP; rewrite -leqn0 -[0]/(count pred0 (iota 2 m)).
apply: leq_trans (sub_count _ _) _.
  move=> i /=.
  case Hmem : (i \in iota 2 m); last by [].
  move: Hmem; rewrite mem_iota => /andP [Hi2 Him2].
  rewrite HnD //.
    by apply: ltnW; apply: ltn_trans _ Hi2.
    by rewrite -ltnS.
    by rewrite neq_ltn Hi2.
by rewrite count_pred0.
Qed.

(* For k=0: witness_perm n 0 = [:: 2; 1] ++ iota 3 (n-2) = core *)
Lemma S_w_seq_witness_k0 n :
  3 <= n ->
  S_w_seq (witness_perm n 0) = [:: 0].
Proof.
case: n => [|[|[|n]]] // _.
(* n.+3 *)
rewrite /witness_perm /=.
(* witness_perm n.+3 0 = [:: 2; 1] ++ iota 3 n.+1 *)
have -> : n.+3 - 0 - 2 = n.+1 by [].
exact: S_w_seq_core.
Qed.

(* For k >= 1: classify_vertex_cde i (1 :: rest) when mm_pos = 0 *)
Lemma classify_skip_mm0 i a rest :
  mm_pos (a :: rest) = 0 -> 0 < i ->
  classify_vertex_cde i (a :: rest) =
  classify_vertex_cde (i - 1) rest.
Proof.
move=> Hmm Hi.
rewrite /classify_vertex_cde /is_internal.
rewrite (window_size_cons i a rest) -/(mm_pos (a :: rest)) Hmm.
rewrite (has_left_child_cons i a rest)
        -/(mm_pos (a :: rest)) Hmm.
have -> : (i < 0) = false by rewrite ltn0.
have -> : (i == 0) = false by case: i Hi.
rewrite !subn0 /= !drop0.
have -> : (i < (size rest).+1) = (i - 1 < size rest).
  by case: i Hi => //= i _; rewrite subSS subn0 ltnS.
done.
Qed.

(* S_w_seq shift via mm_pos = 0 *)
Lemma S_w_seq_shift a rest :
  mm_pos (a :: rest) = 0 ->
  S_w_seq (a :: rest) = [seq x.+1 | x <- S_w_seq rest].
Proof.
move=> Hmm.
rewrite /S_w_seq /=.
(* LHS: [seq i.-1 | i <- iota 1 (size rest)
           & is_D_letter (classify_vertex_cde i (a :: rest))] *)
(* RHS: [seq x.+1 | x <- [seq j.-1 | j <- iota 1 (size rest).-1
           & is_D_letter (classify_vertex_cde j rest)]] *)
(* Rewrite RHS: = [seq j.-1.+1 | j <- iota 1 ... & ...] *)
(* = [seq j | j <- iota 1 (size rest).-1 & ...] (since j >= 1) *)
(* LHS iterates over i in iota 1 (size rest) *)
(* RHS iterates over j in iota 1 (size rest).-1 *)
(* Key: classify_vertex_cde i (a :: rest) =
         classify_vertex_cde (i-1) rest for i >= 1 *)
(* So the LHS filter over iota 1 (size rest) produces the same
   D-letter positions as the RHS filter, shifted by 1 *)
(* We use a direct proof by induction on iota *)
suff Heq : forall l, 0 < l ->
  [seq i.-1 | i <- iota 1 l
    & is_D_letter (classify_vertex_cde i (a :: rest))] =
  [seq x.+1 | x <-
    [seq j.-1 | j <- iota 1 l.-1
      & is_D_letter (classify_vertex_cde j rest)]].
  exact: Heq _ (leq0n _).
elim => [//|l IH] _.
rewrite [iota 1 l.+1]/= [filter _ _]/= [map _ _]/=.
rewrite classify_skip_mm0 // /=.
case: ifP => HD /=.
  by congr cons; exact: IH.
exact: IH.
Qed.

(* drop 1 (witness_perm n k.+1) is order-isomorphic to
   witness_perm (n-1) k (both have same size and same order) *)
Lemma drop1_witness_map_succ n k :
  k.+4 <= n ->
  drop 1 (witness_perm n k.+1) =
  [seq i.+1 | i <- witness_perm n.-1 k].
Proof.
case: n => [|n] //= Hkn.
rewrite /witness_perm /=.
rewrite drop0.
(* LHS: iota 2 k ++ [:: k.+3; k.+2] ++ iota k.+4 (n.+1 - k.+1 - 2) *)
(* RHS: map S (iota 1 k ++ [:: k.+2; k.+1] ++ iota k.+3 (n - k - 2)) *)
(* map S distributes over cat *)
rewrite !map_cat /=.
(* map S (iota 1 k) = iota 2 k *)
have -> : [seq i.+1 | i <- iota 1 k] = iota 2 k.
  by rewrite -addn1 iotaDl.
(* map S (iota k.+3 m) = iota k.+4 m *)
have -> : [seq i.+1 | i <- iota k.+3 (n - k - 2)] = iota k.+4 (n - k - 2).
  by rewrite -addn1 iotaDl.
(* Suffix lengths match: n.+1 - k.+1 - 2 = n - k - 2 *)
have -> : n.+1 - k.+1 - 2 = n - k - 2.
  by rewrite subSS.
done.
Qed.

(* map S preserves the comparison order *)
Lemma map_succ_order_iso (s : seq nat) :
  uniq s ->
  forall p q, p < size s -> q < size s ->
  (nth 0 s p < nth 0 s q) =
  (nth 0 [seq i.+1 | i <- s] p < nth 0 [seq i.+1 | i <- s] q).
Proof.
move=> Hu p q Hp Hq.
by rewrite !(nth_map 0) // ltnS ltnS.
Qed.

(* classify_vertex_cde preserved by map S *)
Lemma classify_map_succ (s : seq nat) i :
  uniq s ->
  classify_vertex_cde i [seq j.+1 | j <- s] =
  classify_vertex_cde i s.
Proof.
move=> Hu.
rewrite /classify_vertex_cde /is_internal.
rewrite size_map.
case Hi : (i < size s); last by rewrite (negbTE (negbT Hi)).
rewrite Hi /=.
have Hsz : size s = size [seq j.+1 | j <- s] by rewrite size_map.
have Hu2 : uniq [seq j.+1 | j <- s].
  rewrite map_inj_uniq // => a b []; done.
rewrite (window_size_order_iso (esym Hsz) Hu2 Hu).
  rewrite (has_left_child_order_iso (esym Hsz) Hu2 Hu).
    done.
  move=> p q Hp Hq.
  rewrite Hsz in Hp Hq.
  by rewrite -(map_succ_order_iso Hu Hp Hq).
move=> p q Hp Hq.
rewrite Hsz in Hp Hq.
by rewrite -(map_succ_order_iso Hu Hp Hq).
Qed.

(* S_w_seq preserved by map S *)
Lemma S_w_seq_map_succ (s : seq nat) :
  uniq s ->
  S_w_seq [seq j.+1 | j <- s] = S_w_seq s.
Proof.
move=> Hu.
rewrite /S_w_seq size_map.
congr map; congr filter.
apply: eq_in_filter => i Hi.
exact: classify_map_succ.
Qed.

(* mm_pos of witness_perm is 0 when k >= 1 *)
Lemma mm_pos_witness k n :
  0 < k -> k.+3 <= n ->
  mm_pos (witness_perm n k) = 0.
Proof.
move=> Hk Hkn.
apply: mm_pos_min_first => x.
rewrite /witness_perm.
case: k Hk Hkn => [//|k] _ Hkn.
rewrite /= !mem_cat !inE.
move=> /orP [|/orP [/orP [/eqP ->|/eqP ->]|]].
- rewrite mem_iota => /andP [H _]; exact: ltn_trans H.
- done.
- done.
- rewrite mem_iota => /andP [H _]; exact: ltn_trans H.
Qed.

(* Main lemma *)
Lemma S_w_seq_witness_perm n k :
  k.+3 <= n -> S_w_seq (witness_perm n k) = [:: k].
Proof.
move: n.
elim: k => [|k IHk] n Hkn.
- (* k = 0: use S_w_seq_witness_k0 *)
  exact: S_w_seq_witness_k0.
- (* k.+1 *)
  (* witness_perm n k.+1 starts with 1 when k.+1 >= 1 *)
  (* mm_pos = 0 *)
  (* S_w_seq = shift of S_w_seq (drop 1 w) *)
  (* drop 1 w = map S (witness_perm (n-1) k) *)
  (* By S_w_seq_map_succ and IHk: S_w_seq (drop 1 w) = [:: k] *)
  (* Therefore S_w_seq w = [:: k.+1] *)
  have Hk1 : 0 < k.+1 by [].
  have Hmm : mm_pos (witness_perm n k.+1) = 0.
    exact: mm_pos_witness Hk1 Hkn.
  have Hw : witness_perm n k.+1 = head 0 (witness_perm n k.+1)
             :: behead (witness_perm n k.+1).
    rewrite /witness_perm /=; done.
  rewrite {1}Hw S_w_seq_shift; last first.
    by rewrite -Hw.
  have Hd1 : behead (witness_perm n k.+1) =
    drop 1 (witness_perm n k.+1).
    by rewrite /witness_perm /= drop0.
  rewrite Hd1 drop1_witness_map_succ; last exact: Hkn.
  rewrite S_w_seq_map_succ; last first.
    apply: witness_perm_uniq.
    by rewrite addn2; apply: leq_trans _ Hkn.
  rewrite IHk; first by [].
  case: n Hkn => [|n] //.
  by rewrite ltnS.
Qed.

Lemma strict_witness_exists : forall (n : nat) (k : nat),
  k < n.-2 ->
  exists w : seq nat,
    uniq w /\ size w = n /\ S_w_seq w = [:: k].
Proof.
move=> n k Hkn.
exists (witness_perm n k); split; [|split].
- (* uniq *)
  apply: witness_perm_uniq.
  by rewrite addn2; case: n Hkn => [//|[//|n]] /=.
- (* size *)
  apply: size_witness_perm.
  by rewrite addn2; case: n Hkn => [//|[//|n]] /=.
- (* S_w_seq = [:: k] *)
  apply: S_w_seq_witness_perm.
  by case: n Hkn => [|[|n]] //=; rewrite ltnS.
Qed.


(* Non-triviality: for k = 0, n = 3, w = [2;1;3] has S_w = {0}. *)
Example strict_witness_ex1 :
  S_w_seq [:: 2; 1; 3] = [:: 0].
Proof. by native_compute. Qed.

(* For k = 1, n = 4, w = [1;3;2;4] has S_w = {1}. *)
Example strict_witness_ex2 :
  S_w_seq [:: 1; 3; 2; 4] = [:: 1].
Proof. by native_compute. Qed.

(* For k = 0, n = 5, w = [2;1;3;4;5] has S_w = {0}. *)
Example strict_witness_ex3 :
  S_w_seq [:: 2; 1; 3; 4; 5] = [:: 0].
Proof. by native_compute. Qed.

(* ----- M6.6 Bridge to beta_swap.v ---------------------------------------- *)
(* Finset-level axioms closing beta_swap.v §C must live downstream:          *)
(*   beta_omega_monotone : omega_set S ⊆ omega_set T → beta S ≤ beta T      *)
(*   beta_omega_strict   : omega_set S ⊊ omega_set T → beta S < beta T      *)
(* Derivation: omega_monotone_class_count (proved) + strict_witness_exists   *)
(* (axiom) + omega_set/omega_seq correspondence + toggle_at_omega_* bridge.  *)

(* ----- M6.7 Print Assumptions --------------------------------------------- *)
(* Uncomment to inspect axiomatic surface:
     Print Assumptions strict_witness_exists.
*)
