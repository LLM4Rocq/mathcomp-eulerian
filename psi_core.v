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

(* Helper: transfer order-isomorphism to take m *)
Lemma order_iso_take m (s1 s2 : seq nat) :
  m < size s1 -> size s1 = size s2 ->
  (forall p q, p < size s1 -> q < size s1 ->
    (nth 0 s1 p < nth 0 s1 q) = (nth 0 s2 p < nth 0 s2 q)) ->
  forall p q, p < size (take m s1) -> q < size (take m s1) ->
    (nth 0 (take m s1) p < nth 0 (take m s1) q) =
    (nth 0 (take m s2) p < nth 0 (take m s2) q).
Proof.
move=> Hm Hsz Hord p q Hp Hq.
rewrite !nth_take //.
rewrite (size_takel (ltnW Hm)) in Hp.
rewrite (size_takel (ltnW Hm)) in Hq.
apply: Hord; exact: ltn_trans _ Hm.
all: by rewrite (size_takel (ltnW Hm)) in Hp Hq.
Qed.

(* Helper: transfer order-isomorphism to drop m.+1 *)
Lemma order_iso_drop m (s1 s2 : seq nat) :
  m < size s1 -> size s1 = size s2 ->
  (forall p q, p < size s1 -> q < size s1 ->
    (nth 0 s1 p < nth 0 s1 q) = (nth 0 s2 p < nth 0 s2 q)) ->
  forall p q, p < size (drop m.+1 s1) -> q < size (drop m.+1 s1) ->
    (nth 0 (drop m.+1 s1) p < nth 0 (drop m.+1 s1) q) =
    (nth 0 (drop m.+1 s2) p < nth 0 (drop m.+1 s2) q).
Proof.
move=> Hm Hsz Hord p q Hp Hq.
rewrite !nth_drop.
apply: Hord.
all: rewrite -ltn_subRL; by rewrite size_drop in Hp Hq *.
Qed.

Lemma window_size_order_iso (s1 s2 : seq nat) i :
  size s1 = size s2 -> uniq s1 -> uniq s2 ->
  (forall p q, p < size s1 -> q < size s1 ->
    (nth 0 s1 p < nth 0 s1 q) =
    (nth 0 s2 p < nth 0 s2 q)) ->
  window_size i s1 = window_size i s2.
Proof.
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
  + rewrite (size_takel (ltnW Hm1)).
    exact: leq_trans Hm1 Hsz1.
  + have Hm2 : m < size (a2 :: t2) by rewrite -Hszeq'.
    by rewrite (size_takel (ltnW Hm1)) (size_takel (ltnW Hm2)).
  + by move: Hu1; rewrite -{1}(cat_take_drop m (a1 :: t1))
       cat_uniq => /andP [].
  + by move: Hu2; rewrite -{1}(cat_take_drop m (a2 :: t2))
       cat_uniq => /andP [].
  + exact: order_iso_take Hm1 Hszeq' Hord.
- apply: IH.
  + rewrite size_drop.
    have := @leq_sub2r m.+1 _ _ Hsz1.
    rewrite subSS; move=> H; exact: leq_trans H (leq_subr m n).
  + by rewrite !size_drop Hszeq'.
  + by move: Hu1;
       rewrite -{1}(cat_take_drop m.+1 (a1 :: t1))
       cat_uniq => /andP [_ /andP [_ ?]].
  + by move: Hu2;
       rewrite -{1}(cat_take_drop m.+1 (a2 :: t2))
       cat_uniq => /andP [_ /andP [_ ?]].
  + exact: order_iso_drop Hm1 Hszeq' Hord.
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
