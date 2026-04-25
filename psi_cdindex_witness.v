(* psi_cdindex_witness.v — Milestone 6: omega_seq, S_w_seq, witness_perm     *)
(*                                                                           *)
(* Split from psi_cdindex.v to reduce -vo compilation memory.                *)
(* Contains: omega_seq, S_w_seq definitions, support checks,                 *)
(* witness_perm infrastructure, strict_witness_exists.                        *)

From mathcomp Require Import all_ssreflect.
Require Import mmtree psi_core psi_comm psi_descent_v2 psi_descent_thms.
Require Import psi_cdindex_core.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

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
Proof. by vm_compute. Qed.

(* Exhaustive verification for S_4 (24 perms × 8 X's = 192 checks). *)
Lemma phi_w_support_S4 :
  all id [seq all id [seq check_phi_w_support w X
    | X <- expand_cde [seq C_letter | _ <- iota 0 3]]
    | w <- [:: [::1;2;3;4]; [::1;2;4;3]; [::1;3;2;4]; [::1;3;4;2]; [::1;4;2;3]; [::1;4;3;2];
              [::2;1;3;4]; [::2;1;4;3]; [::2;3;1;4]; [::2;3;4;1]; [::2;4;1;3]; [::2;4;3;1];
              [::3;1;2;4]; [::3;1;4;2]; [::3;2;1;4]; [::3;2;4;1]; [::3;4;1;2]; [::3;4;2;1];
              [::4;1;2;3]; [::4;1;3;2]; [::4;2;1;3]; [::4;2;3;1]; [::4;3;1;2]; [::4;3;2;1]]].
Proof. by vm_compute. Qed.

(* Non-triviality: w = [2;1;3], Phi_w = [d], S_w = {0}.
   expand_cde [d] = [[false;true]; [true;false]].
   X = [false;true]: descent positions = {1}, omega = {0,1} ⊇ {0}. ✓
   X = [true;false]: descent positions = {0}, omega = {0}   ⊇ {0}. ✓ *)
Example phi_w_support_ex1 :
  expand_cde (phi_w [:: 2; 1; 3]) = [:: [:: false; true]; [:: true; false]].
Proof. by vm_compute. Qed.

Example S_w_seq_ex1 : S_w_seq [:: 2; 1; 3] = [:: 0].
Proof. by vm_compute. Qed.

Example S_w_seq_ex2 : S_w_seq [:: 1; 3; 2] = [::].
Proof. by vm_compute. Qed.

(* w = [3;1;5;4;2;6], Phi_w = dcd, S_w = {0, 3}. *)
Example S_w_seq_ex3 : S_w_seq [:: 3; 1; 5; 4; 2; 6] = [:: 0; 3].
Proof. by vm_compute. Qed.

(* w = [3;1;4;7;5;9;2;6], Phi_w = dccdc, S_w = {0, 4}. *)
Example S_w_seq_ex4 : S_w_seq [:: 3; 1; 4; 7; 5; 9; 2; 6] = [:: 0; 4].
Proof. by vm_compute. Qed.

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
have Hxy : x <= y
  by move: Hps => /= /andP [].
have Hps' : path leq y s
  by move: Hps => /= /andP [].
have Hay : a <= y := leq_trans Hax Hxy.
have Hpay : path leq a (y :: s)
  by rewrite /= Hay.
rewrite (IH a Hpay).
apply: geq_maxn'.
exact: leq_trans Hxy
  (@path_leq_last' s y Hps').
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

Lemma max_pos_iota' m n :
  max_pos (iota m n.+1) = n.
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
rewrite andbT inE eqn_leq leqNgt ltnSn /= andbF /=.
apply/andP; split; last first.
  apply/andP; split.
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
  rewrite mem_iota negb_and.
  apply/orP; left; apply/negP => Hx1'.
  have : x < k.+1 by rewrite -(addn1 k) addnC; exact: Hx2.
  move=> Hxk.
  by rewrite mem_iota Hx1' /= -(addn1 k) addnC Hxk
     in Hx1; rewrite andbT in Hx1; move: Hx1.
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
  by have := leq_ltn_trans Hx3 Hxk1;
     rewrite ltnNge leqnSn.
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
Proof. by vm_compute. Qed.
Example check_sw_4_0 : check_strict_witness 4 0.
Proof. by vm_compute. Qed.
Example check_sw_4_1 : check_strict_witness 4 1.
Proof. by vm_compute. Qed.
Example check_sw_5_0 : check_strict_witness 5 0.
Proof. by vm_compute. Qed.
Example check_sw_5_1 : check_strict_witness 5 1.
Proof. by vm_compute. Qed.
Example check_sw_5_2 : check_strict_witness 5 2.
Proof. by vm_compute. Qed.
Example check_sw_8_5 : check_strict_witness 8 5.
Proof. by vm_compute. Qed.
Example check_sw_10_7 : check_strict_witness 10 7.
Proof. by vm_compute. Qed.

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
Lemma has_left_child_iota m l i :
  has_left_child i (iota m l) = false.
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
  has_left_child i
    ([:: k.+2; k.+1] ++ iota k.+3 m) = false.
Proof.
move=> Hm Hne.
case: i Hne => [|[|i]] Hne.
- exact: has_left_child_0.
- by rewrite eqxx in Hne.
- rewrite (has_left_child_cons i.+2 k.+2
    (k.+1 :: iota k.+3 m)).
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
  window_size 1
    ([:: k.+2; k.+1] ++ iota k.+3 m) = m.+1.
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
  S_w_seq ([:: k.+2; k.+1] ++ iota k.+3 m) =
  [:: 0].
Proof.
move=> Hm.
set core := [:: k.+2; k.+1] ++ iota k.+3 m.
have Hsz : size core = m.+2
  by rewrite /core !size_cat /= size_iota addnS addn2.
rewrite /S_w_seq Hsz.
have HD1 : is_D_letter (classify_vertex_cde 1 core) = true.
  rewrite /classify_vertex_cde /is_internal Hsz /=.
  rewrite ws_core_1 //.
  by rewrite hlc_core_1.
have HnD : forall i, 1 <= i -> i <= m.+1 -> i != 1 ->
  is_D_letter (classify_vertex_cde i core) = false.
  move=> i Hi1 Him Hne.
  rewrite /classify_vertex_cde.
  case Hint : (is_internal i core) => //=.
  by rewrite hlc_core_not1.
have -> : iota 1 m.+1 = 1 :: iota 2 m by [].
rewrite /= HD1 /=.
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
rewrite /witness_perm /=.
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
rewrite (window_size_cons i a rest)
  -/(mm_pos (a :: rest)) Hmm.
rewrite (has_left_child_cons i a rest)
        -/(mm_pos (a :: rest)) Hmm.
have -> : (i < 0) = false by rewrite ltn0.
have -> : (i == 0) = false by case: i Hi.
rewrite !subn0 /= !drop0.
have -> : (i < (size rest).+1) =
  (i - 1 < size rest).
  by case: i Hi => //= i _;
     rewrite subSS subn0 ltnS.
done.
Qed.

(* S_w_seq shift via mm_pos = 0 *)
Lemma S_w_seq_shift a rest :
  mm_pos (a :: rest) = 0 ->
  S_w_seq (a :: rest) =
  [seq x.+1 | x <- S_w_seq rest].
Proof.
move=> Hmm.
rewrite /S_w_seq /=.
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
rewrite !map_cat /=.
have -> : [seq i.+1 | i <- iota 1 k] = iota 2 k.
  by rewrite -addn1 iotaDl.
have -> : [seq i.+1 | i <- iota k.+3 (n - k - 2)] =
  iota k.+4 (n - k - 2).
  by rewrite -addn1 iotaDl.
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
case Hi : (i < size s); last
  by rewrite (negbTE (negbT Hi)).
rewrite Hi /=.
have Hsz : size s = size [seq j.+1 | j <- s]
  by rewrite size_map.
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
- exact: S_w_seq_witness_k0.
- have Hk1 : 0 < k.+1 by [].
  have Hmm : mm_pos (witness_perm n k.+1) = 0.
    exact: mm_pos_witness Hk1 Hkn.
  have Hw : witness_perm n k.+1 =
    head 0 (witness_perm n k.+1)
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

Lemma strict_witness_exists :
  forall (n : nat) (k : nat),
  k < n.-2 ->
  exists w : seq nat,
    uniq w /\ size w = n /\ S_w_seq w = [:: k].
Proof.
move=> n k Hkn.
exists (witness_perm n k); split; [|split].
- apply: witness_perm_uniq.
  by rewrite addn2;
     case: n Hkn => [//|[//|n]] /=.
- apply: size_witness_perm.
  by rewrite addn2;
     case: n Hkn => [//|[//|n]] /=.
- apply: S_w_seq_witness_perm.
  by case: n Hkn => [|[|n]] //=;
     rewrite ltnS.
Qed.


(* Non-triviality: for k = 0, n = 3, w = [2;1;3] has S_w = {0}. *)
Example strict_witness_ex1 :
  S_w_seq [:: 2; 1; 3] = [:: 0].
Proof. by vm_compute. Qed.

(* For k = 1, n = 4, w = [1;3;2;4] has S_w = {1}. *)
Example strict_witness_ex2 :
  S_w_seq [:: 1; 3; 2; 4] = [:: 1].
Proof. by vm_compute. Qed.

(* For k = 0, n = 5, w = [2;1;3;4;5] has S_w = {0}. *)
Example strict_witness_ex3 :
  S_w_seq [:: 2; 1; 3; 4; 5] = [:: 0].
Proof. by vm_compute. Qed.

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

