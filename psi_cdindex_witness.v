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

(** [omega_seq s] is the seq-level [omega] map: positions [k] such that
    exactly one of [k], [k+1] belongs to [s].  Mirrors [omega_set] from
    [beta_swap.v] on raw [seq nat] (no finset). *)
Definition omega_seq (s : seq nat) : seq nat :=
  [seq k <- iota 0 (foldr maxn 0 s).+1
   | (k \in s) != ((k.+1) \in s)].

(* ----- M6.2 S_w: the d-position set --------------------------------------- *)
(* For the cd-string Φ'_w = f_0 ... f_{n-1}, define S_w = {i-1 : f_i = d}.  *)
(* Using the M5 definition classify_vertex_cde.                              *)

(** [is_D_letter l] tests whether [l] is the D cd-letter. *)
Definition is_D_letter (l : cde) : bool :=
  match l with D_letter => true | _ => false end.

(** [S_w_seq w] is the d-position set of [w]: predecessors of D-vertices
    in the cd-classification.  This is the support set [S_w] from
    Stanley's Prop 1.6.4. *)
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

(** Boolean form of the support claim: [X] expands from [phi_w w] iff every
    d-position of [w] is in [omega] of [X]'s descent set. *)
(* phi_w_support_S3 and phi_w_support_S4 — exhaustive vm_compute sanity   *)
(* checks for S_3 (24 cases) and S_4 (192 cases) — were sanity proofs not  *)
(* used by any downstream lemma.  Removed because the S_4 case takes      *)
(* >30 minutes to type-check at -vo.                                       *)

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

(** Weak monotonicity: if [omega_seq S] is contained in [omega_seq T], then
    every M-class whose d-positions are covered by [omega_seq S] is also
    covered by [omega_seq T].  Half of Stanley's Prop 1.6.4. *)
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

(** [witness_perm n k] is the permutation [1;..;k; k+2; k+1; k+3;..;n]:
    a single inversion at position [k] embedded in a sorted backbone.
    Realises a cd-word with [S_w = {k}], used in [strict_witness_exists]. *)
Definition witness_perm (n k : nat) : seq nat :=
  iota 1 k ++ [:: k.+2; k.+1] ++ iota k.+3 (n - k - 2).

(** Local arithmetic helper: [maxn a b = a] when [b <= a]. *)
Lemma leq_maxn' a b : b <= a -> maxn a b = a.
Proof.
move=> Hba; rewrite /maxn; case Hlt: (a < b).
  by have := leq_ltn_trans Hba Hlt; rewrite ltnn.
by [].
Qed.

(** Local arithmetic helper: [maxn a b = b] when [a <= b]. *)
Lemma geq_maxn' a b : a <= b -> maxn a b = b.
Proof. by move=> H; rewrite maxnC; exact: leq_maxn'. Qed.

(** Local arithmetic helper: [minn a b = a] when [a <= b]. *)
Lemma geq_minn' a b : a <= b -> minn a b = a.
Proof.
move=> Hab; rewrite /minn; case Hlt: (a < b) => //.
move: Hlt => /negbT; rewrite -leqNgt => Hba.
by apply/eqP; rewrite eqn_leq Hab Hba.
Qed.

(** A leq-path from [a] over [s] gives [a <= last a s]. *)
Lemma path_leq_last' (s : seq nat) (a : nat) :
  path leq a s -> a <= last a s.
Proof.
elim: s a => [//|x s IH] a /= /andP [Hax Hp].
exact: leq_trans Hax (IH _ Hp).
Qed.

(** On a sorted (leq-path) sequence, [foldr maxn] reduces to its last
    element. *)
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

(** [foldr minn a s = a] when every element of [s] is at least [a]. *)
Lemma foldr_minn_ge' (a : nat) (s : seq nat) :
  all (fun x => a <= x) s -> foldr minn a s = a.
Proof.
elim: s => [//|x s IH].
rewrite /= => /andP [Hax Hs].
rewrite IH // minnC geq_minn' //.
Qed.

(** Every element of [iota m.+1 n] is at least [m]. *)
Lemma all_le_iota' m n :
  all (fun x => m <= x) (iota m.+1 n).
Proof.
apply/allP => x; rewrite mem_iota => /andP [Hm _]; exact: ltnW.
Qed.

(** [min_pos] of an ascending [iota] is 0 (minimum is the head). *)
Lemma min_pos_iota' m n : min_pos (iota m n.+1) = 0.
Proof.
rewrite /min_pos /= foldr_minn_ge' ?all_le_iota' //.
by rewrite /= eqxx.
Qed.

(** [iota m.+1 n] is a leq-path with starting point [m]. *)
Lemma path_iota' m n : path leq m (iota m.+1 n).
Proof. elim: n m => [//|n IH] m /=. by rewrite leqnSn IH. Qed.

(** Last element of [m :: iota m.+1 n] is [m + n]. *)
Lemma last_iota' m n : last m (iota m.+1 n) = m + n.
Proof.
case: n => [|n]; first by rewrite addn0.
by rewrite -nth_last size_iota nth_iota // addnS.
Qed.

(** [foldr maxn] of an ascending [iota] equals its last element. *)
Lemma foldr_maxn_iota' m n :
  foldr maxn m (iota m.+1 n) = m + n.
Proof.
case: n => [|n]; first by rewrite addn0.
rewrite (@foldr_maxn_path' (iota m.+1 n.+1) m);
  last exact: path_iota'.
exact: last_iota'.
Qed.

(** [max_pos] of an ascending [iota] is the last index. *)
Lemma max_pos_iota' m n :
  max_pos (iota m n.+1) = n.
Proof.
rewrite /max_pos.
rewrite [head 0 _]/= [behead _]/= foldr_maxn_iota'.
have -> : iota m n.+1 = iota m n ++ [:: m + n].
  rewrite -addn1 iotaD /=.
  by [].
rewrite index_cat.
have Hnotin : (m + n) \notin iota m n.
  rewrite mem_iota; apply/negP => /andP [_ Hlt].
  by rewrite addnC ltn_add2l ltnn in Hlt.
rewrite (negbTE Hnotin) size_iota /= eqxx /=.
by rewrite addn0.
Qed.

(** [mm_pos] of an ascending [iota] is 0 (root is the minimum). *)
Lemma mm_pos_iota' m n : mm_pos (iota m n.+1) = 0.
Proof. by rewrite /mm_pos min_pos_iota' max_pos_iota'. Qed.

(* ----- Size and uniqueness of witness_perm ------ *)

(** [witness_perm n k] has length [n] when [k + 2 < n]. *)
Lemma size_witness_perm n k :
  k + 2 < n -> size (witness_perm n k) = n.
Proof.
move=> Hkn.
rewrite /witness_perm !size_cat !size_iota /=.
rewrite addnA -subnDA.
by rewrite subnKC // ltnW.
Qed.

(** Membership in [iota m l] gives [m <= i < m + l]. *)
(** [witness_perm n k] is duplicate-free when [k + 2 < n]. *)
Lemma witness_perm_uniq n k :
  k + 2 < n -> uniq (witness_perm n k).
Proof.
move=> Hkn.
rewrite /witness_perm.
rewrite cat_uniq iota_uniq.
apply/and3P; split=> //.
- (* iota 1 k disjoint from [::k.+2; k.+1] ++ iota k.+3 _ *)
  apply/hasPn => x; rewrite mem_cat => Hx.
  rewrite mem_iota negb_and.
  apply/orP; right.
  rewrite -leqNgt addnC addn1.
  case/orP: Hx => Hx.
  + rewrite !inE in Hx; case/orP: Hx => /eqP ->.
    * exact: leqnSn.
    * exact: leqnn.
  + rewrite mem_iota in Hx; case/andP: Hx => Hx3 _.
    apply: leq_trans _ Hx3.
    by exact: leq_trans (leqnSn _) (leqnSn _).
rewrite cat_uniq iota_uniq /=.
apply/and3P; split=> //.
- (* uniq [::k.+2; k.+1] *)
  rewrite andbT /= inE.
  by rewrite eqSS (gtn_eqF (ltnSn _)).
- (* [::k.+2; k.+1] disjoint from iota k.+3 _ *)
  apply/hasPn => x; rewrite mem_iota => /andP [Hx3 _].
  rewrite !inE; apply/norP; split; apply/eqP => Habs;
    rewrite Habs in Hx3.
  by rewrite ltnn in Hx3.
  by rewrite ltnNge leqnSn in Hx3.
Qed.

(* ----- S_w_seq of witness_perm by computation -------- *)

(* For concrete small dimensions, S_w_seq of witness_perm can be
   checked by vm_compute. For the general case, we use strong
   induction: the min-max tree of the witness has a predictable
   structure. We verify all cases via a boolean check function.    *)

(** Boolean witness: [witness_perm n k] is uniq, of length [n], and has
    [S_w_seq] equal to [[:: k]].  Used for vm_compute sanity checks. *)
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
(* check_sw_8_5 and check_sw_10_7 sanity examples removed —              *)
(* their vm_compute on witness_perm of size 8/10 dominates the -vo        *)
(* compile time (>1 hour combined) and they are unused.                   *)

(* The key property: check_strict_witness n k implies the
   conclusion of strict_witness_exists for that (n,k). *)
(** [check_strict_witness] reflects [strict_witness_exists] for that [n,k]. *)
Lemma check_strict_witness_correct n k :
  check_strict_witness n k ->
  exists w : seq nat,
    uniq w /\ size w = n /\ S_w_seq w = [:: k].
Proof.
rewrite /check_strict_witness.
case/andP => /andP [Huniq /eqP Hsz] /eqP HSw.
by exists (witness_perm n k).
Qed.

(** Helper: ascending sequences ([iota]) have no left children in their
    min-max tree, since [mm_pos = 0] at every recursion depth. *)
Lemma has_left_child_iota m l i :
  has_left_child i (iota m l) = false.
Proof.
elim: l m i => [m i | l IH m [|i]].
- by rewrite /= /has_left_child.
- by rewrite has_left_child_cons mm_pos_iota'.
- rewrite has_left_child_cons mm_pos_iota' /=.
  rewrite subn1 drop0 /=.
  exact: IH.
Qed.

(** Helper: [foldr minn a s = a] when [a] is strictly less than every
    element of [s]. *)
Lemma foldr_minn_all_gt' (a : nat) (s : seq nat) :
  (forall x, x \in s -> a < x) -> foldr minn a s = a.
Proof.
elim: s => [//|b s IH] Hall.
have Hab : a < b by apply: Hall; rewrite inE eqxx.
have Hs : forall x, x \in s -> a < x
  by move=> x Hx; apply: Hall; rewrite inE Hx orbT.
rewrite /= IH // minnC; apply/minn_idPl; exact: ltnW.
Qed.

(** [mm_pos (a :: s) = 0] when [a] is the strict minimum of [a :: s]. *)
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

(** [min_pos] of the witness core [[k+2; k+1] ++ iota k.+3 m] is 1
    (the [k+1] at position 1 is the unique minimum). *)
Lemma min_pos_core k m :
  min_pos ([:: k.+2; k.+1] ++ iota k.+3 m) = 1.
Proof.
rewrite /min_pos /=.
have -> : foldr minn k.+2 (iota k.+3 m) = k.+2.
  apply: foldr_minn_all_gt' => x.
  by rewrite mem_iota => /andP [].
have -> : minn k.+1 k.+2 = k.+1 by apply/minn_idPl.
have -> : (k.+2 == k.+1) = false by rewrite eqSS (gtn_eqF (ltnSn _)).
by rewrite eqxx.
Qed.

(** [max_pos] of the witness core is positive when the suffix [iota k.+3 m]
    is non-empty. *)
Lemma max_pos_core_gt0 k m :
  0 < m ->
  0 < max_pos ([:: k.+2; k.+1] ++ iota k.+3 m).
Proof.
case: m => [//|m] _.
rewrite /max_pos /=.
have Hge : k.+3 <=
  maxn k.+1 (maxn k.+3 (foldr maxn k.+2 (iota k.+4 m))).
  by apply: leq_trans (leq_maxl _ _) (leq_maxr _ _).
rewrite eq_sym (gtn_eqF Hge).
by [].
Qed.

(** [mm_pos] of the witness core is 1 (position of [k+1]) when the suffix
    is non-empty. *)
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

(** In the witness core, only position 1 has a left child; all other
    positions are leaves of the min-max tree. *)
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

(** Position 1 in the witness core has a left child (the [k+2] vertex). *)
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

(** [window_size] at the [mm_pos] position 1 in the witness core is [m.+1]
    (covers [k+1] and the entire ascending suffix). *)
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
by [].
Qed.

(** [S_w_seq] of the witness core is [[:: 0]]: the only D-position is at
    index 1, contributing [0] to the d-position set. *)
Lemma S_w_seq_core k m :
  0 < m ->
  S_w_seq ([:: k.+2; k.+1] ++ iota k.+3 m) =
  [:: 0].
Proof.
move=> Hm.
set core := [:: k.+2; k.+1] ++ iota k.+3 m.
have Hsz : size core = m.+2
  by rewrite /core !size_cat /= size_iota.
rewrite /S_w_seq Hsz.
have HD1 : is_D_letter (classify_vertex_cde 1 core) = true.
  rewrite /classify_vertex_cde /is_internal Hsz /=.
  rewrite ws_core_1 // hlc_core_1 //.
  by rewrite ltnS Hm.
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
rewrite (eq_in_count (a2 := pred0)); first by rewrite count_pred0.
move=> i Hi /=.
move: Hi; rewrite mem_iota => /andP [Hi2 Him2].
have Hi_pos : 0 < i by exact: ltnW Hi2.
have Hi_le : i <= m.+1 by rewrite -ltnS.
have Hi_ne1 : i != 1 by rewrite neq_ltn Hi2 orbT.
by rewrite HnD.
Qed.

(** Base case [k = 0]: [witness_perm n 0] is exactly the witness core, so
    [S_w_seq = [:: 0]]. *)
Lemma S_w_seq_witness_k0 n :
  3 <= n ->
  S_w_seq (witness_perm n 0) = [:: 0].
Proof.
case: n => [|[|[|n]]] // _.
rewrite /witness_perm /=.
have -> : [:: 2, 1, 3 & iota 4 n] = [:: 2; 1] ++ iota 3 n.+1 by [].
by apply: (S_w_seq_core 0); apply: ltn0Sn.
Qed.

(** When the head [a] is at the root ([mm_pos = 0]), classifying any
    positive position [i] in [a :: rest] reduces to classifying [i-1] in
    the right subtree [rest]. *)
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

(** Index-shift property: when the head is at the root, [S_w_seq] of the
    cons equals the [S_w_seq] of the tail with every entry incremented. *)
Lemma S_w_seq_shift a rest :
  mm_pos (a :: rest) = 0 ->
  S_w_seq (a :: rest) =
  [seq x.+1 | x <- S_w_seq rest].
Proof.
move=> Hmm.
rewrite /S_w_seq /=.
(* Step 1: replace classify_vertex_cde i (a :: rest) by classify (i-1) rest
   for i in iota 1 (size rest), using classify_skip_mm0. *)
rewrite (eq_in_filter
  (a2 := fun i => is_D_letter (classify_vertex_cde (i - 1) rest))); last first.
  move=> i; rewrite mem_iota => /andP [Hi _].
  by rewrite (classify_skip_mm0 Hmm Hi).
(* Step 2: change of variable i = j.+1 in iota *)
have iota_S : forall l m, iota m.+1 l = [seq j.+1 | j <- iota m l].
  by elim=> [|l IH] m //=; rewrite IH.
have -> : iota 1 (size rest) = [seq j.+1 | j <- iota 0 (size rest)]
  by exact: iota_S.
rewrite filter_map -!map_comp.
(* LHS: [seq (j.+1).-1 | j <- iota 0 (size rest) &
          is_D_letter (classify_vertex_cde (j.+1 - 1) rest)] *)
rewrite (eq_filter (a2 := fun j => is_D_letter (classify_vertex_cde j rest))); last first.
  by move=> j /=; rewrite subn1 /=.
rewrite (eq_map (g := id)); last first.
  by move=> j /=.
rewrite map_id.
(* Now LHS: filter (D over rest) (iota 0 (size rest)) *)
case Hsz : (size rest) => [|m] /=.
  by [].
have HE : is_D_letter (classify_vertex_cde 0 rest) = false.
  rewrite /classify_vertex_cde.
  by case: ifP => //= _; rewrite has_left_child_0.
rewrite HE /=.
(* Goal: filter D (iota 1 m) = map (succ \o pred) (filter D (iota 1 m)) *)
rewrite -[LHS]map_id.
apply/eq_in_map => j Hj.
rewrite mem_filter mem_iota in Hj.
case/andP: Hj => _ /andP [Hj _].
by case: j Hj.
Qed.

(** Tail of [witness_perm n k.+1] equals the [+1]-shift of
    [witness_perm n.-1 k]; provides the inductive step for k. *)
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
  rewrite (eq_map (g := addn 1)); last by move=> i; rewrite addnC addn1.
  by rewrite -iotaDl.
have -> : [seq i.+1 | i <- iota k.+3 (n - k - 2)] =
  iota k.+4 (n - k - 2).
  rewrite (eq_map (g := addn 1)); last by move=> i; rewrite addnC addn1.
  by rewrite -[k.+4]/(1 + k.+3) -iotaDl.
have -> : n.+1 - k.+1 - 2 = n - k - 2.
  by rewrite subSS.
done.
Qed.

(** Mapping [S] over a uniq sequence preserves the order of elements
    (used to lift order-iso properties through the witness shift). *)
(** [classify_vertex_cde] is invariant under the [+1]-shift on a uniq
    sequence (since cd-classification depends only on order). *)
Lemma classify_map_succ (s : seq nat) i :
  uniq s ->
  classify_vertex_cde i [seq j.+1 | j <- s] =
  classify_vertex_cde i s.
Proof.
move=> Hu.
rewrite /classify_vertex_cde /is_internal.
rewrite size_map.
case Hi : (i < size s) => /=; last by [].
have Hsz : size s = size [seq j.+1 | j <- s]
  by rewrite size_map.
have Hu2 : uniq [seq j.+1 | j <- s].
  rewrite map_inj_uniq // => a b []; done.
have Horder p q : p < size s -> q < size s ->
    (nth 0 [seq j.+1 | j <- s] p < nth 0 [seq j.+1 | j <- s] q) =
    (nth 0 s p < nth 0 s q).
  move=> Hp Hq.
  by rewrite (nth_map 0 _ _ Hp) (nth_map 0 _ _ Hq) ltnS.
rewrite (window_size_order_iso i (esym Hsz) Hu2 Hu); last first.
  move=> p q Hp Hq; rewrite -Hsz in Hp Hq.
  by rewrite Horder.
rewrite (has_left_child_order_iso i (esym Hsz) Hu2 Hu); last first.
  move=> p q Hp Hq; rewrite -Hsz in Hp Hq.
  by rewrite Horder.
done.
Qed.

(** [S_w_seq] is invariant under the [+1]-shift on a uniq sequence. *)
Lemma S_w_seq_map_succ (s : seq nat) :
  uniq s ->
  S_w_seq [seq j.+1 | j <- s] = S_w_seq s.
Proof.
move=> Hu.
rewrite /S_w_seq size_map.
congr map.
apply: eq_filter => i.
by rewrite (classify_map_succ _ Hu).
Qed.

(** [mm_pos] of [witness_perm n k] is 0 for [k >= 1]: the [1] at the head
    is the strict minimum of the permutation. *)
Lemma mm_pos_witness k n :
  0 < k -> k.+3 <= n ->
  mm_pos (witness_perm n k) = 0.
Proof.
case: k => [//|k] _ Hkn.
rewrite /witness_perm.
have -> : iota 1 k.+1 = 1 :: iota 2 k by [].
rewrite cat_cons.
apply: mm_pos_min_first => x.
rewrite !mem_cat !inE.
case/orP=> [|H].
- by rewrite mem_iota => /andP [H _].
- case/orP: H => [|H2].
  + by case/orP=> /eqP ->.
  + by rewrite mem_iota in H2; case/andP: H2 => H _; apply: ltn_trans H.
Qed.

(** Main lemma: [S_w_seq (witness_perm n k) = [:: k]] for all [k.+3 <= n].
    Proof by induction on [k]: base via [S_w_seq_witness_k0], step via
    [S_w_seq_shift] + [drop1_witness_map_succ] + [S_w_seq_map_succ]. *)
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
  have Hn : 0 < n by apply: leq_trans Hkn.
  have Hn1 : k.+3 <= n.-1.
    by rewrite -ltnS prednK //; apply: Hkn.
  rewrite S_w_seq_map_succ; last first.
    apply: witness_perm_uniq.
    by rewrite addn2.
  by rewrite IHk.
Qed.

(** Strict-witness existence (Stanley Prop 1.6.4, strict half): for every
    [k < n.-2] there is a uniq permutation [w] of length [n] with
    [S_w_seq w = [:: k]].  The witness is [witness_perm n k]. *)
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

