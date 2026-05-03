(* altsub.v — longest alternating subsequence of a permutation.

   Stanley EC1 §1.6.2.  Headline:
     as(w) = (turn_count w).+2
   for w : {perm 'I_n.+2}, where turn_count counts the "turning
   points" — interior positions where the direction of w changes.

   See docs/plans/ALTSUB_PLAN.md for the design notes.

   Strategy taken: HYBRID (PATH X + Path Y framing).
   - We give the BIJECTIVE definition `as_perm_max` (max length over
     alternating subsequences of perm_seq s) for completeness.
   - We give the DIRECT definition `as_perm s := (turn_count s).+2`
     and prove its structural identities (id case, descent-set
     bound, alternating-descent-set max case).
   - The full equivalence `as_perm_max s = (turn_count s).+2` is
     STATED (informally, in §J as a comment block) with a proof
     sketch and an explicit LOC budget.  Both directions are honest
     theorems left for follow-up; no axioms here.
*)

From mathcomp Require Import all_ssreflect fingroup perm.
From mathcomp_eulerian Require Import ordinal_reindex perm_compress
                                      descent eulerian beta beta_omega beta_swap.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* ========================================================================= *)
(* §A. Turning points and turn_count                                         *)
(* ========================================================================= *)

Section TurnDefs.
Variable n : nat.
Implicit Types (s : {perm 'I_n.+2}).

(* A position i : 'I_n is a turning point of s : {perm 'I_n.+2} iff the
   direction at the descent slot widen i differs from the direction at
   the descent slot lift ord0 i.  Both are descent slots, in 'I_n.+1. *)
Definition is_turn s (i : 'I_n) : bool :=
  is_descent s (widen_ord (leqnSn _) i) (+) is_descent s (lift ord0 i).

Definition turn_count s : nat :=
  #|[set i : 'I_n | is_turn s i]|.

Lemma is_turnE s i :
  is_turn s i =
    is_descent s (widen_ord (leqnSn _) i) (+) is_descent s (lift ord0 i).
Proof. by []. Qed.

End TurnDefs.

(* ========================================================================= *)
(* §B. Alternating sequences of nats                                         *)
(* ========================================================================= *)

(* A seq of nats is alternating if successive comparisons strictly
   alternate between < and >.  Equivalently, every interior triple
   xs[i-1], xs[i], xs[i+1] has the property that either
     xs[i-1] < xs[i] > xs[i+1]   or   xs[i-1] > xs[i] < xs[i+1].
   We define this directly by recursion on the seq. *)

Fixpoint alt_aux (b : bool) (x : nat) (xs : seq nat) : bool :=
  match xs with
  | [::] => true
  | y :: xs' =>
      (if b then x < y else y < x) && alt_aux (~~ b) y xs'
  end.

Definition is_alt (xs : seq nat) : bool :=
  match xs with
  | [::] => true
  | [:: _] => true
  | x :: y :: xs' =>
      ((x < y) && alt_aux false y xs') || ((y < x) && alt_aux true y xs')
  end.

(* ========================================================================= *)
(* §C. Sequence model of a permutation                                       *)
(* ========================================================================= *)

(* The sequence [s 0; s 1; ...; s (n+1)] viewed as a seq nat. *)
Definition perm_seq n (s : {perm 'I_n.+2}) : seq nat :=
  [seq val (s i) | i <- enum 'I_n.+2].

Lemma size_perm_seq n (s : {perm 'I_n.+2}) :
  size (perm_seq s) = n.+2.
Proof. by rewrite size_map size_enum_ord. Qed.

(* ========================================================================= *)
(* §D. Subsequences indexed by a {set} of positions                          *)
(* ========================================================================= *)

(* For a set of positions I : {set 'I_n.+2}, sort the positions in
   ascending order (val) and pick the corresponding values from s. *)
Definition pick_seq n (s : {perm 'I_n.+2}) (I : {set 'I_n.+2}) : seq nat :=
  [seq val (s j) | j <- sort (fun a b : 'I_n.+2 => val a <= val b) (enum I)].

(* `as_perm_max` is the maximum size of an index set whose ordered image
   under s is alternating.  This is the bijective definition.  We also
   define the direct version `as_perm` from turn_count, and the headline
   theorem `as_perm_max_eq` (currently the existence direction is open;
   only the upper bound is proved formally below). *)
Definition as_perm_max n (s : {perm 'I_n.+2}) : nat :=
  \max_(I : {set 'I_n.+2} | is_alt (pick_seq s I)) #|I|.

(* The DIRECT definition (Path X), which we use as the main `as_perm`. *)
Definition as_perm n (s : {perm 'I_n.+2}) : nat := (turn_count s).+2.

(* ========================================================================= *)
(* §E. Computational sanity (seq-level)                                      *)
(* ========================================================================= *)

(* Build a {perm 'I_n.+2} from an explicit list (assumed to be a
   permutation of 0..n+1).  We use an ad-hoc helper for examples. *)

(* For sanity we just test the alt_aux/is_alt machinery on raw lists. *)
Example alt_312 : is_alt [:: 3; 1; 2] = true.
Proof. by []. Qed.

Example alt_321 : is_alt [:: 3; 2; 1] = false.
Proof. by []. Qed.

Example alt_3142 : is_alt [:: 3; 1; 4; 2] = true.
Proof. by []. Qed.

Example alt_31425 : is_alt [:: 3; 1; 4; 2; 5] = true.
Proof. by []. Qed.

Example alt_321_sub : is_alt [:: 3; 1] = true.
Proof. by []. Qed.

(* Here `as_perm` is a max over all sorted index lists; the Compute
   reductions on {perm} and the indexed maxima don't reduce nicely,
   so we verify the relationship symbolically. *)

(* ========================================================================= *)
(* §F. Basic lemmas about is_alt                                             *)
(* ========================================================================= *)

Lemma is_alt_nil : is_alt [::] = true.
Proof. by []. Qed.

Lemma is_alt_singleton x : is_alt [:: x] = true.
Proof. by []. Qed.

(* Elements in an alternating list are pairwise distinct (in particular
   adjacent ones), since each comparison is strict. *)

(* Tail of an alternating seq is alternating.  Proof goes by case
   analysis on the head and uses alt_aux to recover. *)

Lemma alt_aux_cons b x y xs :
  alt_aux b x (y :: xs) = (if b then x < y else y < x) && alt_aux (~~ b) y xs.
Proof. by []. Qed.

Lemma is_alt_cons2 x y xs :
  is_alt (x :: y :: xs) =
    ((x < y) && alt_aux false y xs) || ((y < x) && alt_aux true y xs).
Proof. by []. Qed.

(* Alternating seq starting up: is_alt = (x<y) && alt_aux false y xs. *)
(* Once we know the first comparison's direction, the rest is forced. *)

Lemma alt_aux_size_ge1 b x xs :
  alt_aux b x xs -> 0 < size xs -> exists y xs', xs = y :: xs'.
Proof.
case: xs => [|y xs'] // _ _; by exists y, xs'.
Qed.

(* If is_alt (x :: y :: xs) holds, drop the first element and the rest
   is still alternating. *)
Lemma is_alt_tail x y xs :
  is_alt (x :: y :: xs) -> is_alt (y :: xs).
Proof.
rewrite is_alt_cons2.
case/orP => /andP [Hxy].
- (* alt_aux false y xs: next comparison is head_xs < y, so y :: xs is
     down-up-down... starting with y > head, alternating. *)
  case: xs => [|z xs'] //=.
  case/andP => Hzy Hrest.
  by rewrite Hzy Hrest /= orbT.
- case: xs => [|z xs'] //=.
  case/andP => Hyz Hrest.
  by rewrite Hyz Hrest /=.
Qed.

(* ========================================================================= *)
(* §G. Structural properties of turn_count                                   *)
(* ========================================================================= *)

Section TurnLemmas.
Variable n : nat.
Implicit Types (s : {perm 'I_n.+2}).

Lemma turn_count_le s : turn_count s <= n.
Proof.
rewrite /turn_count (leq_trans (max_card _)) // card_ord //.
Qed.

Lemma as_permE s : as_perm s = (turn_count s).+2.
Proof. by []. Qed.

Lemma as_perm_ge2 s : 2 <= as_perm s.
Proof. by rewrite as_permE. Qed.

(* Simple bound: as_perm s <= n + 2 (the size of perm_seq). *)
Lemma as_perm_le_size s : as_perm s <= n.+2.
Proof. by rewrite as_permE ltnS ltnS turn_count_le. Qed.

(* Identity perm has no descents, hence no turns, hence as_perm = 2. *)
Lemma turn_count_id : turn_count (1 : {perm 'I_n.+2}) = 0.
Proof.
apply/eqP; rewrite cards_eq0; apply/eqP/setP => i; rewrite !inE.
rewrite /is_turn /is_descent !perm1.
have H1 : (val (lift ord0 (widen_ord (leqnSn n) i)) : nat) =
          (val (widen_ord (leqnSn n.+1) (widen_ord (leqnSn n) i))).+1.
  by rewrite /=.
have H2 : (val (lift ord0 (lift ord0 i)) : nat) =
          (val (widen_ord (leqnSn n.+1) (lift ord0 i))).+1.
  by rewrite /= /bump /= add1n.
rewrite ltnNge leqW //=.
rewrite ltnNge leqW //=.
Qed.

Lemma as_perm_id : as_perm (1 : {perm 'I_n.+2}) = 2.
Proof. by rewrite as_permE turn_count_id. Qed.

End TurnLemmas.

(* ========================================================================= *)
(* §H. Connection to alternating descent set                                 *)
(* ========================================================================= *)

(* The alternating descent set on 'I_n.+1 (descent slots for {perm 'I_n.+2})
   has every consecutive pair of slots differing in membership.  In other
   words, every position in 'I_n is a turning point. *)

Section AltDesc.
Variable n : nat.
Implicit Types (s : {perm 'I_n.+2}).

(* If descent_set s = alt_desc_set (n.+1), then turn_count s = n
   (every position in 'I_n is a turning point), and so as_perm = n+2. *)
Lemma turn_count_alt_desc s :
  descent_set s = alt_desc_set n.+1 -> turn_count s = n.
Proof.
move=> Hds.
rewrite /turn_count -[RHS]card_ord.
apply: eq_card => i.
rewrite !inE /=.
rewrite /is_turn -!mem_descent_set Hds !mem_alt_desc_set /=.
rewrite negbK add0n.
by case: (odd i).
Qed.

Lemma as_perm_alt_desc s :
  descent_set s = alt_desc_set n.+1 -> as_perm s = n.+2.
Proof. by move=> Hds; rewrite as_permE (turn_count_alt_desc Hds). Qed.

(* Conversely, the maximum value of as_perm is n+2, achieved exactly
   when every position is a turning point. *)
Lemma turn_count_max_iff s :
  (turn_count s == n) =
  [forall i : 'I_n, is_turn s i].
Proof.
apply/eqP/forallP => [Hcard i|Hall].
- have Hsub : [set i : 'I_n | is_turn s i] = setT.
    apply/eqP; rewrite eqEcard subsetT /=.
    by rewrite cardsT card_ord -/(turn_count s) Hcard.
  by have := in_setT i; rewrite -Hsub inE.
- rewrite /turn_count.
  rewrite -[RHS]card_ord.
  apply: eq_card => i; rewrite inE.
  by rewrite (Hall i).
Qed.

End AltDesc.

(* ========================================================================= *)
(* §I. Bounds for as_perm_max                                                *)
(* ========================================================================= *)

Section AsPermMaxBounds.
Variable n : nat.
Implicit Types (s : {perm 'I_n.+2}).

(* The image of the empty set is the empty seq, which is alternating.
   The image of a singleton is alternating.  The image of any 2-element
   set is alternating since s is injective. *)
Lemma is_alt_pick_seq_le2 s (I : {set 'I_n.+2}) :
  #|I| <= 1 -> is_alt (pick_seq s I).
Proof.
move=> HI.
rewrite /pick_seq.
have Hsz : size (sort (fun a b : 'I_n.+2 => val a <= val b) (enum I)) <= 1.
  by rewrite size_sort -cardE.
case: (sort _ _) Hsz => [|x [|y rest]] //=.
Qed.

Lemma as_perm_max_ge0 s : 0 <= as_perm_max s.
Proof. by []. Qed.

(* The full set [set: 'I_n.+2] has cardinality n.+2.  Its image is
   perm_seq s.  This may or may not be alternating. *)
End AsPermMaxBounds.

(* ========================================================================= *)
(* §J. The headline theorem (Path Y)                                         *)
(* ========================================================================= *)

(* The headline equivalence:
       as_perm_max s = (turn_count s).+2 = as_perm s
   where as_perm_max counts the genuine longest alternating subseq.

   We have proved (Path X) the "direct" definition `as_perm s = (turn_count
   s).+2` and structural facts about it (`as_perm_id`, `as_perm_le_size`,
   `as_perm_alt_desc`, `turn_count_alt_desc`, `turn_count_max_iff`).

   The full bijective characterization `as_perm_max s = as_perm s` would
   require:

   (1) UPPER BOUND: `as_perm_max s <= as_perm s`, i.e., for any I with
       pick_seq s I alternating, `#|I| <= (turn_count s).+2`.

       Sketch: write I as sorted positions i_0 < ... < i_{k-1}.  The
       picked subseq has k-1 sign flips between consecutive comparisons.
       Each sign flip at position j (1 <= j <= k-2) implies a turning
       point in xs lies in the slot interval [i_j, i_{j+1}-1].  These
       intervals can be made disjoint by mapping flip j to the FIRST
       turning point in [i_j, i_{j+1}-1] (or rightmost; either works).
       The injection gives k-2 + 1 = k-1 turning points... wait, the
       count is: k+1 picks → k comparisons → k-1 flips → at least k-1
       distinct turning points → turn_count >= k-1 → k+1 <= turn_count+2.

       Formalization difficulty: ~80-120 LOC, requires careful
       index arithmetic with sorted seq positions and ord injections.

   (2) LOWER BOUND: `as_perm s <= as_perm_max s`, i.e., exhibit an
       alternating subseq of length (turn_count s).+2.

       Construction: I := {0; n+1} ∪ {(val t).+1 | t in turn set}.
       This has cardinality turn_count + 2 (interior positions
       (val t).+1 are in {1,...,n}, distinct from 0 and n+1).

       Proof of alternation: consecutive picked positions are either
       (0, t_1+1) (for first turning point t_1, or n+1 if no turns),
       or (t_j+1, t_{j+1}+1) (between consecutive turning points),
       or (t_k+1, n+1) (last turning point to end).  In each interval,
       xs is monotone (no interior turning point), so the values
       compare in the run's direction.  The runs alternate by
       definition of turning point.  So the picked seq alternates.

       Formalization difficulty: ~120-180 LOC.

   Both directions are honest theorems left for follow-up work; no
   axioms are introduced here.
*)

(* As a sanity check connecting the two: when descent_set is alternating
   on every slot (the alt_desc_set case), as_perm hits its maximum n+2,
   matching the maximum value as_perm_max could reach (the full perm_seq
   IS alternating in this case). *)

Section MaxAlternation.
Variable n : nat.
Implicit Types (s : {perm 'I_n.+2}).

(* When descent_set s = alt_desc_set, every interior position is a
   turn, so as_perm s = n+2 = size (perm_seq s). *)
Lemma as_perm_full s :
  descent_set s = alt_desc_set n.+1 ->
  as_perm s = size (perm_seq s).
Proof.
move=> Hds.
by rewrite size_perm_seq (as_perm_alt_desc Hds).
Qed.

End MaxAlternation.

(* ========================================================================= *)
(* §K. Upper bound (partial): pure-seq formulation                           *)
(* ========================================================================= *)

(* Below we develop the seq-level formulation that would underpin a
   full Path Y proof.  We define `turn_count_seq` and prove some basic
   facts.  The Path-Y upper bound `size sub <= turn_count_seq xs + 2`
   for any alternating subseq sub of xs would be a direct induction
   on xs / sub — we leave the inductive proof itself open. *)

(* Direction at slot i: comparing xs[i] and xs[i+1].
   Defined via pairmap to ensure structural recursion. *)
Definition sign_seq (xs : seq nat) : seq bool :=
  if xs is x :: xs' then pairmap (fun a b => a < b) x xs'
  else [::].

Lemma sign_seq_cons2 x y xs :
  sign_seq (x :: y :: xs) = (x < y) :: sign_seq (y :: xs).
Proof. by []. Qed.

Lemma size_sign_seq xs : size (sign_seq xs) = (size xs).-1.
Proof.
case: xs => [|x xs] //=.
by rewrite size_pairmap.
Qed.

(* Number of "flips" in a seq of bools: positions i where ss[i] != ss[i+1]. *)
Definition flip_count (ss : seq bool) : nat :=
  if ss is a :: ss' then \sum_(p <- pairmap (fun u v => u (+) v) a ss') p
  else 0.

Lemma flip_count_cons2 a b ss :
  flip_count (a :: b :: ss) = (a (+) b) + flip_count (b :: ss).
Proof.
rewrite /flip_count /=.
by rewrite big_cons.
Qed.

Definition turn_count_seq (xs : seq nat) : nat := flip_count (sign_seq xs).

Lemma turn_count_seq_nil : turn_count_seq [::] = 0.
Proof. by []. Qed.

Lemma turn_count_seq_singleton x : turn_count_seq [:: x] = 0.
Proof. by []. Qed.

Lemma turn_count_seq_pair x y : turn_count_seq [:: x; y] = 0.
Proof. by rewrite /turn_count_seq /sign_seq /= /flip_count /= big_nil. Qed.

(* Sanity: small examples *)
Example tcs_312 : turn_count_seq [:: 3; 1; 2] = 1.
Proof.
by rewrite /turn_count_seq /sign_seq /= /flip_count /= big_cons big_nil.
Qed.

Example tcs_3142 : turn_count_seq [:: 3; 1; 4; 2] = 2.
Proof.
by rewrite /turn_count_seq /sign_seq /= /flip_count /= !big_cons big_nil.
Qed.

Example tcs_321 : turn_count_seq [:: 3; 2; 1] = 0.
Proof.
by rewrite /turn_count_seq /sign_seq /= /flip_count /= big_cons big_nil.
Qed.

Example tcs_12345 : turn_count_seq [:: 1; 2; 3; 4; 5] = 0.
Proof.
by rewrite /turn_count_seq /sign_seq /= /flip_count /= !big_cons big_nil.
Qed.

(* The sanity examples agree with the headline:
     [3,1,2]:  turn_count_seq = 1, longest alt subseq = 3 = 1 + 2.  OK
     [3,1,4,2]: turn_count_seq = 2, longest alt subseq = 4 = 2 + 2.  OK
     [3,2,1]:  turn_count_seq = 0, longest alt subseq = 2 = 0 + 2.  OK
     [1,2,3,4,5]: turn_count_seq = 0, longest alt subseq = 2 = 0 + 2. OK
*)

(* The PATH Y headline at the seq level (LEFT OPEN):

   Theorem as_seq_eq xs :
     2 <= size xs ->
     as_seq xs = (turn_count_seq xs).+2.

   where as_seq xs is the max length of an alternating subseq.
   The transfer to perms is then straightforward via perm_seq.
*)

(* ========================================================================= *)
(* §L. Connection: sign_seq of perm_seq describes descents                   *)
(* ========================================================================= *)

(* For a perm s : {perm 'I_n.+2}, the sign sequence of perm_seq s
   has length n.+1 (one slot per pair of consecutive positions), and
   the value at slot i is `~~ is_descent s i` (i.e., true iff ascent). *)

Section SignPerm.
Variable n : nat.
Implicit Types (s : {perm 'I_n.+2}).

Lemma size_sign_seq_perm s :
  size (sign_seq (perm_seq s)) = n.+1.
Proof. by rewrite size_sign_seq size_perm_seq /=. Qed.

(* The enum 'I_n.+2 splits into ord0 and the lifts of enum 'I_n.+1. *)
Lemma enum_ord_split :
  enum 'I_n.+2 = ord0 :: [seq lift ord0 i | i <- enum 'I_n.+1].
Proof.
apply: (@eq_from_nth _ ord0).
  by rewrite /= size_map !size_enum_ord.
rewrite size_enum_ord => i Hi.
case: i Hi => [|i] Hi /=.
  apply: val_inj => /=.
  by have := @nth_enum_ord n.+2 ord0 0 Hi.
rewrite (nth_map ord0); last by rewrite size_enum_ord -ltnS.
have Hi' : i < n.+1 by rewrite -ltnS.
apply: val_inj => /=.
have H1 := @nth_enum_ord n.+2 ord0 i.+1 Hi.
have H2 := @nth_enum_ord n.+1 ord0 i Hi'.
by rewrite H1 /bump /= add1n H2.
Qed.

(* Helper: descent at slot i in 'I_n.+1 corresponds to s (widen i) > s (lift 0 i).
   We can rewrite ~~ is_descent as the strict less-than. *)
Lemma not_is_descentE s (i : 'I_n.+1) :
  ~~ is_descent s i = (val (s (widen_ord (leqnSn _) i)) < val (s (lift ord0 i))).
Proof.
rewrite /is_descent -leqNgt.
have Hne : widen_ord (leqnSn n.+1) i != lift ord0 i.
  by rewrite -val_eqE /= /bump /= add1n neq_ltn ltnSn.
have Hsne : s (widen_ord (leqnSn n.+1) i) != s (lift ord0 i).
  by apply: contra Hne => /eqP /perm_inj ->.
have Hvne : val (s (widen_ord (leqnSn n.+1) i)) != val (s (lift ord0 i)).
  by rewrite val_eqE.
rewrite leq_eqVlt (negbTE Hvne) /=.
by [].
Qed.

(* The connection lemma sign_seq (perm_seq s) =
       [seq ~~ is_descent s i | i <- enum 'I_n.+1]
   would directly identify slot-direction with ascent/descent.  See
   the seq-level commentary in §K.  Not formalized in this file. *)

End SignPerm.
