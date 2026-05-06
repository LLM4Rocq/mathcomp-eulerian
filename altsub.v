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

(** [is_turn s i] is the boolean indicator that interior position
    [i : 'I_n] is a turning point of [s : {perm 'I_n.+2}]: the descent
    indicator at slot [widen i] differs (XOR) from the indicator at slot
    [lift ord0 i].  These two slots straddle position [i]. *)
Definition is_turn s (i : 'I_n) : bool :=
  is_descent s (widen_ord (leqnSn _) i) (+) is_descent s (lift ord0 i).

(** [turn_count s] is the number of turning points of [s], i.e., the
    cardinality of [[set i : 'I_n | is_turn s i]].  Stanley §1.6.2: the
    "turn count" governing the longest alternating subsequence length. *)
Definition turn_count s : nat :=
  #|[set i : 'I_n | is_turn s i]|.

(** Definitional unfolding of [is_turn] to its XOR-of-descents form;
    used as a rewrite rule. *)
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

(** [alt_aux b x xs] checks alternation of the seq [x :: xs] given the
    expected direction [b] of the first comparison ([true] = up, [false]
    = down).  Successive directions flip at each step. *)
Fixpoint alt_aux (b : bool) (x : nat) (xs : seq nat) : bool :=
  match xs with
  | [::] => true
  | y :: xs' =>
      (if b then x < y else y < x) && alt_aux (~~ b) y xs'
  end.

(** [is_alt xs] holds when [xs] is alternating: comparisons of consecutive
    elements strictly alternate between [<] and [>].  Two starts are
    possible (up-down or down-up); both are accepted by disjunction. *)
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

(** [perm_seq s] is the one-line word [[s 0; s 1; ...; s (n+1)]] of
    [s : {perm 'I_n.+2}], as a [seq nat]. *)
Definition perm_seq n (s : {perm 'I_n.+2}) : seq nat :=
  [seq val (s i) | i <- enum 'I_n.+2].

(** [perm_seq s] always has length [n.+2]. *)
Lemma size_perm_seq n (s : {perm 'I_n.+2}) :
  size (perm_seq s) = n.+2.
Proof. by rewrite size_map size_enum_ord. Qed.

(* ========================================================================= *)
(* §D. Subsequences indexed by a {set} of positions                          *)
(* ========================================================================= *)

(** [pick_seq s I] is the subseq of [perm_seq s] indexed by the position
    set [I : {set 'I_n.+2}] in ascending order: sort [I] by underlying
    [val], then read off the [s]-values. *)
Definition pick_seq n (s : {perm 'I_n.+2}) (I : {set 'I_n.+2}) : seq nat :=
  [seq val (s j) | j <- sort (fun a b : 'I_n.+2 => val a <= val b) (enum I)].

(** [as_perm_max s] is the bijective definition of [as(s)] from Stanley
    §1.6.2: the maximum cardinality of a position set [I] whose ordered
    image [pick_seq s I] is alternating. *)
Definition as_perm_max n (s : {perm 'I_n.+2}) : nat :=
  \max_(I : {set 'I_n.+2} | is_alt (pick_seq s I)) #|I|.

(** [as_perm s] is the DIRECT definition (Path X) of [as(s)] as
    [(turn_count s).+2].  The headline [as_perm_max_eq] proves these
    two definitions agree. *)
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

(** The empty seq is alternating. *)
Lemma is_alt_nil : is_alt [::] = true.
Proof. by []. Qed.

(** A singleton seq is alternating. *)
Lemma is_alt_singleton x : is_alt [:: x] = true.
Proof. by []. Qed.

(* Elements in an alternating list are pairwise distinct (in particular
   adjacent ones), since each comparison is strict. *)

(* Tail of an alternating seq is alternating.  Proof goes by case
   analysis on the head and uses alt_aux to recover. *)

(** Defining equation of [alt_aux] on a [cons] tail.  Used as a rewrite. *)
Lemma alt_aux_cons b x y xs :
  alt_aux b x (y :: xs) = (if b then x < y else y < x) && alt_aux (~~ b) y xs.
Proof. by []. Qed.

(** Defining equation of [is_alt] on a 2-element prefix [x :: y :: xs]:
    either start with an ascent or a descent.  Used as a rewrite. *)
Lemma is_alt_cons2 x y xs :
  is_alt (x :: y :: xs) =
    ((x < y) && alt_aux false y xs) || ((y < x) && alt_aux true y xs).
Proof. by []. Qed.

(* Alternating seq starting up: is_alt = (x<y) && alt_aux false y xs. *)
(* Once we know the first comparison's direction, the rest is forced. *)

(** Shape lemma: a non-empty seq tail satisfying [alt_aux] decomposes
    as [y :: xs']. *)
Lemma alt_aux_size_ge1 b x xs :
  alt_aux b x xs -> 0 < size xs -> exists y xs', xs = y :: xs'.
Proof.
case: xs => [|y xs'] // _ _; by exists y, xs'.
Qed.

(** Tail closure of [is_alt]: dropping the first element of an
    alternating seq of length at least 2 leaves an alternating seq. *)
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

(** Cardinality bound: the turn-set of [s : {perm 'I_n.+2}] has at
    most [n] turning points. *)
Lemma turn_count_le s : turn_count s <= n.
Proof.
rewrite /turn_count (leq_trans (max_card _)) // card_ord //.
Qed.

(** Definitional unfolding [as_perm s = (turn_count s).+2]; rewrite rule. *)
Lemma as_permE s : as_perm s = (turn_count s).+2.
Proof. by []. Qed.

(** Lower bound: any [as_perm] is at least [2] (the empty/two-element
    base case). *)
Lemma as_perm_ge2 s : 2 <= as_perm s.
Proof. by rewrite as_permE. Qed.

(** Upper bound on [as_perm]: bounded by [n.+2], the size of [perm_seq s]. *)
Lemma as_perm_le_size s : as_perm s <= n.+2.
Proof. by rewrite as_permE ltnS ltnS turn_count_le. Qed.

(** The identity permutation has no descents, hence no turning points:
    [turn_count 1 = 0]. *)
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

(** [as_perm] hits its minimum [2] on the identity permutation. *)
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

(** When [s] has the alternating descent pattern, every interior
    position is a turning point: [turn_count s = n]. *)
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

(** When [s] has the alternating descent pattern, [as_perm s] attains
    its maximum value [n.+2]. *)
Lemma as_perm_alt_desc s :
  descent_set s = alt_desc_set n.+1 -> as_perm s = n.+2.
Proof. by move=> Hds; rewrite as_permE (turn_count_alt_desc Hds). Qed.

(** Characterization of the maximum [turn_count s = n]: equivalent to
    every position [i : 'I_n] being a turning point. *)
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

(** Trivial alternation: any [pick_seq s I] of size at most [1] is
    automatically alternating. *)
Lemma is_alt_pick_seq_le2 s (I : {set 'I_n.+2}) :
  #|I| <= 1 -> is_alt (pick_seq s I).
Proof.
move=> HI.
rewrite /pick_seq.
have Hsz : size (sort (fun a b : 'I_n.+2 => val a <= val b) (enum I)) <= 1.
  by rewrite size_sort -cardE.
case: (sort _ _) Hsz => [|x [|y rest]] //=.
Qed.

(** Trivial nonnegativity of [as_perm_max]; nat-valued. *)
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

(** When the descent set is alternating, [as_perm s] equals the full
    sequence length [size (perm_seq s) = n.+2]. *)
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

(** [sign_seq xs] is the boolean direction sequence at each adjacent
    pair: [xs[i] < xs[i+1]] for [i = 0, ..., size xs - 2].  Empty for
    [xs = nil]. *)
Definition sign_seq (xs : seq nat) : seq bool :=
  if xs is x :: xs' then pairmap (fun a b => a < b) x xs'
  else [::].

(** Cons reduction for [sign_seq] on a 2-prefix. *)
Lemma sign_seq_cons2 x y xs :
  sign_seq (x :: y :: xs) = (x < y) :: sign_seq (y :: xs).
Proof. by []. Qed.

(** Size of [sign_seq xs]: one less than [size xs]. *)
Lemma size_sign_seq xs : size (sign_seq xs) = (size xs).-1.
Proof.
case: xs => [|x xs] //=.
by rewrite size_pairmap.
Qed.

(** [flip_count ss] is the number of adjacent disagreements (XOR
    flips) in a boolean seq [ss].  Counts indices [i] with
    [ss[i] != ss[i+1]]. *)
Definition flip_count (ss : seq bool) : nat :=
  if ss is a :: ss' then \sum_(p <- pairmap (fun u v => u (+) v) a ss') p
  else 0.

(** Cons reduction: flip count of [a :: b :: ss] equals the boundary
    flip [a (+) b] plus the flip count of [b :: ss]. *)
Lemma flip_count_cons2 a b ss :
  flip_count (a :: b :: ss) = (a (+) b) + flip_count (b :: ss).
Proof.
rewrite /flip_count /=.
by rewrite big_cons.
Qed.

(** [turn_count_seq xs] is the seq-level turn count: number of direction
    flips in [xs], i.e., [flip_count (sign_seq xs)].  The seq analogue
    of [turn_count] for permutations. *)
Definition turn_count_seq (xs : seq nat) : nat := flip_count (sign_seq xs).

(** [turn_count_seq] of the empty seq is [0]. *)
Lemma turn_count_seq_nil : turn_count_seq [::] = 0.
Proof. by []. Qed.

(** [turn_count_seq] of a singleton is [0]. *)
Lemma turn_count_seq_singleton x : turn_count_seq [:: x] = 0.
Proof. by []. Qed.

(** [turn_count_seq] of a 2-element seq is [0]: only one comparison,
    no flip. *)
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

(** The sign sequence of [perm_seq s] has length [n.+1], one slot per
    pair of consecutive positions. *)
Lemma size_sign_seq_perm s :
  size (sign_seq (perm_seq s)) = n.+1.
Proof. by rewrite size_sign_seq size_perm_seq /=. Qed.

(** Decomposition of [enum 'I_n.+2] as [ord0] followed by the [lift
    ord0]-image of [enum 'I_n.+1].  Used to align indexing of [perm_seq]
    with [sign_seq]. *)
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

(** Negated descent indicator as a strict less-than: [~~ is_descent s i]
    iff [val (s (widen i)) < val (s (lift ord0 i))]. *)
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

(** Bridge identifying [sign_seq (perm_seq s)] with the (negated)
    descent indicator over [enum 'I_n.+1].  Connects the seq-level
    flip-count machinery to the perm-level descent/turn structure. *)
Lemma sign_seq_perm_seq s :
  sign_seq (perm_seq s) = [seq ~~ is_descent s i | i <- enum 'I_n.+1].
Proof.
apply: (@eq_from_nth _ true).
  by rewrite size_sign_seq_perm size_map size_enum_ord.
move=> i; rewrite size_sign_seq_perm => Hi.
rewrite (nth_map ord0); last by rewrite size_enum_ord.
rewrite /sign_seq /perm_seq.
rewrite enum_ord_split map_cons -map_comp.
rewrite (@nth_pairmap _ 0 _ true (fun a b : nat => a < b)); last first.
  by rewrite size_map size_enum_ord.
rewrite not_is_descentE.
have Hidx : nth ord0 (enum 'I_n.+1) i = Ordinal Hi.
  by apply: val_inj => /=; rewrite nth_enum_ord.
case: i Hi Hidx => [|j] Hi Hidx /=.
- rewrite (nth_map ord0); last by rewrite size_enum_ord.
  rewrite Hidx /=. by congr (s _ < s _); apply: val_inj.
- have Hj : j < n.+1 by apply: ltnW.
  rewrite (nth_map ord0); last by rewrite size_enum_ord.
  rewrite (nth_map ord0); last by rewrite size_enum_ord.
  rewrite Hidx.
  have -> : nth ord0 (enum 'I_n.+1) j = Ordinal Hj.
    by apply: val_inj => /=; rewrite nth_enum_ord.
  by rewrite /=; congr (s _ < s _); apply: val_inj => /=; rewrite /bump /= add1n.
Qed.

End SignPerm.

(* ========================================================================= *)
(* §M. Trivial bound and full-perm special case                              *)
(* ========================================================================= *)

(* The maximum size over alternating subsequence index sets is bounded by
   the size of the underlying sequence, which is n+2. *)
Section AsPermMaxBoundsM.
Variable n : nat.
Implicit Types (s : {perm 'I_n.+2}).

(** Trivial size bound: [as_perm_max s <= n.+2], the size of the
    underlying [perm_seq s]. *)
Lemma as_perm_max_le_size s : as_perm_max s <= n.+2.
Proof.
rewrite /as_perm_max.
apply/bigmax_leqP => I _.
by rewrite (leq_trans (subset_leq_card (subsetT I))) // cardsT card_ord.
Qed.

End AsPermMaxBoundsM.

(* When the picked positions are *all* of 'I_n.+2 (sorted by val), the
   pick_seq is exactly perm_seq s. *)
Section PickSeqFull.
Variable n : nat.
Implicit Types (s : {perm 'I_n.+2}).

(** [enum 'I_m] is sorted by [val] ascending.  Used to identify
    [pick_seq s [set: ...]] with [perm_seq s]. *)
Lemma sorted_val_enum_ord m :
  sorted (fun a b : 'I_m => val a <= val b) (enum 'I_m).
Proof.
have := iota_sorted 0 m.
rewrite -val_enum_ord.
elim: (enum 'I_m) => [|x [|y xs] IH] //=.
move=> /andP [Hxy Hr].
by rewrite Hxy; apply: IH; rewrite /= Hr.
Qed.

(** Picking the full position set yields the full one-line word:
    [pick_seq s [set: 'I_n.+2] = perm_seq s]. *)
Lemma pick_seq_setT s : pick_seq s [set: 'I_n.+2] = perm_seq s.
Proof.
rewrite /pick_seq /perm_seq.
congr [seq val (s _) | _ <- _].
rewrite enum_setT -enumT.
apply: sorted_sort.
- by move=> a b c; apply: leq_trans.
- exact: sorted_val_enum_ord.
Qed.

(** If [perm_seq s] is itself alternating, [as_perm_max s] hits its
    maximum [n.+2] (witnessed by the full set). *)
Lemma as_perm_max_full s :
  is_alt (perm_seq s) -> as_perm_max s = n.+2.
Proof.
move=> Halt.
apply/eqP; rewrite eqn_leq.
apply/andP; split; first exact: as_perm_max_le_size.
have <- : #|[set: 'I_n.+2]| = n.+2 by rewrite cardsT card_ord.
rewrite /as_perm_max.
apply: (leq_bigmax_cond [set: 'I_n.+2]).
by rewrite pick_seq_setT.
Qed.

End PickSeqFull.

(* ========================================================================= *)
(* §N. Auxiliary alt-subseq lemmas (towards the upper bound)                  *)
(* ========================================================================= *)

(** Any seq of size at most [1] is alternating. *)
Lemma is_alt_size_le1 (xs : seq nat) : size xs <= 1 -> is_alt xs.
Proof. by case: xs => [|x [|y xs]]. Qed.

(** An alternating seq of length at least [3] cannot have its first
    three entries strictly monotone in either direction. *)
Lemma is_alt_three x y z xs :
  is_alt (x :: y :: z :: xs) ->
  (x < y < z) = false /\ (z < y < x) = false.
Proof.
rewrite is_alt_cons2 /=.
case/orP => /andP [Hxy].
- case/andP => Hzy _.
  split.
  + by rewrite Hxy /= ltnNge ltnW.
  + by rewrite Hzy /= ltnNge (ltnW Hxy).
- case/andP => Hyz _.
  split.
  + by rewrite ltnNge (ltnW Hxy).
  + apply/andP=> -[Hzy _].
    by have := ltn_trans Hyz Hzy; rewrite ltnn.
Qed.

(** Strict-monotone base case for the upper bound: any alternating
    subseq of a strictly ascending seq has length at most [2]. *)
Lemma is_alt_subseq_strictmono_le2 (xs sub : seq nat) :
  subseq sub xs -> sorted ltn xs -> is_alt sub -> size sub <= 2.
Proof.
move=> Hsub Hxs Halt.
case Hsz: (size sub <= 2) => //.
move/negbT: Hsz; rewrite -ltnNge.
move=> Hsz.
case: sub Hsub Halt Hsz => [|a [|b [|c sub']]] // Hsub Halt _.
have /(_ a b c sub' Halt) [Habs _] := is_alt_three.
have Hsubmono : sorted ltn (a :: b :: c :: sub').
  apply: subseq_sorted Hsub Hxs.
  by move=> x y z; apply: ltn_trans.
move/and3P: Hsubmono => [Hab Hbc _].
have Hab' : a < b := Hab.
have Hbc' : b < c := Hbc.
by rewrite Hab' Hbc' in Habs.
Qed.

(* ========================================================================= *)
(* §P. Slot-interval infrastructure                                          *)
(* ========================================================================= *)

(* The slot interval [i, j) is the set of descent slots in 'I_n.+1 whose
   underlying nat lies between val i (inclusive) and val j (exclusive).
   A "slot" k : 'I_n.+1 controls comparison between positions k and k+1
   of a {perm 'I_n.+2}.  A "turn" t : 'I_n controls the comparison of
   adjacent slots (val t) and (val t).+1 in 'I_n.+1. *)

Section SlotInterval.
Variable n : nat.
Implicit Types (s : {perm 'I_n.+2}).

(** [slot_iv i j] is the set of descent slots [k : 'I_n.+1] whose
    underlying [nat] satisfies [val i <= val k < val j].  Indexes the
    "slot interval" between positions [i] and [j]. *)
Definition slot_iv (i j : 'I_n.+2) : {set 'I_n.+1} :=
  [set k : 'I_n.+1 | (val i <= val k) && (val k < val j)].

(** Membership in [slot_iv i j] unfolded to the [val] inequalities. *)
Lemma mem_slot_iv (i j : 'I_n.+2) (k : 'I_n.+1) :
  (k \in slot_iv i j) = (val i <= val k) && (val k < val j).
Proof. by rewrite inE. Qed.

(** Cardinality of the slot interval: [#|slot_iv i j| = val j - val i],
    when [val j <= n.+1]. *)
Lemma card_slot_iv (i j : 'I_n.+2) :
  val j <= n.+1 ->
  #|slot_iv i j| = val j - val i.
Proof.
move=> Hj.
rewrite cardE size_filter -[Finite.enum _]enumT.
have ME : forall k : 'I_n.+1, mem (slot_iv i j) k
                            = (val i <= val k) && (val k < val j).
  by move=> k; rewrite -mem_slot_iv.
under eq_count => k do rewrite ME.
rewrite -(count_map val (fun m => (val i <= m) && (m < val j))).
rewrite val_enum_ord.
have Hi := ltn_ord i.
have HiSm : val i <= n.+1 by rewrite -ltnS (leq_trans Hi).
case: (leqP (val i) (val j)) => Hij; last first.
  have -> : val j - val i = 0 by apply/eqP; rewrite subn_eq0 ltnW.
  apply/eqP; rewrite -leqn0 leqNgt -has_count; apply/hasPn => m _ /=.
  by case: (leqP (val i) m) => //= Him; rewrite ltnNge (leq_trans (ltnW Hij) Him).
have HX : n.+1 = val i + (n.+1 - val i) by rewrite subnKC.
rewrite [in iota 0 n.+1]HX iotaD count_cat.
have -> : count (fun m : nat => val i <= m < val j) (iota 0 (val i)) = 0.
  apply/eqP; rewrite -leqn0 leqNgt -has_count; apply/hasPn => m.
  rewrite mem_iota add0n => /andP [_ Hm] /=.
  apply/negP => /andP [Hi' _].
  by have := leq_ltn_trans Hi' Hm; rewrite ltnn.
rewrite add0n add0n.
have HY : n.+1 - val i = (val j - val i) + (n.+1 - val j).
  have HK : val j - val i + (n.+1 - val j) = n.+1 - val i.
    apply/eqP; rewrite -(eqn_add2r (val i)) addnAC -addnA subnK //.
    by rewrite addnA (subnK Hij) addnC (subnK Hj).
  by rewrite -HK.
rewrite HY iotaD count_cat.
have -> : count (fun m : nat => val i <= m < val j)
                (iota (val i + (val j - val i)) (n.+1 - val j)) = 0.
  apply/eqP; rewrite -leqn0 leqNgt -has_count; apply/hasPn => m.
  rewrite mem_iota subnKC // => /andP [Hm _] /=.
  by apply/negP => /andP [_ Hm']; have := leq_ltn_trans Hm Hm'; rewrite ltnn.
rewrite addn0.
rewrite -[RHS](size_iota (val i) (val j - val i)) -[in RHS]count_predT.
apply: eq_in_count => m.
rewrite mem_iota => /andP [Hm Hm2] /=.
rewrite subnKC // in Hm2.
by rewrite Hm Hm2.
Qed.

End SlotInterval.

Section InterTurn.
Variable n : nat.
Implicit Types (s : {perm 'I_n.+2}).

(** Constancy of the descent indicator on a turn-free slot interval:
    if no turning point of [s] lies in slot range [[val i, val j)], then
    [is_descent s k1 = is_descent s k2] for all slots [k1, k2] in the
    range.  Used to derive monotone behavior of [s] on turn-free zones. *)
Lemma slot_descent_const s (i j : 'I_n.+2) :
  (forall t : 'I_n, val i <= (val t).+1 < val j -> ~~ is_turn s t) ->
  forall (k1 k2 : 'I_n.+1),
    val i <= val k1 -> val k1 <= val k2 -> val k2 < val j ->
    is_descent s k1 = is_descent s k2.
Proof.
move=> Hnoturn k1 k2 Hi1 H12 H2j.
move: H12 Hi1.
elim: (val k2 - val k1) {-2}k1 (refl_equal (val k2 - val k1)) =>
      [|d IH] k1' Hd H12 Hi1.
- move/eqP: Hd; rewrite subn_eq0 => Hk21.
  have : val k1' = val k2 by apply/eqP; rewrite eqn_leq H12 Hk21.
  by move=> /val_inj ->.
- have Hk1lt : val k1' < val k2 by rewrite -subn_gt0 Hd.
  have Hk1ord : val k1' < n.
    by have := ltn_ord k2; rewrite ltnS => Hk2; rewrite (leq_trans Hk1lt).
  pose t : 'I_n := Ordinal Hk1ord.
  have Ht : val i <= (val t).+1 < val j.
    apply/andP; split; first by rewrite (leq_trans Hi1).
    by rewrite (leq_trans _ H2j).
  have := Hnoturn t Ht.
  rewrite /is_turn negb_add => /eqP Hd1.
  have Hk1eq : (widen_ord (leqnSn n) t : 'I_n.+1) = k1' by apply: val_inj.
  rewrite Hk1eq in Hd1; rewrite Hd1.
  have HSk1 : val (lift ord0 t : 'I_n.+1) = (val k1').+1
    by rewrite /= /bump /= add1n.
  apply: (IH (lift ord0 t)).
  - rewrite HSk1; apply: succn_inj.
    by rewrite subnSK // Hd.
  - by rewrite HSk1.
  - by rewrite HSk1 (leq_trans Hi1).
Qed.

(** Constant-descent implies monotonicity: if [is_descent s k = b] for
    all slots [k] in [[val p, val q)], then [s] is monotone on positions
    [(p, q)]: ascending if [b = false], descending if [b = true]. *)
Lemma constant_descent_monotone s (p q : 'I_n.+2) (b : bool) :
  val p < val q ->
  (forall k : 'I_n.+1, val p <= val k < val q -> is_descent s k = b) ->
  if b then val (s q) < val (s p) else val (s p) < val (s q).
Proof.
move=> Hpq Hconst.
move: q Hpq Hconst.
elim: (n.+2 - val p) {-2}p (refl_equal (n.+2 - val p)) =>
      [|d IH] p' Hd q Hpq Hconst.
  have Hq2 : val q < n.+2 by exact: ltn_ord.
  move/eqP: Hd; rewrite subn_eq0 => Hp'.
  by have := leq_ltn_trans (leq_trans Hp' (ltnW Hpq)) Hq2; rewrite ltnn.
have Hp'lt : val p' < n.+1.
  by rewrite -ltnS; apply: leq_trans (ltn_ord q).
pose k0 : 'I_n.+1 := Ordinal Hp'lt.
have Hwidp : (widen_ord (leqnSn n.+1) k0 : 'I_n.+2) = p' by apply: val_inj.
case: (eqVneq (val q) (val p').+1) => [Hpq1|Hne].
- have Hkrange : val p' <= val k0 < val q by rewrite /= leqnn /= Hpq1.
  have Hkdesc := Hconst k0 Hkrange.
  rewrite /is_descent in Hkdesc.
  have Hliftq : (lift ord0 k0 : 'I_n.+2) = q.
    by apply: val_inj => /=; rewrite /bump /= add1n.
  rewrite Hwidp Hliftq in Hkdesc.
  have Hpqne : p' != q by rewrite -val_eqE neq_ltn Hpq.
  have Hspqne : s p' != s q by apply: contra_neq Hpqne => /perm_inj.
  have Hvspqne : val (s p') != val (s q) by rewrite val_eqE.
  have Hsd : (val (s q) < val (s p'))%N = b by [].
  case Eb : b Hsd => Hsd /=; first by [].
  rewrite -[s p' < s q]/(val (s p') < val (s q))%N.
  rewrite ltn_neqAle leqNgt Hsd /=.
  by rewrite Hvspqne.
- have HqGtSp : (val p').+1 < val q by rewrite ltn_neqAle eq_sym Hne /= Hpq.
  pose pmid : 'I_n.+2 := lift ord0 k0.
  have Hpmid : val pmid = (val p').+1 by rewrite /= /bump /= add1n.
  have Hd' : n.+2 - val pmid = d.
    rewrite Hpmid; apply: succn_inj.
    have Hp'2 : val p' < n.+2 by exact: ltn_ord.
    by rewrite subnSK // Hd.
  have Hpmidq : val pmid < val q by rewrite Hpmid.
  have Hslot1 : val p' <= val k0 < val q.
    by rewrite /= leqnn (ltn_trans _ HqGtSp).
  have Hd1 := Hconst k0 Hslot1.
  rewrite /is_descent Hwidp in Hd1.
  have Hliftpmid : (lift ord0 k0 : 'I_n.+2) = pmid by [].
  rewrite Hliftpmid in Hd1.
  have Hsubconst : forall k : 'I_n.+1,
                     val pmid <= val k < val q -> is_descent s k = b.
    move=> k /andP [Hk1 Hk2].
    apply: Hconst.
    rewrite Hk2 andbT.
    by rewrite (leq_trans _ Hk1) // Hpmid leqnSn.
  have IHmid := IH pmid Hd' q Hpmidq Hsubconst.
  have Hpmidne : pmid != p'.
    by rewrite -val_eqE Hpmid eqn_leq leqNgt ltnSn /=.
  have Hspmidne : s pmid != s p' by apply: contra_neq Hpmidne => /perm_inj.
  have Hvne1 : val (s pmid) != val (s p') by rewrite val_eqE.
  case Eb : b Hd1 IHmid => Hd1 IHmid /=.
  + have Hd1' : (val (s pmid) < val (s p'))%N by [].
    have IHmid' : (val (s q) < val (s pmid))%N by [].
    by apply: ltn_trans IHmid' Hd1'.
  + have HX1 : ~~ (val (s pmid) < val (s p'))%N by rewrite Hd1.
    have Hd1' : (val (s p') < val (s pmid))%N.
      by rewrite ltn_neqAle leqNgt HX1 /=; rewrite eq_sym Hvne1.
    have IHmid' : (val (s pmid) < val (s q))%N by [].
    rewrite -[s p' < s q]/(val (s p') < val (s q))%N.
    by apply: ltn_trans Hd1' IHmid'.
Qed.

(** Direction transport across a turn-free slot range: if no turning
    point lies in [[val i, val j)], then the [s]-comparison direction
    on any sub-pair [(p, q)] inside [[i, j]] matches the boundary
    direction at [(i, j)]. *)
Lemma inter_turn_monotone s (i j : 'I_n.+2) :
  val i < val j ->
  (forall t : 'I_n, val i <= (val t).+1 < val j -> ~~ is_turn s t) ->
  forall (p q : 'I_n.+2),
    val i <= val p -> val p < val q -> val q <= val j ->
    (val (s p) < val (s q))%N = (val (s i) < val (s j))%N.
Proof.
move=> Hij Hnoturn p q Hip Hpq Hqj.
have Hjle : val i < n.+1.
  by have := ltn_ord j; rewrite ltnS => Hj2; rewrite (leq_trans Hij).
pose k0 : 'I_n.+1 := Ordinal Hjle.
have Hk0range : val i <= val k0 < val j by rewrite /= leqnn /= Hij.
pose b := is_descent s k0.
have Hconst_ij : forall k : 'I_n.+1,
                   val i <= val k < val j -> is_descent s k = b.
  move=> k /andP [Hki Hkj].
  case: (leqP (val k0) (val k)) => Hkk0.
  - rewrite /b /=.
    by apply: esym; apply: (slot_descent_const Hnoturn) => //=.
  - apply: (slot_descent_const Hnoturn) => //=.
    exact: ltnW.
have Hconst_pq : forall k : 'I_n.+1,
                   val p <= val k < val q -> is_descent s k = b.
  move=> k /andP [Hkp Hkq].
  apply: Hconst_ij.
  by rewrite (leq_trans Hip Hkp) /= (leq_trans Hkq).
have Hmono_ij := constant_descent_monotone Hij Hconst_ij.
have Hmono_pq := constant_descent_monotone Hpq Hconst_pq.
case Eb : b Hmono_ij Hmono_pq => Hmono_ij Hmono_pq /=.
- rewrite ltnNge (ltnW Hmono_pq) /=.
  by rewrite ltnNge (ltnW Hmono_ij) /=.
- by rewrite Hmono_pq Hmono_ij.
Qed.

(** Existence of a witness turn for any sign flip: if three positions
    [i < j < k] have an [s]-comparison flip across the middle, then
    some turning point of [s] lies in the slot interval [[val i, val k)]. *)
Lemma pick_flip_has_turn s (i j k : 'I_n.+2) :
  val i < val j < val k ->
  (val (s i) < val (s j))%N <> (val (s j) < val (s k))%N ->
  exists t : 'I_n, (val i <= (val t).+1 < val k) /\ is_turn s t.
Proof.
move=> /andP [Hij Hjk] Hflip.
have Hik : val i < val k by apply: ltn_trans Hij Hjk.
case Habs :
    [exists t : 'I_n, (val i <= (val t).+1 < val k) && is_turn s t].
  case/existsP: Habs => t /andP [Ht Htn].
  by exists t; split.
exfalso; apply: Hflip.
have Habs' : forall t : 'I_n,
               ~ ((val i <= (val t).+1 < val k) /\ is_turn s t).
  move=> t [Ht Htn].
  have Hcontra :
      ~ [exists t0 : 'I_n,
            (val i <= (val t0).+1 < val k) && is_turn s t0]
    by rewrite Habs.
  by apply: Hcontra; apply/existsP; exists t; rewrite Ht Htn.
have Hno' : forall t : 'I_n,
              val i <= (val t).+1 < val k -> ~~ is_turn s t.
  move=> t Ht; apply/negP => Htn; by apply: (Habs' t).
rewrite (inter_turn_monotone Hik Hno' (p := i) (q := j)) //; last exact: ltnW.
by rewrite (inter_turn_monotone Hik Hno' (p := j) (q := k)) // ltnW.
Qed.

End InterTurn.

(* ========================================================================= *)
(* §O. Status of the headline equivalence (open)                              *)
(* ========================================================================= *)

(* The headline equivalence
       as_perm_max s = (turn_count s).+2
   reduces, given the bridge `sign_seq_perm_seq` proven above and the
   trivial bound `as_perm_max_le_size`, to:

   (1) UPPER BOUND: an alternating pick_seq has length at most
       (turn_count s).+2.

       Sketch: a pick_seq of length k > 1 has sign_seq of length k-1.
       If alternating, every adjacent pair in sign_seq differs, so
       flip_count (sign_seq (pick_seq s I)) = k-2.  We need
         flip_count (sign_seq (pick_seq s I)) <= turn_count s.
       This follows from a "subseq monotonicity": each sign-flip in
       the pick_seq corresponds to a turning point of s in the slot
       interval [i_j, i_{j+1}-1].  An injective assignment of flips
       to turning points (mapping flip j to its leftmost turning point)
       gives the required bound.  Roughly 80-120 LOC of careful
       slot-interval bookkeeping.

   (2) EXISTENCE: there is a pick_seq of length (turn_count s).+2 that
       is alternating.

       Construction: I := {ord0; ord_max} ∪ {(val t).+1 | t turning of s}.
       Cardinality: turn_count s + 2 (interior positions are distinct
       from 0 and n+1 by construction).
       Alternation: between consecutive picked positions, the slot
       interval contains no turning point of s (by construction), so
       s is monotone there; consecutive runs differ in direction (by
       definition of turning), so the picked values alternate.
       Roughly 100-180 LOC.

   We have proven the special case `as_perm_max_full`: when perm_seq s
   itself is alternating, as_perm_max s = n+2 = (turn_count s).+2.
*)

(* ========================================================================= *)
(* §Q. Upper bound: as_perm_max s <= (turn_count s).+2                       *)
(* ========================================================================= *)

(* Strategy:
   - Define `turn_iv s a b` = set of turns t : 'I_n with (val t).+1 in [a, b).
   - Key combinatorial lemma `flip_count_le_turn_iv`: for any sorted-strict
     sequence xs of positions, the flip_count of (sign_seq (s applied to xs))
     is bounded by #|turn_iv s a b| for appropriate boundaries [a, b).
   - Combined with `is_alt_flip_count` (alt seq has flip_count = size - 2)
     and `card_turn_iv_le`, this gives the upper bound.

   Status: the key lemma `flip_count_le_turn_iv` is currently ADMITTED.
   Session 3 should close this combinatorial step.  See the comment above
   the Admitted lemma for the proof approach (Hall-style injection of
   flips to leftmost witnessed turns).

   The base infrastructure in §P (`slot_iv`, `inter_turn_monotone`,
   `pick_flip_has_turn`) plus the new `turn_iv_split` provide all the
   tools needed.
*)

Section UpperBound.
Variable n : nat.
Implicit Types (s : {perm 'I_n.+2}).

(** [turn_iv s a b] is the set of turning points [t : 'I_n] of [s]
    whose witness position [(val t).+1] lies in the half-open interval
    [[a, b)]. *)
Definition turn_iv s (a b : nat) : {set 'I_n} :=
  [set t : 'I_n | is_turn s t && (a <= (val t).+1 < b)].

(** Membership in [turn_iv s a b] unfolded to its conjunction. *)
Lemma mem_turn_iv s a b (t : 'I_n) :
  (t \in turn_iv s a b) = (is_turn s t && (a <= (val t).+1 < b)).
Proof. by rewrite inE. Qed.

(** [turn_iv s a b] is a subset of the global turn set of [s]. *)
Lemma turn_iv_subset s a b :
  turn_iv s a b \subset [set t : 'I_n | is_turn s t].
Proof. by apply/subsetP => t; rewrite !inE; case/andP => ->. Qed.

(** Cardinality bound: [#|turn_iv s a b| <= turn_count s]. *)
Lemma card_turn_iv_le s a b :
  #|turn_iv s a b| <= turn_count s.
Proof. exact: subset_leq_card (turn_iv_subset s a b). Qed.

(** Additivity of [turn_iv] cardinality on a split point [b]:
    [#|turn_iv s a c| = #|turn_iv s a b| + #|turn_iv s b c|]
    when [a <= b <= c]. *)
Lemma turn_iv_split s (a b c : nat) :
  a <= b -> b <= c ->
  #|turn_iv s a c| = #|turn_iv s a b| + #|turn_iv s b c|.
Proof.
move=> Hab Hbc.
have Heq : turn_iv s a c = turn_iv s a b :|: turn_iv s b c.
  apply/setP => t; rewrite !inE.
  apply/and3P/orP.
    case=> Hturn Hat Htc.
    case: (ltnP (val t).+1 b) => Htb.
      by left; apply/and3P; split.
    by right; apply/and3P; split.
  case=> /and3P [Hturn H1 H2]; split=> //.
    exact: leq_trans H2 Hbc.
  exact: leq_trans Hab H1.
rewrite Heq cardsU.
have -> : turn_iv s a b :&: turn_iv s b c = set0.
  apply/setP => t; rewrite !inE.
  apply/negP => /andP [/and3P [_ _ Htb] /and3P [_ Hbt _]].
  by have := leq_ltn_trans Hbt Htb; rewrite ltnn.
by rewrite cards0 subn0.
Qed.

(* THE KEY COMBINATORIAL LEMMA — currently OPEN (session 3 task).

   For a strictly sorted sequence xs of positions in 'I_n.+2,
   the flip_count of the sign-seq of the picked perm-values is bounded
   by the number of turns in the slot-interval covering xs.

   PROOF STRATEGY (for session 3):

   Use strong induction on size xs.  Base: size <= 2, flip_count = 0.

   Inductive step (size k+1 >= 3, xs = x0 :: x1 :: x2 :: rest):

   CASE 1: (s x0 < s x1) = (s x1 < s x2)  [no flip at position 0]
     flip_count(xs) = flip_count(x1 :: rest).  Apply IH to (x1::rest)
     with the bound [val x1, val j); use turn_iv monotonicity in left
     endpoint to extend to [val i, val j).

   CASE 2: (s x0 < s x1) ≠ (s x1 < s x2)  [flip at position 0]
     SUBCASE 2A: ∃ turn t in [val x0, val x1).
       Peel x0.  flip_count(xs) = 1 + flip_count(x1::rest).
       Use turn t to absorb the +1 via `turn_iv_split`.
     SUBCASE 2B: NO turn in [val x0, val x1).  By `pick_flip_has_turn`
       and the empty first half, the witness for the flip lies in
       [val x1, val x2).  THE HARD CASE — naive IH fails because
       the witness gets "double-counted" by the IH's bound.

       Resolution (Hall-style refinement): strengthen the IH to a
       STRICT bound when the first slot interval [val xs[0], val xs[1])
       has a turn, OR to track a "sign carry" that absorbs the
       boundary case.  Equivalently, use the leftmost-witness
       greedy assignment with a careful proof that consecutive
       leftmost witnesses are distinct.

   ALTERNATIVE: prove via `inter_turn_monotone` that fully
   alternating flip patterns force ≥ k turns; this avoids case
   analysis but requires a parity-counting lemma.

   Estimated effort: 60-100 LOC.  The base infrastructure
   (`turn_iv_split`, `inter_turn_monotone`, `pick_flip_has_turn`)
   provides the necessary tools.
*)
(* Lemma flip_count_le_turn_iv s (xs : seq 'I_n.+2) :
     sorted (fun a b : 'I_n.+2 => val a < val b) xs ->
     forall (i j : 'I_n.+2),
     val i <= val (head i xs) -> val (last i xs) <= val j ->
     flip_count (sign_seq [seq val (s x) | x <- xs])
       <= #|turn_iv s (val i) (val j)|.
   STILL OPEN — but session B-4 made significant infrastructure progress.
   See §Q.1 below for the seq-level building blocks (`triangle_xor_nat_g`,
   `bool_triangle`, `flip_count_pairmap_insert_anywhere`). The key
   reduction now needed: assemble these into the TURN-INTERVAL bound. *)

End UpperBound.

(* ========================================================================= *)
(* §Q.1. Seq-level monotonicity infrastructure (Session B-4)                  *)
(* ========================================================================= *)

(* These are PURE NAT-SEQ lemmas (no perm/turn structure). They establish
   that flip_count is MONOTONE w.r.t. seq insertion — i.e., inserting one
   element into a nat seq preserves or increases flip_count. This gives a
   bridge to the GLOBAL bound:
     flip_count(sign_seq(s @ xs)) <= flip_count(sign_seq(perm_seq s)) = turn_count s
   for sorted-strict xs being a sub-listing of enum 'I_n.+2.

   The pieces below FULLY PROVE the per-step monotonicity; the open work
   is iterating this through subseq + applying it to the perm setting.

   STATUS: building blocks are CLOSED, no axioms. The integration into
   `flip_count_le_turn_iv` (or its global cousin `flip_count_le_turn_count`)
   is SESSION B-5 work — see comment at the end. *)

(** Hamming-style triangle inequality on three booleans:
    [a XOR c <= (a XOR b) + (b XOR c)].  Building block for the
    flip-count monotonicity arguments. *)
Lemma bool_triangle (a b c : bool) : (a (+) c) <= (a (+) b) + (b (+) c).
Proof. by case: a; case: b; case: c. Qed.

(** Triangle inequality for XOR of strict nat comparisons, used to
    bound the flip count when an element is inserted between two others.
    Exploits the transitivity / total-order structure of [<] on nats. *)
Lemma triangle_xor_nat_g (a x y z : nat) :
  (a < x) (+) (x < z) <= (a < x) (+) (x < y) + ((x < y) (+) (y < z)).
Proof.
case Hxy : (x < y)%N; case Hyz : (y < z)%N.
- have Hxz : (x < z)%N by exact: ltn_trans Hxy Hyz.
  rewrite Hxz /=.
  by case: (a < x)%N.
- by case: (a < x)%N; case: (x < z)%N.
- by case: (a < x)%N; case: (x < z)%N.
- move/negbT: Hxy; rewrite -leqNgt => Hyx.
  move/negbT: Hyz; rewrite -leqNgt => Hzy.
  have Hxz : ~~ (x < z)%N by rewrite -leqNgt (leq_trans Hzy Hyx).
  rewrite (negbTE Hxz) /=.
  by case: (a < x)%N.
Qed.

(** Mirror variant of [triangle_xor_nat_g] with the middle position on
    the left.  Used for "insert at front" reductions in flip count. *)
Lemma triangle_xor_nat (w y z r : nat) :
  (w < z) (+) (z < r) <= (w < y) (+) (y < z) + ((y < z) (+) (z < r)).
Proof.
case Hwz : (w < z)%N; case Hzr : (z < r)%N; rewrite /= ?addn0 ?addn1.
- exact: leq0n.
- case Hwy : (w < y)%N; case Hyz : (y < z)%N; rewrite //=.
  move/negbT: Hwy; rewrite -leqNgt => Hyw.
  move/negbT: Hyz; rewrite -leqNgt => Hzy.
  have Hwz' : ~~ (w < z)%N by rewrite -leqNgt (leq_trans Hzy Hyw).
  by rewrite Hwz in Hwz'.
- case Hwy : (w < y)%N; case Hyz : (y < z)%N; rewrite //=.
  have Hwz' : (w < z)%N by exact: ltn_trans Hwy Hyz.
  by rewrite Hwz in Hwz'.
- exact: leq0n.
Qed.

(** Front-insertion monotonicity for [flip_count] on a [pairmap]:
    inserting one element at the front never decreases the flip count.
    Step 1 building block for [flip_count_pairmap_insert_anywhere]. *)
Lemma flip_count_pairmap_insert (a y : nat) (xs : seq nat) :
  flip_count (pairmap (fun u : nat => [eta leq u.+1]) a xs) <=
  flip_count (pairmap (fun u : nat => [eta leq u.+1]) a (y :: xs)).
Proof.
case: xs => [|x xs] /=.
- by rewrite /flip_count /= big_nil.
- case Exs : xs => [|x' xs'] /=.
  + rewrite /flip_count /= !big_cons big_nil !addn0.
    by case: ((a < y)%N (+) (y < x)%N).
  + rewrite /flip_count /= !big_cons.
    rewrite addnA leq_add2r.
    exact: (triangle_xor_nat a y x x').
Qed.

(** Inductive step helper for [flip_count_pairmap_insert_anywhere]:
    combines the IH bound [s1 <= ... + s2] with a structural matching
    condition to handle the four [(x < z) = (y < z)] cases uniformly. *)
Lemma flip_step_helper (a x y z : nat) (s1 s2 : nat) :
  s1 <= ((x < y) (+) (y < z)) + s2 ->
  ((x < z) = (y < z) -> s1 = s2) ->
  (a < x) (+) (x < z) + s1 <= (a < x) (+) (x < y) + ((x < y) (+) (y < z) + s2).
Proof.
move=> IHv Hsame.
case Hxz : (x<z)%N; case Hyz : (y<z)%N.
- have Hs : s1 = s2 by apply: Hsame; rewrite Hxz Hyz.
  rewrite Hs addnA leq_add2r.
  exact: bool_triangle.
- have Hxy : (x < y)%N.
    move/negbT: Hyz; rewrite -leqNgt => Hzy.
    have Hxz' : (x<z)%N by rewrite Hxz.
    exact: leq_trans Hxz' Hzy.
  rewrite Hxy /=.
  rewrite leq_add2l.
  by rewrite Hxy Hyz /= in IHv.
- have Hyx : (x < y)%N = false.
    move/negbT: Hxz; rewrite -leqNgt => Hzx.
    have Hyz' : (y<z)%N by rewrite Hyz.
    have Hyx' : (y < x)%N by exact: leq_trans Hyz' Hzx.
    apply/negbTE; rewrite -leqNgt; exact: ltnW.
  rewrite Hyx /=.
  rewrite Hyx Hyz /= in IHv.
  rewrite leq_add2l.
  exact: IHv.
- have Hs : s1 = s2 by apply: Hsame; rewrite Hxz Hyz.
  rewrite Hs addnA leq_add2r.
  exact: bool_triangle.
Qed.

(** Insertion-anywhere monotonicity for [flip_count] on a [pairmap]:
    inserting one element at any position never decreases the flip
    count.  Generalizes [flip_count_pairmap_insert] to interior
    positions. *)
Lemma flip_count_pairmap_insert_anywhere (xs ys : seq nat) (y : nat) (a : nat) :
  flip_count (pairmap (fun u : nat => [eta leq u.+1]) a (xs ++ ys)) <=
  flip_count (pairmap (fun u : nat => [eta leq u.+1]) a (xs ++ y :: ys)).
Proof.
move: a; elim: xs => [|x xs IH] a /=.
- exact: flip_count_pairmap_insert.
- have IHv := IH x.
  case Exs : xs IHv => [|x' xs'] IHv.
  + rewrite /= in IHv |- *.
    case Eys : ys IHv => [|z ys'] IHv.
    * rewrite /flip_count /= !big_cons big_nil !addn0.
      by case: ((a < x)%N (+) (x < y)%N).
    * rewrite /flip_count /= !big_cons in IHv |- *.
      apply: flip_step_helper.
      -- exact: IHv.
      -- by move=> ->.
  + rewrite /=.
    rewrite /flip_count /= !big_cons.
    rewrite leq_add2l.
    rewrite /= in IHv.
    exact: IHv.
Qed.

(** Sign-seq front-insertion monotonicity: inserting [y] at the front
    of [xs] never decreases [flip_count (sign_seq _)]. *)
Lemma flip_count_sign_seq_insert_front (y : nat) (xs : seq nat) :
  flip_count (sign_seq xs) <= flip_count (sign_seq (y :: xs)).
Proof.
case: xs => [|x xs] /=.
  by [].
case: xs => [|x' xs'] /=.
  by rewrite /flip_count /= big_nil.
rewrite /flip_count /= !big_cons.
by case: ((y < x)%N (+) (x < x')%N).
Qed.

(* SESSION B-5 ROADMAP: complete the proof of `flip_count_le_turn_iv` (or
   equivalently the global `flip_count_le_turn_count`).

   Key steps remaining:

   1. Generalize `flip_count_pairmap_insert_anywhere` from "insert one"
      to "subseq". Concretely:
        Lemma flip_count_pairmap_le_subseq (a : nat) (xs ys : seq nat) :
          subseq xs ys ->
          flip_count (pairmap leq.+1 a xs) <= flip_count (pairmap leq.+1 a ys).
      Proof by induction on ys + case on whether to take or skip the head.
      ~30 LOC.

   2. Specialize to sign_seq:
        Lemma flip_count_sign_seq_le_subseq (xs ys : seq nat) :
          subseq xs ys ->
          flip_count (sign_seq xs) <= flip_count (sign_seq ys).
      Direct from (1) using the relation `sign_seq xs = pairmap leq.+1 (head 0 xs) (behead xs)`.
      ~10 LOC.

   3. Apply to perm_seq: for sorted-strict xs in 'I_n.+2 being a sub-listing
      (after sorted_subseq_sort or similar) of perm_seq s:
        flip_count(sign_seq(s @ xs)) ≤ flip_count(sign_seq(perm_seq s))
      ~20 LOC of sort/subseq manipulation.

   4. Compute flip_count of perm_seq:
        flip_count(sign_seq(perm_seq s)) = turn_count s
      Direct from `sign_seq_perm_seq` + counting argument.
      ~30 LOC.

   5. Final assembly: as_perm_max s ≤ (turn_count s).+2.
      ~15 LOC.

   Total estimated: ~100 LOC. The HARD CASES are now CLOSED above. *)

(* ========================================================================= *)
(* §Q.2. Subseq monotonicity for flip_count (Session B-5, Step 1-2)          *)
(* ========================================================================= *)

(** Strict-subseq dropping: if [xs] is a proper subseq of [ys], some
    index [i] of [ys] can be removed while still containing [xs]. *)
Lemma subseq_drop_extra (xs ys : seq nat) :
  subseq xs ys -> size xs < size ys ->
  exists i, i < size ys /\
    subseq xs (take i ys ++ drop i.+1 ys).
Proof.
elim: ys xs => [|y ys IH] xs //=.
case: xs => [|x xs] /=.
- move=> _ _.
  exists 0; split => //=.
  by rewrite drop0 sub0seq.
- case Eeq : (x == y) => Hsub Hsz.
  + have Hsz' : size xs < size ys by [].
    have [i [Hi Hsubi]] := IH xs Hsub Hsz'.
    exists i.+1; split => //=.
    by rewrite Eeq.
  + exists 0; split => //=.
    by rewrite drop0.
Qed.

(** Size of [ys] with element at position [i] removed: [(size ys).-1]. *)
Lemma size_take_drop_skip (i : nat) (ys : seq nat) :
  i < size ys -> size (take i ys ++ drop i.+1 ys) = (size ys).-1.
Proof.
move=> Hi.
rewrite size_cat size_take size_drop Hi.
case Hsz : (size ys) Hi => [|m] Hi //=.
rewrite subSS.
have Him : i <= m by rewrite -ltnS.
by rewrite subnKC.
Qed.

(** Subseq monotonicity for [flip_count] on a [pairmap]: if [xs] is a
    subseq of [ys], its flip count is at most that of [ys].  Iterates
    [flip_count_pairmap_insert_anywhere] across the size difference. *)
Lemma flip_count_pairmap_le_subseq (xs ys : seq nat) :
  subseq xs ys ->
  forall a : nat,
  flip_count (pairmap (fun u : nat => [eta leq u.+1]) a xs) <=
  flip_count (pairmap (fun u : nat => [eta leq u.+1]) a ys).
Proof.
move=> Hsub.
have [k Hk] : exists k, size ys = size xs + k.
  by exists (size ys - size xs); rewrite addnC subnK //; exact: size_subseq.
move: xs ys Hsub Hk.
elim: k => [|k IH] xs ys Hsub Hk a.
- rewrite addn0 in Hk.
  have HL := size_subseq_leqif Hsub.
  have Heq : xs = ys.
    by case: HL => _ Hiff; apply/eqP; rewrite -Hiff Hk.
  by rewrite Heq.
- have Hszlt : size xs < size ys by rewrite Hk addnS ltnS leq_addr.
  have [i [Hi Hsubi]] := subseq_drop_extra Hsub Hszlt.
  pose ys' := take i ys ++ drop i.+1 ys.
  have Hsz' : size ys' = size xs + k.
    have := size_take_drop_skip Hi.
    rewrite -/ys' Hk addnS /=.
    by case Hsz0: (size ys) => [|m] //= [->].
  have IHv := IH xs ys' Hsubi Hsz' a.
  apply: leq_trans IHv _.
  have Hys_split : ys = take i ys ++ (nth 0 ys i :: drop i.+1 ys).
    rewrite -[in LHS](cat_take_drop i ys).
    congr (_ ++ _).
    by rewrite (drop_nth 0 Hi).
  rewrite [X in _ <= flip_count (pairmap _ _ X)]Hys_split.
  exact: flip_count_pairmap_insert_anywhere.
Qed.

(** Subseq monotonicity specialized to [sign_seq]: if [xs] is a subseq
    of [ys], then [flip_count (sign_seq xs) <= flip_count (sign_seq ys)].
    Used in [as_perm_max_upper] to bound subseq alternation by the global
    flip count. *)
Lemma flip_count_sign_seq_le_subseq (xs ys : seq nat) :
  subseq xs ys ->
  flip_count (sign_seq xs) <= flip_count (sign_seq ys).
Proof.
move=> Hsub.
case: xs Hsub => [|x xs] Hsub /=.
- by [].
- case: ys Hsub => [|y ys] Hsub.
  + by move: Hsub; rewrite /= => /eqP.
  + rewrite /sign_seq /=.
    case Eeq : (x == y) Hsub => Hsub.
    * move/eqP: Eeq => Eeq; rewrite Eeq in Hsub *.
      have Hsub' : subseq xs ys.
        by move: Hsub; rewrite /= eq_refl.
      exact: flip_count_pairmap_le_subseq Hsub' y.
    * have Hsubys : subseq (x :: xs) ys.
        by move: Hsub; rewrite /= Eeq.
      have Hstep1 := flip_count_sign_seq_insert_front y (x :: xs).
      rewrite /sign_seq /= in Hstep1.
      have Hstep2 : flip_count (pairmap (fun u : nat => [eta leq u.+1]) y (x :: xs)) <=
                    flip_count (pairmap (fun u : nat => [eta leq u.+1]) y ys).
        exact: flip_count_pairmap_le_subseq Hsubys y.
      exact: leq_trans Hstep1 Hstep2.
Qed.

(* ========================================================================= *)
(* §R. Seq-level: alternating seq has flip_count(sign_seq) = size - 2.       *)
(* ========================================================================= *)

(** [is_alt_bool_aux a xs] checks alternation of a boolean seq with a
    leading "previous" element [a]: every adjacent pair must XOR to true. *)
Fixpoint is_alt_bool_aux (a : bool) (xs : seq bool) : bool :=
  match xs with
  | [::] => true
  | b :: rest => (a (+) b) && is_alt_bool_aux b rest
  end.

(** [is_alt_bool xs] holds when the boolean seq [xs] is fully
    alternating: every adjacent pair differs. *)
Definition is_alt_bool (xs : seq bool) : bool :=
  match xs with
  | [::] => true
  | a :: rest => is_alt_bool_aux a rest
  end.

(** Fully alternating boolean seqs maximize flip count:
    [flip_count xs = (size xs).-1] when [is_alt_bool xs] holds. *)
Lemma flip_count_is_alt_bool xs :
  is_alt_bool xs -> flip_count xs = (size xs).-1.
Proof.
case: xs => [|a xs] //=.
elim: xs a => [|b xs IH] a //=.
  by rewrite /flip_count /= big_nil.
case/andP => Hab Halt.
rewrite /flip_count /= big_cons Hab /=.
have IHv := IH b Halt.
rewrite /flip_count /= in IHv.
by rewrite IHv add1n.
Qed.

(** The sign seq of an [is_alt] nat seq is itself fully alternating
    as a boolean seq: every adjacent direction pair differs. *)
Lemma sign_seq_is_alt xs :
  is_alt xs -> 2 <= size xs -> is_alt_bool (sign_seq xs).
Proof.
case: xs => [|x [|y rest]] //=.
move=> Halt _.
move: x y Halt; elim: rest => [|z rest IH] x y //= Halt.
case/orP: Halt => /andP [Hcmp Halt].
- case/andP: Halt => Hzy Halt2.
  rewrite Hcmp /=.
  have Hyzn : ~~ (y < z) by rewrite -leqNgt ltnW.
  rewrite (negbTE Hyzn) /=.
  have Halt' : (y < z) && alt_aux false z rest || (z < y) && alt_aux true z rest.
    by rewrite Hzy Halt2 /= orbT.
  have IHv := IH y z Halt'.
  by move: IHv; rewrite (negbTE Hyzn).
- case/andP: Halt => Hyz Halt2.
  have Hxyn : ~~ (x < y) by rewrite -leqNgt ltnW.
  rewrite (negbTE Hxyn) Hyz /=.
  have Halt' : (y < z) && alt_aux false z rest || (z < y) && alt_aux true z rest.
    by rewrite Hyz Halt2 /=.
  have IHv := IH y z Halt'.
  by move: IHv; rewrite Hyz.
Qed.

(** Flip-count formula for alternating seqs: an [is_alt] seq of size
    at least [2] has [flip_count (sign_seq xs) = (size xs).-2].  Used
    in [as_perm_max_upper] to reduce alternation to flip-count bounds. *)
Lemma is_alt_flip_count xs :
  is_alt xs -> 2 <= size xs -> flip_count (sign_seq xs) = (size xs).-2.
Proof.
move=> Halt Hsz.
have := flip_count_is_alt_bool (sign_seq_is_alt Halt Hsz).
rewrite size_sign_seq.
by case: xs Halt Hsz => [|x [|y [|z rest]]] //= _ _ ->.
Qed.

(* ========================================================================= *)
(* §S. Final assembly: as_perm_max_upper                                      *)
(* ========================================================================= *)

Section UpperBoundAssembly.
Variable n : nat.
Implicit Types (s : {perm 'I_n.+2}).

(** Sorting the enumeration of a [{set 'I_n.+2}] by [val] gives a
    strictly sorted seq, since the underlying enumeration is
    duplicate-free. *)
Lemma sort_enum_strict_sorted (I : {set 'I_n.+2}) :
  sorted (fun a b : 'I_n.+2 => val a < val b)
         (sort (fun a b : 'I_n.+2 => val a <= val b) (enum I)).
Proof.
have Hsort := sort_sorted (T := 'I_n.+2)
  (fun a b => leq_total (val a) (val b)) (enum I).
have Huniq : uniq (sort (fun a b : 'I_n.+2 => val a <= val b) (enum I)).
  by rewrite sort_uniq enum_uniq.
move: Hsort Huniq.
elim: (sort _ _) => [|a [|b xs] IH] //= /andP [Hab Hsorted] /andP [Han Hu].
have Hab' : val a < val b.
  rewrite ltn_neqAle Hab andbT.
  apply/eqP => Hva.
  have Hab2 : a = b by apply: val_inj.
  by move: Han; rewrite Hab2 inE eq_refl.
rewrite Hab' /=.
exact: IH.
Qed.

(* THE HEADLINE THEOREM (UPPER BOUND) — pending flip_count_le_turn_iv.
   Once that key combinatorial lemma lands, the assembly proof is
   ~35 lines; the full text is preserved in the git history at the
   commit just before this revert (session-2 attempt that introduced
   an Admitted; reverted to keep the project axiom-free).  *)

End UpperBoundAssembly.

(* ========================================================================= *)
(* §T. Existence: as_perm_max s >= (turn_count s).+2                          *)
(* ========================================================================= *)

(* Construction: I := {ord0; ord_max} ∪ {(val t).+1 | t turning point of s}.
   The picked sequence is alternating because between consecutive picked
   positions there are no turning points (by construction), so s is monotone
   there (by inter_turn_monotone), and adjacent runs alternate in direction
   (because each interior witness corresponds to a turning point). *)

Section LowerBound.
Variable n : nat.
Implicit Types (s : {perm 'I_n.+2}).

(** [turn_inj t] injects an interior position [t : 'I_n] into
    [{ 'I_n.+2 }] at the offset [(val t).+1].  Used to construct the
    witness set [turn_witness] for the lower-bound construction. *)
Definition turn_inj (t : 'I_n) : 'I_n.+2 :=
  lift ord0 (widen_ord (leqnSn n) t).

(** Underlying value of [turn_inj t]: [(val t).+1]. *)
Lemma val_turn_inj (t : 'I_n) : val (turn_inj t) = (val t).+1.
Proof. by rewrite /turn_inj /= /bump /= add1n. Qed.

(** [turn_inj] is injective. *)
Lemma turn_inj_inj : injective turn_inj.
Proof.
move=> a b /(congr1 val); rewrite !val_turn_inj => /succn_inj.
exact: val_inj.
Qed.

(** [turn_witness s] is the explicit alternating-subseq witness:
    [{ord0; ord_max} ∪ {turn_inj t | t turning point of s}].  Has
    cardinality [(turn_count s).+2]; its [pick_seq] is the alternating
    subsequence of length [(turn_count s).+2]. *)
Definition turn_witness s : {set 'I_n.+2} :=
  ord0 |: (ord_max |: [set turn_inj t | t in [set i : 'I_n | is_turn s i]]).

(** Image of [turn_inj] on the turn set has cardinality [turn_count s]. *)
Lemma card_turn_image s :
  #|[set turn_inj t | t in [set i : 'I_n | is_turn s i]]| = turn_count s.
Proof. by rewrite card_imset //; apply: turn_inj_inj. Qed.

(** Range bound: any element of the [turn_inj]-image of the turn set
    has [0 < val x <= n]; in particular, neither [ord0] nor [ord_max]. *)
Lemma turn_image_lt_max s (x : 'I_n.+2) :
  x \in [set turn_inj t | t in [set i : 'I_n | is_turn s i]] ->
  0 < val x <= n.
Proof.
case/imsetP => t _ ->.
rewrite val_turn_inj /=.
by have := ltn_ord t.
Qed.

(** [ord0] is not in the [turn_inj]-image of the turn set. *)
Lemma ord0_notin_turn_image s :
  (ord0 : 'I_n.+2) \notin [set turn_inj t | t in [set i : 'I_n | is_turn s i]].
Proof.
apply/negP => /turn_image_lt_max /andP [].
by rewrite (_ : val (ord0 : 'I_n.+2) = 0).
Qed.

(** [ord_max] is not in the [turn_inj]-image of the turn set. *)
Lemma ord_max_notin_turn_image s :
  (ord_max : 'I_n.+2) \notin
    [set turn_inj t | t in [set i : 'I_n | is_turn s i]].
Proof.
apply/negP => /turn_image_lt_max /andP [_].
rewrite (_ : val (ord_max : 'I_n.+2) = n.+1) //.
by rewrite ltnn.
Qed.

(** Trivial distinction: [ord0] and [ord_max] differ in [{'I_n.+2}]. *)
Lemma ord0_neq_ord_max : (ord0 : 'I_n.+2) != ord_max.
Proof. by rewrite -val_eqE /=. Qed.

(** Cardinality of the lower-bound witness set:
    [#|turn_witness s| = (turn_count s).+2]. *)
Lemma card_turn_witness s :
  #|turn_witness s| = (turn_count s).+2.
Proof.
rewrite /turn_witness.
rewrite cardsU1 in_setU1 (negbTE ord0_neq_ord_max) /=.
rewrite (negbTE (ord0_notin_turn_image s)) /=.
rewrite cardsU1 (negbTE (ord_max_notin_turn_image s)) /=.
by rewrite card_turn_image add1n add1n.
Qed.

(** Strict-left variant of [slot_descent_const]: hypothesis only excludes
    turns with witness STRICTLY greater than [val i].  Used in the
    lower-bound construction where [i] itself may be a turn position. *)
Lemma slot_descent_const_strict s (i j : 'I_n.+2) :
  (forall t : 'I_n, val i < (val t).+1 < val j -> ~~ is_turn s t) ->
  forall (k1 k2 : 'I_n.+1),
    val i <= val k1 -> val k1 <= val k2 -> val k2 < val j ->
    is_descent s k1 = is_descent s k2.
Proof.
move=> Hnoturn k1 k2 Hi1 H12 H2j.
move: H12 Hi1.
elim: (val k2 - val k1) {-2}k1 (refl_equal (val k2 - val k1)) =>
      [|d IH] k1' Hd H12 Hi1.
- move/eqP: Hd; rewrite subn_eq0 => Hk21.
  have : val k1' = val k2 by apply/eqP; rewrite eqn_leq H12 Hk21.
  by move=> /val_inj ->.
- have Hk1lt : val k1' < val k2 by rewrite -subn_gt0 Hd.
  have Hk1ord : val k1' < n.
    by have := ltn_ord k2; rewrite ltnS => Hk2; rewrite (leq_trans Hk1lt).
  pose t : 'I_n := Ordinal Hk1ord.
  have Ht : val i < (val t).+1 < val j.
    apply/andP; split; first by apply: leq_ltn_trans Hi1 _.
    by rewrite (leq_trans _ H2j).
  have := Hnoturn t Ht.
  rewrite /is_turn negb_add => /eqP Hd1.
  have Hk1eq : (widen_ord (leqnSn n) t : 'I_n.+1) = k1' by apply: val_inj.
  rewrite Hk1eq in Hd1; rewrite Hd1.
  have HSk1 : val (lift ord0 t : 'I_n.+1) = (val k1').+1
    by rewrite /= /bump /= add1n.
  apply: (IH (lift ord0 t)).
  - rewrite HSk1; apply: succn_inj.
    by rewrite subnSK // Hd.
  - by rewrite HSk1.
  - by rewrite HSk1 (leq_trans Hi1).
Qed.

(** Strict-left variant of [inter_turn_monotone]: monotone direction
    transport with a strict lower-bound hypothesis on turn witnesses. *)
Lemma inter_turn_monotone_strict s (i j : 'I_n.+2) :
  val i < val j ->
  (forall t : 'I_n, val i < (val t).+1 < val j -> ~~ is_turn s t) ->
  forall (p q : 'I_n.+2),
    val i <= val p -> val p < val q -> val q <= val j ->
    (val (s p) < val (s q))%N = (val (s i) < val (s j))%N.
Proof.
move=> Hij Hnoturn p q Hip Hpq Hqj.
have Hjle : val i < n.+1.
  by have := ltn_ord j; rewrite ltnS => Hj2; rewrite (leq_trans Hij).
pose k0 : 'I_n.+1 := Ordinal Hjle.
have Hk0range : val i <= val k0 < val j by rewrite /= leqnn /= Hij.
pose b := is_descent s k0.
have Hconst_ij : forall k : 'I_n.+1,
                   val i <= val k < val j -> is_descent s k = b.
  move=> k /andP [Hki Hkj].
  case: (leqP (val k0) (val k)) => Hkk0.
  - rewrite /b /=.
    by apply: esym; apply: (slot_descent_const_strict Hnoturn) => //=.
  - apply: (slot_descent_const_strict Hnoturn) => //=.
    exact: ltnW.
have Hconst_pq : forall k : 'I_n.+1,
                   val p <= val k < val q -> is_descent s k = b.
  move=> k /andP [Hkp Hkq].
  apply: Hconst_ij.
  by rewrite (leq_trans Hip Hkp) /= (leq_trans Hkq).
have Hmono_ij := constant_descent_monotone Hij Hconst_ij.
have Hmono_pq := constant_descent_monotone Hpq Hconst_pq.
case Eb : b Hmono_ij Hmono_pq => Hmono_ij Hmono_pq /=.
- rewrite ltnNge (ltnW Hmono_pq) /=.
  by rewrite ltnNge (ltnW Hmono_ij) /=.
- by rewrite Hmono_pq Hmono_ij.
Qed.

(** Direction LEFT of a turn witness: when [b = turn_inj t] and no
    interior turn lies in [(val a, val b)], the direction [s a] vs
    [s b] equals [~~ is_descent s (widen_ord t)] (the "left half"
    descent indicator at slot [t]). *)
Lemma dir_left_of_turn s (a b : 'I_n.+2) (t : 'I_n) :
  b = turn_inj t -> val a <= val t ->
  (forall t' : 'I_n, val a < (val t').+1 < val b -> ~~ is_turn s t') ->
  (val (s a) < val (s b))%N = ~~ is_descent s (widen_ord (leqnSn n) t).
Proof.
move=> Hbeq Hat Hno.
have Hbval : val b = (val t).+1 by rewrite Hbeq val_turn_inj.
(* Position p' = (val t) lifted to 'I_n.+2. *)
have Htlt2 : val t < n.+2 by rewrite (leq_trans (ltn_ord t)) //; apply: ltnW.
pose p' : 'I_n.+2 := Ordinal Htlt2.
have Hp'val : val p' = val t by [].
have Hap' : val a <= val p' by rewrite Hp'val.
have Hp'b : val p' < val b by rewrite Hp'val Hbval.
have Hbb : val b <= val b by [].
have Hab : val a < val b by rewrite (leq_ltn_trans Hap' Hp'b).
(* Use inter_turn_monotone_strict on (a, b) with sub-interval (p', b). *)
rewrite -(inter_turn_monotone_strict Hab Hno Hap' Hp'b Hbb).
(* Now compute direction at (p', b): position p' = val t and b = (val t).+1
   are adjacent, so the direction equals ~~ is_descent s (widen_ord t). *)
have Hwt : (widen_ord (leqnSn n.+1) (widen_ord (leqnSn n) t) : 'I_n.+2) = p'
  by apply: val_inj.
have Hlt : (lift ord0 (widen_ord (leqnSn n) t) : 'I_n.+2) = b
  by apply: val_inj => /=; rewrite Hbval /bump /= add1n.
have := not_is_descentE s (widen_ord (leqnSn n) t).
by rewrite Hwt Hlt => ->.
Qed.

(** Direction RIGHT of a turn witness: dual of [dir_left_of_turn]; the
    direction [s b] vs [s c] equals [~~ is_descent s (lift ord0 t)]
    (the "right half" descent indicator at slot [t]). *)
Lemma dir_right_of_turn s (b c : 'I_n.+2) (t : 'I_n) :
  b = turn_inj t -> val b < val c ->
  (forall t' : 'I_n, val b < (val t').+1 < val c -> ~~ is_turn s t') ->
  (val (s b) < val (s c))%N = ~~ is_descent s (lift ord0 t).
Proof.
move=> Hbeq Hbc Hno.
have Hbval : val b = (val t).+1 by rewrite Hbeq val_turn_inj.
(* Position c' = (val t).+2 lifted to 'I_n.+2. *)
have Htn : val t < n by apply: ltn_ord.
have HtSlt2 : (val t).+2 < n.+2 by rewrite !ltnS.
pose c' : 'I_n.+2 := Ordinal HtSlt2.
have Hc'val : val c' = (val t).+2 by [].
have Hbc' : val b < val c' by rewrite Hbval Hc'val.
have Hbb : val b <= val b by [].
have Hc'c : val c' <= val c.
  by rewrite Hc'val -Hbval.
(* Use inter_turn_monotone_strict on (b, c) with sub-interval (b, c'). *)
rewrite -(inter_turn_monotone_strict Hbc Hno Hbb Hbc' Hc'c).
(* Now compute direction at (b, c'): b = (val t).+1 and c' = (val t).+2,
   adjacent positions; direction equals ~~ is_descent s (lift ord0 t). *)
have Hwt : (widen_ord (leqnSn n.+1) (lift ord0 t) : 'I_n.+2) = b.
  by apply: val_inj => /=; rewrite Hbval /bump /= add1n.
have Hlt : (lift ord0 (lift ord0 t) : 'I_n.+2) = c'.
  by apply: val_inj => /=; rewrite /bump /= !add1n.
have := not_is_descentE s (lift ord0 t).
by rewrite Hwt Hlt => ->.
Qed.

(** Key adjacency lemma for the lower bound: at an interior witness
    [b = turn_inj t] flanked by neighbors [a, c] with no interior turns
    in the half-open intervals, the directions across [(a, b)] and [(b, c)]
    DIFFER (since [t] is a turning point).  Used in [triple_flip_pos_seq]
    to verify the alternating property of [pick_seq s (turn_witness s)]. *)
Lemma sign_flip_at_turn s (a b c : 'I_n.+2) (t : 'I_n) :
  is_turn s t -> b = turn_inj t ->
  val a <= val t -> val b < val c ->
  (forall t' : 'I_n, val a < (val t').+1 < val b -> ~~ is_turn s t') ->
  (forall t' : 'I_n, val b < (val t').+1 < val c -> ~~ is_turn s t') ->
  (val (s a) < val (s b))%N != (val (s b) < val (s c))%N.
Proof.
move=> Htn Hbeq Hat Hbc Hno_left Hno_right.
rewrite (dir_left_of_turn Hbeq Hat Hno_left).
rewrite (dir_right_of_turn Hbeq Hbc Hno_right).
move: Htn; rewrite /is_turn.
by case: (is_descent _ _); case: (is_descent _ _).
Qed.

End LowerBound.

(* ========================================================================= *)
(* §T. is_alt characterization via alternating sign_seq + distinctness        *)
(* ========================================================================= *)

(* Converse to sign_seq_is_alt: alternating signs (with adjacent distinctness)
   imply is_alt.  We need this so we can build is_alt from sign-flip data. *)

(** [uniq_adj xs] holds when every adjacent pair in [xs] consists of
    distinct elements.  Weaker than [uniq], used to characterize when
    [is_alt] follows from sign-seq alternation. *)
Definition uniq_adj (xs : seq nat) : bool :=
  match xs with
  | [::] => true
  | x :: xs' => all (fun p => p.1 != p.2) (zip (x :: xs') xs')
  end.

(** Cons reduction for [uniq_adj] on a 2-prefix. *)
Lemma uniq_adj_cons2 x y rest :
  uniq_adj (x :: y :: rest) = (x != y) && uniq_adj (y :: rest).
Proof. by rewrite /= eqE. Qed.

(** Tail closure of [uniq_adj]. *)
Lemma uniq_adj_tail x y rest :
  uniq_adj (x :: y :: rest) -> uniq_adj (y :: rest).
Proof. by case: rest => [|z r] /= /andP []. Qed.

(** Head distinctness extracted from [uniq_adj]. *)
Lemma uniq_adj_head_neq x y rest :
  uniq_adj (x :: y :: rest) -> x != y.
Proof. by case: rest => [|z r] /= /andP []. Qed.

(** For distinct nats, [x < y] iff [~~ (y < x)]; trichotomy in
    boolean form. *)
Lemma sign_pair_neq (x y : nat) : x != y -> (x < y)%N = ~~ (y < x)%N.
Proof.
move=> Hne; case Hxy : (x < y)%N.
  by rewrite ltnNge ltnW.
move/negbT: Hxy; rewrite -leqNgt leq_eqVlt => /orP [/eqP Hxy|->] //.
by rewrite Hxy eq_refl in Hne.
Qed.

(** Key reverse direction: an alternating boolean sign seq plus adjacent
    distinctness implies the [alt_aux] predicate.  Building block for
    [is_alt_from_sign]. *)
Lemma alt_aux_from_sign x y xs :
  uniq_adj (x :: y :: xs) ->
  is_alt_bool (sign_seq (x :: y :: xs)) ->
  alt_aux (~~ (x < y)%N) y xs.
Proof.
elim: xs y x => [|z rest IH] y x /=.
  by [].
move=> Hu Hab.
have Hyz_ne : y != z by case/and3P: Hu.
have Huyz : uniq_adj (y :: z :: rest).
  by case: rest Hu {IH Hab} => [|w r] /=; case/and3P=> _ Hyz Hr; rewrite Hyz //=.
move: Hab => /=.
case/andP=> Hflip Hbabool.
have Hrec : alt_aux (~~ (y < z)%N) z rest by exact: IH.
move: Hrec.
have Hxy_yz : (x < y)%N (+) (y < z)%N by exact: Hflip.
case Exy : (x < y)%N Hxy_yz => Hxy_yz /=.
- have Hyz_false : (y < z)%N = false by case: (y < z)%N Hxy_yz.
  rewrite Hyz_false /= => ->.
  by rewrite andbT ltn_neqAle leqNgt Hyz_false /= eq_sym Hyz_ne.
- have Hyz_true : (y < z)%N = true by case: (y < z)%N Hxy_yz.
  by rewrite Hyz_true /= => ->.
Qed.

(** Triple-flip sufficient condition for sign-seq alternation: if every
    adjacent triple [(js[i], js[i+1], js[i+2])] has flipping
    [s]-direction, then the sign seq of the [s]-image is alternating
    as a boolean seq. *)
Lemma sign_seq_alt_of_triple_flip n (s : {perm 'I_n.+2}) (js : seq 'I_n.+2) :
  (forall i, i.+2 < size js ->
     (val (s (nth ord0 js i)) < val (s (nth ord0 js i.+1)))%N
       != (val (s (nth ord0 js i.+1)) < val (s (nth ord0 js i.+2)))%N) ->
  is_alt_bool (sign_seq [seq val (s j) | j <- js]).
Proof.
elim: js => [|x [|y [|z rest]]] // IH Htriples /=.
have Hrec_hyp : forall i, i.+2 < size [:: y, z & rest] ->
  (val (s (nth ord0 [:: y, z & rest] i))
     < val (s (nth ord0 [:: y, z & rest] i.+1)))%N
     != (val (s (nth ord0 [:: y, z & rest] i.+1))
            < val (s (nth ord0 [:: y, z & rest] i.+2)))%N.
  by move=> i Hi; apply: (Htriples i.+1).
have Hrec := IH Hrec_hyp.
move: Hrec; rewrite /sign_seq /=.
move=> Hrec.
apply/andP; split; last exact: Hrec.
have H0 : 2 < size [:: x, y, z & rest] by [].
have := Htriples 0%N H0; rewrite /=.
by case: (val (s x) < _)%N; case: (val (s y) < _)%N.
Qed.

(** [uniq_adj] follows from full [uniq] for nat seqs. *)
Lemma uniq_adj_of_uniq (xs : seq nat) : uniq xs -> uniq_adj xs.
Proof.
case: xs => [|x xs] //=.
elim: xs x => [|y rest IH] x //= /andP [Hx /andP [Hy Hu]].
have Hxy : x != y by apply: contraNneq Hx => ->; rewrite mem_head.
rewrite Hxy /=.
by apply: IH; rewrite Hy Hu.
Qed.

(** Main reverse characterization: [is_alt xs] follows from
    [is_alt_bool (sign_seq xs)] together with adjacent distinctness.
    Used to construct alternating subseqs from sign-flip witnesses. *)
Lemma is_alt_from_sign xs :
  uniq_adj xs -> is_alt_bool (sign_seq xs) -> is_alt xs.
Proof.
case: xs => [|x [|y rest]] // Hu Hab.
have Hxy_ne : x != y by exact: uniq_adj_head_neq Hu.
rewrite is_alt_cons2.
have Hrec := alt_aux_from_sign Hu Hab.
case Exy : (x < y)%N Hrec => /= Hrec.
  by rewrite Hrec.
by rewrite Hrec andbT ltn_neqAle leqNgt Exy /= eq_sym Hxy_ne.
Qed.

(* ========================================================================= *)
(* §U. Existence of an alternating subsequence of length turn_count + 2     *)
(* ========================================================================= *)

Section ExistenceLB.
Variable n : nat.
Implicit Types (s : {perm 'I_n.+2}).

(** [pos_seq s] is the [turn_witness s] enumerated in ascending [val]
    order: the sorted seq of position indices in the lower-bound
    witness construction. *)
Definition pos_seq s : seq 'I_n.+2 :=
  sort (fun a b : 'I_n.+2 => val a <= val b) (enum (turn_witness s)).

(** [pos_seq s] has length [(turn_count s).+2]. *)
Lemma size_pos_seq s : size (pos_seq s) = (turn_count s).+2.
Proof. by rewrite /pos_seq size_sort -cardE card_turn_witness. Qed.

(** [pos_seq s] is duplicate-free. *)
Lemma pos_seq_uniq s : uniq (pos_seq s).
Proof. by rewrite /pos_seq sort_uniq enum_uniq. Qed.

(** Definitional unfolding: [pick_seq s (turn_witness s)] equals the
    map of [pos_seq s] under [val (s _)]. *)
Lemma pick_seq_pos_seq s :
  pick_seq s (turn_witness s) = [seq val (s j) | j <- pos_seq s].
Proof. by []. Qed.

(** [pos_seq s] is strictly sorted by [val]. *)
Lemma pos_seq_strict_sorted s :
  sorted (fun a b : 'I_n.+2 => val a < val b) (pos_seq s).
Proof. exact: sort_enum_strict_sorted. Qed.

(** Membership transfer: [x \in pos_seq s] iff [x \in turn_witness s]. *)
Lemma mem_pos_seq s (x : 'I_n.+2) :
  x \in pos_seq s = (x \in turn_witness s).
Proof. by rewrite /pos_seq mem_sort mem_enum. Qed.

(** Strict-sorted property: index-order in [pos_seq s] matches
    [val]-order. *)
Lemma pos_seq_val_lt s (i j : nat) :
  i < size (pos_seq s) -> j < size (pos_seq s) -> i < j ->
  val (nth ord0 (pos_seq s) i) < val (nth ord0 (pos_seq s) j).
Proof.
move=> Hi Hj Hij.
have Htrans : transitive (fun a b : 'I_n.+2 => val a < val b).
  by move=> a b c; apply: ltn_trans.
exact: (sorted_ltn_nth Htrans ord0 (pos_seq_strict_sorted s)).
Qed.

(** Converse strict-sorted property: [val]-order forces index-order
    in [pos_seq s]. *)
Lemma pos_seq_val_lt_inv s (i j : nat) :
  i < size (pos_seq s) -> j < size (pos_seq s) ->
  val (nth ord0 (pos_seq s) i) < val (nth ord0 (pos_seq s) j) ->
  i < j.
Proof.
move=> Hi Hj Hlt.
case: (ltngtP i j) Hlt => // Hij Hlt.
  by have := pos_seq_val_lt Hj Hi Hij; rewrite ltnNge ltnW.
by rewrite Hij ltnn in Hlt.
Qed.

(** Gap property: no element of [pos_seq s] has [val] strictly between
    consecutive entries [pos_seq s i] and [pos_seq s i.+1]. *)
Lemma no_inner_in_pos_seq s i (x : 'I_n.+2) :
  i.+1 < size (pos_seq s) ->
  x \in pos_seq s ->
  val (nth ord0 (pos_seq s) i) < val x ->
  val x < val (nth ord0 (pos_seq s) i.+1) ->
  False.
Proof.
move=> Hi Hin Hxa Hxb.
have Hi0 : i < size (pos_seq s) by exact: ltnW.
have /(nthP ord0) [j Hj Hxnth] := Hin.
rewrite -Hxnth in Hxa Hxb.
have H1 := pos_seq_val_lt_inv Hi0 Hj Hxa.
have H2 := pos_seq_val_lt_inv Hj Hi Hxb.
by have := leq_trans H2 H1; rewrite ltnn.
Qed.

(** First element of [pos_seq s] is [ord0]. *)
Lemma pos_seq_nth0 s : nth ord0 (pos_seq s) 0 = ord0.
Proof.
have Hsz : 0 < size (pos_seq s) by rewrite size_pos_seq.
have Hord0_in : (ord0 : 'I_n.+2) \in pos_seq s.
  by rewrite mem_pos_seq /turn_witness !inE eq_refl.
have /(nthP ord0) [k Hk Hk_eq] := Hord0_in.
case Ek : k Hk Hk_eq => [|k'] Hk Hk_eq.
  by [].
have Hk0lt : (0 < k'.+1)%N by [].
have := pos_seq_val_lt Hsz Hk Hk0lt.
rewrite Hk_eq /=.
by [].
Qed.

(** Last element of [pos_seq s] has value [n.+1] (i.e., is [ord_max]). *)
Lemma pos_seq_last_val s :
  val (nth ord0 (pos_seq s) (turn_count s).+1) = n.+1.
Proof.
have Hszm1 : (turn_count s).+1 < size (pos_seq s) by rewrite size_pos_seq.
have Hord_max_in : (ord_max : 'I_n.+2) \in pos_seq s.
  by rewrite mem_pos_seq /turn_witness !inE eq_refl orbT.
have /(nthP ord0) [k Hk Hk_eq] := Hord_max_in.
have Hk_le : k <= (turn_count s).+1.
  rewrite leqNgt; apply/negP => Hk_gt.
  have Hsz_eq : size (pos_seq s) = (turn_count s).+2 by rewrite size_pos_seq.
  by have := Hk; rewrite Hsz_eq ltnS leqNgt Hk_gt.
case: (eqVneq k (turn_count s).+1) => [Heq|Hne].
  by rewrite -Heq Hk_eq.
have Hk_lt : k < (turn_count s).+1 by rewrite ltn_neqAle Hne.
have := pos_seq_val_lt Hk Hszm1 Hk_lt.
rewrite Hk_eq /= => Hcontr.
have Hbound : val (nth ord0 (pos_seq s) (turn_count s).+1) < n.+2 by exact: ltn_ord.
by apply/eqP; rewrite eqn_leq; apply/andP; split;
  [have := Hbound; rewrite ltnS | apply: ltnW].
Qed.

(** Interior elements of [pos_seq s] (indices [0 < i < size - 1]) are
    [turn_inj]-images of turning points: they correspond to actual
    turns of [s]. *)
Lemma interior_is_turn_inj s (i : nat) :
  0 < i -> i.+1 < size (pos_seq s) ->
  exists t : 'I_n, is_turn s t /\ nth ord0 (pos_seq s) i = turn_inj t.
Proof.
move=> H0 Hi.
have Hi0 : i < size (pos_seq s) by exact: ltnW.
pose b := nth ord0 (pos_seq s) i.
have Hbin : b \in pos_seq s by apply: mem_nth.
rewrite mem_pos_seq /turn_witness !inE in Hbin.
case/orP: Hbin => [/eqP Hb_ord0|].
  exfalso.
  have Hsz_pos : 0 < size (pos_seq s) by rewrite size_pos_seq.
  have := pos_seq_val_lt Hsz_pos Hi0 H0.
  by rewrite pos_seq_nth0 -/b Hb_ord0.
case/orP => [/eqP Hb_ord_max|].
  exfalso.
  have Hsz_eq : size (pos_seq s) = (turn_count s).+2 by rewrite size_pos_seq.
  have Hi_lt : i < (turn_count s).+1 by have := Hi; rewrite Hsz_eq.
  have Hszm1 : (turn_count s).+1 < size (pos_seq s) by rewrite Hsz_eq.
  have := pos_seq_val_lt Hi0 Hszm1 Hi_lt.
  rewrite -/b Hb_ord_max pos_seq_last_val.
  by rewrite ltnn.
case/imsetP => t Hin Heq.
exists t; split.
  by move: Hin; rewrite inE.
by [].
Qed.

(** Strict interior value bounds: [0 < val (pos_seq s i) < n.+1] for
    indices [i] strictly between the endpoints. *)
Lemma interior_val_bounds s i :
  0 < i -> i.+1 < size (pos_seq s) ->
  0 < val (nth ord0 (pos_seq s) i) /\
  val (nth ord0 (pos_seq s) i) < n.+1.
Proof.
move=> H0 Hi.
have Hi0 : i < size (pos_seq s) by exact: ltnW.
have [t [Ht Heq]] := interior_is_turn_inj H0 Hi.
rewrite Heq val_turn_inj.
split; first by [].
by have := ltn_ord t.
Qed.

(** Triple-flip property for adjacent triples in [pos_seq s]: directions
    across consecutive [s]-comparisons differ.  The interior witness in
    each triple is a turning point, so [sign_flip_at_turn] applies. *)
Lemma triple_flip_pos_seq s i :
  i.+2 < size (pos_seq s) ->
  (val (s (nth ord0 (pos_seq s) i)) < val (s (nth ord0 (pos_seq s) i.+1)))%N
    != (val (s (nth ord0 (pos_seq s) i.+1)) < val (s (nth ord0 (pos_seq s) i.+2)))%N.
Proof.
move=> Hi.
have Hi1 : i.+1 < size (pos_seq s) by exact: ltnW.
have Hi0 : i < size (pos_seq s) by do 2 apply: ltnW.
pose a := nth ord0 (pos_seq s) i.
pose b := nth ord0 (pos_seq s) i.+1.
pose c := nth ord0 (pos_seq s) i.+2.
have Hab : val a < val b by exact: pos_seq_val_lt.
have Hbc : val b < val c by exact: pos_seq_val_lt.
have [t [Htn Heqb]] := interior_is_turn_inj (i := i.+1) (ltn0Sn _) Hi.
have Hbeq : b = turn_inj t by [].
have Hbval : val b = (val t).+1 by rewrite Hbeq val_turn_inj.
have Hat : val a <= val t.
  by rewrite -ltnS -Hbval.
(* No turns in (val a, val b). *)
have Hno_left : forall t' : 'I_n, val a < (val t').+1 < val b -> ~~ is_turn s t'.
  move=> t' /andP [Ht1 Ht2].
  apply/negP => Ht'turn.
  pose x := turn_inj t'.
  have Hxin : x \in pos_seq s.
    rewrite mem_pos_seq /turn_witness !inE.
    apply/orP; right; apply/orP; right.
    apply/imsetP; exists t' => //.
    by rewrite inE.
  have Hxa : val a < val x by rewrite val_turn_inj.
  have Hxb : val x < val b by rewrite val_turn_inj.
  exact: (no_inner_in_pos_seq Hi1 Hxin Hxa Hxb).
(* No turns in (val b, val c). *)
have Hno_right : forall t' : 'I_n, val b < (val t').+1 < val c -> ~~ is_turn s t'.
  move=> t' /andP [Ht1 Ht2].
  apply/negP => Ht'turn.
  pose x := turn_inj t'.
  have Hxin : x \in pos_seq s.
    rewrite mem_pos_seq /turn_witness !inE.
    apply/orP; right; apply/orP; right.
    apply/imsetP; exists t' => //.
    by rewrite inE.
  have Hxb : val b < val x by rewrite val_turn_inj.
  have Hxc : val x < val c by rewrite val_turn_inj.
  exact: (no_inner_in_pos_seq Hi Hxin Hxb Hxc).
exact: (sign_flip_at_turn Htn Heqb Hat Hbc Hno_left Hno_right).
Qed.

(** Witness alternation: [pick_seq s (turn_witness s)] is alternating.
    Combines [triple_flip_pos_seq] with the sign-seq characterization
    of [is_alt]. *)
Theorem is_alt_pick_turn_witness s :
  is_alt (pick_seq s (turn_witness s)).
Proof.
rewrite pick_seq_pos_seq.
apply: is_alt_from_sign.
  apply: uniq_adj_of_uniq.
  rewrite map_inj_in_uniq.
    exact: pos_seq_uniq.
  by move=> x y _ _ /val_inj /perm_inj.
apply: sign_seq_alt_of_triple_flip.
exact: triple_flip_pos_seq.
Qed.

(** Headline lower bound for [as_perm_max]:
    [(turn_count s).+2 <= as_perm_max s].  Witnessed by [turn_witness s],
    which has [(turn_count s).+2] elements and induces an alternating
    [pick_seq] (Stanley §1.6.2). *)
Theorem as_perm_max_lower s : (turn_count s).+2 <= as_perm_max s.
Proof.
rewrite -card_turn_witness.
rewrite /as_perm_max.
exact: (leq_bigmax_cond (turn_witness s) (is_alt_pick_turn_witness s)).
Qed.

End ExistenceLB.

(* ========================================================================= *)
(* §V. Upper bound: as_perm_max s <= (turn_count s).+2                        *)
(* ========================================================================= *)

(* Step 3: pick_seq is a subseq of perm_seq (as nat seqs).                    *)
Section UpperBoundChain.
Variable n : nat.
Implicit Types (s : {perm 'I_n.+2}).

(** Sorted enumeration of a subset is a subseq of the sorted full
    enumeration: [sort by val (enum I)] is a subseq of [enum 'I_n.+2]. *)
Lemma sort_enum_subseq_enum (I : {set 'I_n.+2}) :
  subseq (sort (fun a b : 'I_n.+2 => val a <= val b) (enum I)) (enum 'I_n.+2).
Proof.
have Hle_total : total (fun a b : 'I_n.+2 => val a <= val b).
  by move=> a b; apply: leq_total.
have Hle_trans : transitive (fun a b : 'I_n.+2 => val a <= val b).
  by move=> a b c; apply: leq_trans.
have Hsub_enumI : subseq (enum I) (enum 'I_n.+2).
  rewrite enumT /enum_mem.
  exact: filter_subseq.
have Hsorted : sorted (fun a b : 'I_n.+2 => val a <= val b) (enum 'I_n.+2).
  exact: sorted_val_enum_ord.
have Hsort_enum : sort (fun a b : 'I_n.+2 => val a <= val b) (enum 'I_n.+2) =
                  enum 'I_n.+2.
  exact: (sorted_sort Hle_trans Hsorted).
rewrite -Hsort_enum.
apply: (subseq_sort Hle_total Hle_trans).
exact: Hsub_enumI.
Qed.

(** [pick_seq s I] is a subseq of [perm_seq s] for any position set [I]. *)
Lemma pick_seq_subseq_perm_seq s (I : {set 'I_n.+2}) :
  subseq (pick_seq s I) (perm_seq s).
Proof.
rewrite /pick_seq /perm_seq.
exact: map_subseq (sort_enum_subseq_enum I).
Qed.

(** Flip-count comparison for [pick_seq] vs [perm_seq]: any pick has
    [flip_count] at most that of the full perm seq. *)
Lemma flip_count_pick_le_perm s (I : {set 'I_n.+2}) :
  flip_count (sign_seq (pick_seq s I)) <= flip_count (sign_seq (perm_seq s)).
Proof.
exact: flip_count_sign_seq_le_subseq (pick_seq_subseq_perm_seq s I).
Qed.

(* Step 4: flip_count of sign_seq of perm_seq equals turn_count.              *)

(** [flip_count] expressed as an indexed sum of consecutive XOR-pairs.
    Used to align with the [turn_count] sum over [is_turn]. *)
Lemma flip_count_as_sum (xs : seq bool) :
  flip_count xs = \sum_(0 <= i < (size xs).-1) (nth false xs i (+) nth false xs i.+1).
Proof.
case: xs => [|x xs] /=.
  by rewrite /flip_count /= big_nil.
rewrite /flip_count /=.
rewrite (big_nth false) size_pairmap.
apply: eq_big_nat => i Hi.
have Hi' : i < size xs by case/andP: Hi.
rewrite (nth_pairmap x) //.
case: i Hi' {Hi} => [|i] Hi' //=.
- by rewrite (@set_nth_default _ _ false x).
- rewrite (@set_nth_default _ _ false x i (ltnW Hi')).
  by rewrite (@set_nth_default _ _ false x i.+1 Hi').
Qed.

(** XOR is invariant under double negation: [~~ a (+) ~~ b = a (+) b]. *)
Lemma neg_add_neg (a b : bool) : ~~ a (+) ~~ b = a (+) b.
Proof. by case: a; case: b. Qed.

(** Bridge identity: [flip_count (sign_seq (perm_seq s)) = turn_count s].
    The seq-level flip count of the full word equals the perm-level turn
    count, via [sign_seq_perm_seq] and the descent-XOR characterization
    of [is_turn]. *)
Lemma flip_count_perm_seq_eq_turn_count s :
  flip_count (sign_seq (perm_seq s)) = turn_count s.
Proof.
rewrite sign_seq_perm_seq flip_count_as_sum.
rewrite size_map size_enum_ord /=.
under eq_big_nat => i Hi.
  have Hi1 : i < n.+1 by case/andP: Hi => _; apply: ltnW.
  have Hi2 : i.+1 < n.+1 by case/andP: Hi.
  rewrite (nth_map ord0); last by rewrite size_enum_ord.
  rewrite (nth_map ord0); last by rewrite size_enum_ord.
  rewrite neg_add_neg.
  over.
rewrite big_mkord.
have Hsum_eq : forall i : 'I_n,
    is_descent s (nth ord0 (enum 'I_n.+1) i)
      (+) is_descent s (nth ord0 (enum 'I_n.+1) i.+1) = is_turn s i.
  move=> i.
  have Heq1 : (nth ord0 (enum 'I_n.+1) i : 'I_n.+1) = widen_ord (leqnSn n) i.
    by apply: val_inj => /=; rewrite nth_enum_ord //; apply: ltnW; apply: ltn_ord.
  have Heq2 : (nth ord0 (enum 'I_n.+1) i.+1 : 'I_n.+1) = lift ord0 i.
    apply: val_inj => /=.
    rewrite nth_enum_ord /=. by rewrite /bump /= add1n.
    by apply: ltn_ord.
  by rewrite Heq1 Heq2.
under eq_bigr => i _ do rewrite Hsum_eq.
rewrite /turn_count -sum1_card.
rewrite [in RHS]big_mkcond.
apply: eq_bigr => i _.
rewrite inE.
by case: (is_turn s i).
Qed.

(** Headline upper bound for [as_perm_max]:
    [as_perm_max s <= (turn_count s).+2].  Combines the alternating
    [flip_count] formula [is_alt_flip_count] with the subseq monotonicity
    [flip_count_pick_le_perm] and the bridge
    [flip_count_perm_seq_eq_turn_count]. *)
Lemma as_perm_max_upper s : as_perm_max s <= (turn_count s).+2.
Proof.
rewrite /as_perm_max.
apply/bigmax_leqP => I HI.
case Hsize : (#|I| <= 1).
  by rewrite (leq_trans Hsize).
move/negbT: Hsize; rewrite -ltnNge => Hsize2.
have Hps_size : size (pick_seq s I) = #|I|.
  by rewrite /pick_seq size_map size_sort -cardE.
have Hsz_ge2 : 2 <= size (pick_seq s I) by rewrite Hps_size.
have Halt_fc := is_alt_flip_count HI Hsz_ge2.
rewrite Hps_size in Halt_fc.
have Hbound : (#|I|).-2 <= turn_count s.
  rewrite -Halt_fc -flip_count_perm_seq_eq_turn_count.
  exact: flip_count_pick_le_perm.
by case Hcard : #|I| Hsize2 Hbound => [|[|m]] // _ _.
Qed.

(** HEADLINE THEOREM (Stanley §1.6.2): the longest alternating
    subsequence count of [s : {perm 'I_n.+2}] equals [(turn_count s).+2].
    That is, [as(w) = (turn_count w).+2], proving the two definitions
    [as_perm_max] (bijective max) and [as_perm] (turn count) coincide.
    Combines [as_perm_max_upper] and [as_perm_max_lower]. *)
Theorem as_perm_max_eq s : as_perm_max s = (turn_count s).+2.
Proof.
apply: anti_leq.
apply/andP; split.
- exact: as_perm_max_upper.
- exact: as_perm_max_lower.
Qed.

End UpperBoundChain.

