(* mmtree.v — Milestone 1 of the cd-index route.

   Stanley EC1 (2nd ed.) §1.6.3 defines, for a sequence w = a_1 … a_n of
   distinct integers, the *min-max tree* M(w) as follows:
     - let j be the least index such that a_j is either the minimum or
       maximum of {a_1, …, a_n};
     - a_j becomes the root, with M(a_1, …, a_{j-1}) as its left subtree
       and M(a_{j+1}, …, a_n) as its right subtree.

   This file delivers Milestone 1 as specified in
   docs/internal/AXIOMS_TODO.md §4:
     - a `mmtree` inductive for labelled binary trees;
     - `mmtree_of_seq` implementing the construction;
     - `mmtree_to_seq` : in-order traversal;
     - `mmtree_of_seqK` : in-order traversal round-trips the
       construction (ordinary list equality, NO artificial leaf-marker
       interleaving).

   Design choice (docs/internal/AXIOMS_TODO.md §4 row 1, "Notes"):
   For Milestone 1 we only need the *round-trip*, so we pick ONE
   consistent rule at every recursive step: split at the index of the
   *minimum* element of the current sub-sequence.  The full alternating
   min/max rule needed for the ψᵢ operators is deferred to Milestone 2.

   We work with `nat` labels for concreteness and computability.  The
   round-trip theorem does not require distinct labels: `index` picks
   the least occurrence, which is a consistent well-defined choice. *)

From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section MMTree.

(** [mmtree T] is the labelled binary tree datatype underlying Stanley's
    min-max tree construction [M(w)] for sequences with labels in [T]. *)
Inductive mmtree (T : Type) : Type :=
  | Leaf : mmtree T
  | Node : mmtree T -> T -> mmtree T -> mmtree T.

Arguments Leaf {T}.
Arguments Node {T} _ _ _.

(** [mmtree_to_seq t] is the in-order traversal of [t]: left subtree, then
    root, then right subtree. *)
Fixpoint mmtree_to_seq {T : Type} (t : mmtree T) : seq T :=
  match t with
  | Leaf => [::]
  | Node l x r => mmtree_to_seq l ++ x :: mmtree_to_seq r
  end.

(** [min_pos s] is the least index [j] in [s] at which the minimum of [s]
    occurs; returns 0 on the empty sequence (vacuous case). *)
Definition min_pos (s : seq nat) : nat :=
  index (foldr minn (head 0 s) (behead s)) s.

(** [min_in] states that [foldr minn a s] always lies in the sequence
    [a :: s]; used to bound [min_pos] within range. *)
Lemma min_in s a : foldr minn a s \in a :: s.
Proof.
elim: s a => [| b s IH] a /=.
  by rewrite inE eqxx.
(* foldr minn a (b :: s) = minn b (foldr minn a s).  `leqP` rewrites `minn`   *)
(* automatically to either argument depending on the branch.                  *)
rewrite !inE.
case: leqP => _; first by rewrite eqxx orbT.
have := IH a; rewrite inE => /orP [->|->] //; by rewrite !orbT.
Qed.

(** [min_pos_lt] : on a nonempty sequence the split index [min_pos s] is in
    range, ensuring the recursion in [mmtree_of_seq_fuel] is well-defined. *)
Lemma min_pos_lt s : s <> [::] -> min_pos s < size s.
Proof.
case: s => [// | a s _]; rewrite /min_pos.
have -> : head 0 (a :: s) = a by [].
have -> : behead (a :: s) = s by [].
by rewrite index_mem; exact: min_in.
Qed.

(** [mmtree_of_seq_fuel fuel s] is the fuel-bounded M1 tree construction:
    splits [s] at [min_pos s], recursing on the take/drop halves.  Fuel
    equal to [size s] suffices since each recursion strictly shrinks. *)
Fixpoint mmtree_of_seq_fuel (fuel : nat) (s : seq nat) : mmtree nat :=
  match fuel with
  | 0 => Leaf
  | fuel'.+1 =>
      match s with
      | [::] => Leaf
      | _ :: _ =>
          let j := min_pos s in
          Node (mmtree_of_seq_fuel fuel' (take j s))
               (nth 0 s j)
               (mmtree_of_seq_fuel fuel' (drop j.+1 s))
      end
  end.

(** [mmtree_of_seq s] runs [mmtree_of_seq_fuel] with fuel [size s], the
    M1 (minimum-only) variant of Stanley's min-max tree construction. *)
Definition mmtree_of_seq (s : seq nat) : mmtree nat :=
  mmtree_of_seq_fuel (size s) s.

(** [mmtree_of_seq_fuel_correct] : the fuel-bounded construction round-trips
    in-order, i.e. [mmtree_to_seq] inverts [mmtree_of_seq_fuel] when fuel
    bounds the sequence size. *)
Lemma mmtree_of_seq_fuel_correct :
  forall fuel s, size s <= fuel ->
    mmtree_to_seq (mmtree_of_seq_fuel fuel s) = s.
Proof.
elim => [| fuel IH] s.
  by rewrite leqn0 => /nilP ->.
case: s => [// | a s Hsz] /=.
set s0 := a :: s in Hsz *.
have Hs0 : s0 <> [::] by [].
have Hj : min_pos s0 < size s0 by apply: min_pos_lt.
(* size of left part: min_pos s0 <= fuel *)
have Hleft : size (take (min_pos s0) s0) <= fuel.
  rewrite size_take Hj.
  by rewrite -ltnS; apply: (leq_trans Hj).
(* size of right part: size s0 - (min_pos s0).+1 <= fuel *)
have Hright : size (drop (min_pos s0).+1 s0) <= fuel.
  rewrite size_drop.
  have : size s0 <= fuel.+1 by [].
  move: Hj; case: (size s0) => // k Hk Hk1.
  by rewrite subSS; apply: (leq_trans (leq_subr _ _)).
rewrite (IH _ Hleft) (IH _ Hright).
(* Conclude by cat_take_drop and nth/drop. *)
rewrite -[RHS](cat_take_drop (min_pos s0) s0).
congr (_ ++ _).
by rewrite (drop_nth 0 Hj).
Qed.

(** [mmtree_of_seqK] is the M1 round-trip theorem: in-order traversal
    inverts [mmtree_of_seq] for every input sequence. *)
Theorem mmtree_of_seqK : forall s, mmtree_to_seq (mmtree_of_seq s) = s.
Proof.
move=> s; rewrite /mmtree_of_seq; apply: mmtree_of_seq_fuel_correct.
exact: leqnn.
Qed.

(* --- Non-triviality example
       (docs/internal/AXIOMS_TODO.md §5, item 1 & §4 constraint) ---
   Concrete sequence from the brief. *)

(** [ex_seq] is the concrete test sequence used to demonstrate that the
    construction yields a genuinely branching tree. *)
Definition ex_seq := [:: 3; 1; 4; 1; 5; 9; 2; 6].

(** [ex_nontrivial] checks that [mmtree_of_seq ex_seq] is genuinely
    branching (not a leaf and not a chain). *)
Example ex_nontrivial :
  match mmtree_of_seq ex_seq with
  | Leaf => false
  | Node Leaf _ _ => false
  | Node _ _ Leaf => false
  | _ => true
  end = true.
Proof. by []. Qed.

(** [ex_roundtrip] is the round-trip [mmtree_of_seqK] applied to [ex_seq]. *)
Example ex_roundtrip :
  mmtree_to_seq (mmtree_of_seq ex_seq) = ex_seq.
Proof. exact: mmtree_of_seqK. Qed.

(** [ex_roundtrip_compute] is the boolean version of [ex_roundtrip],
    verifying that [Compute] reduces the round-trip to [true]. *)
Example ex_roundtrip_compute :
  (mmtree_to_seq (mmtree_of_seq ex_seq) == ex_seq) = true.
Proof. by []. Qed.

End MMTree.
