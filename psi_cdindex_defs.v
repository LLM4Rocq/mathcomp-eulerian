(* psi_cdindex_defs.v — Definitions and simple lemmas for cd-index            *)
(*                                                                           *)
(* Split from psi_cdindex_core.v to reduce -vo compilation memory.           *)
(* Contains: is_internal, apply_psis, char_mono, cde, classify_vertex_cde,   *)
(* phi_w, internal_vertices, expand_cde, powerset_internal, leq_seqb,        *)
(* and simple apply_psis lemmas.                                             *)

From mathcomp Require Import all_ssreflect.
Require Import mmtree psi_core psi_comm psi_descent_v2 psi_descent_thms.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

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
