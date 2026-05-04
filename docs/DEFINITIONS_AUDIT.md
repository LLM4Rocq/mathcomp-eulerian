# Definitions Audit — Stanley ↔ Rocq Side-by-Side

> **Purpose.** A definition-by-definition audit of the formal
> development against Stanley *Enumerative Combinatorics I* (EC1).
> Each entry gives Stanley's informal definition, the verbatim Rocq
> definition with its file:line, and a brief verdict on whether
> the translation is faithful.
>
> **Read the conventions first.** The single recurring shift is
> 0-indexing — see [`READING_GUIDE.md`](READING_GUIDE.md) §1-2 for
> the index/type translation table. In particular: our `{perm 'I_n.+1}`
> = Stanley's `S_{n+1}`, and our `eulerian n k` = Stanley's `A(n+1, k)`.

## How to use this document

Each entry has four parts:

1. **Stanley** — the informal definition as it appears in Stanley.
2. **Rocq** — the verbatim formal definition.
3. **Where** — file path and line number.
4. **Audit** — a 1-line verdict: ✓ matches Stanley, ⚠ matches Stanley
   modulo a noted convention, or ✗ if a discrepancy is suspected
   (none currently).

If you find a definition that doesn't match Stanley, or a convention
note that's missing, please file an issue or PR.

---

# §1.3.1 — Cycle representation

## Definition: `cycle_count`

**Stanley §1.3.1, p. 17:** For `w ∈ S_n`, write `w` as a product of
disjoint cycles. Then `c(w)` is the number of cycles.

**Rocq** (`cycles.v:24`):
```coq
Definition cycle_count {T : finType} (s : {perm T}) : nat := #|porbits s|.
```

**Audit:** ✓ `porbits s` is mathcomp's set of orbits of `s` under
iteration; for permutations these are exactly the cycles of the
disjoint-cycle decomposition. Cardinality matches Stanley's `c(w)`.

---

## Definition: `stirling_c` (signless Stirling cycle numbers)

**Stanley §1.3.2, p. 18:** `c(n, k)` is the number of permutations
of `[n]` with exactly `k` cycles. Stanley calls these the *signless
Stirling numbers of the first kind*.

**Rocq** (`cycles.v:33-34`):
```coq
Definition stirling_c (n k : nat) : nat :=
  #|[set s : {perm 'I_n} | cycle_count s == k]|.
```

**Audit:** ✓ Direct match. `'I_n` has cardinality `n`, so `{perm 'I_n}`
is permutations of `n` elements = Stanley's `S_n`. Counting those with
`cycle_count s = k` gives Stanley's `c(n, k)`.

**Note.** This is one of the few definitions where our parameter `n`
matches Stanley's `n` directly (no off-by-one).

---

# §1.3.3 — Inversions and the major index

## Definition: `is_inv` (inversion predicate)

**Stanley §1.3.3, p. 21:** A pair `(i, j)` is an inversion of `w` if
`i < j` and `w_i > w_j`.

**Rocq** (`inversions.v:26-27`):
```coq
Definition is_inv s (i j : 'I_n.+1) : bool :=
  (i < j) && (s j < s i).
```

**Where** `s : {perm 'I_n.+1}`, `i j : 'I_n.+1`.

**Audit:** ✓ Direct match. `(s j < s i)` is the same as `(s i > s j)`.

---

## Definition: `inv` (inversion count)

**Stanley §1.3.3:** `inv(w) = #{(i, j) : i < j, w_i > w_j}`.

**Rocq** (`inversions.v:30, 34`):
```coq
Definition inv_set s : {set 'I_n.+1 * 'I_n.+1} :=
  [set ij | is_inv s ij.1 ij.2].

Definition inv s : nat := #|inv_set s|.
```

**Audit:** ✓ Cardinality of the inversion set.

---

## Definition: `maj` (major index)

**Stanley §1.3.3, p. 21:** `maj(w) = ∑_{i ∈ D(w)} i`, summing
**1-indexed** descent positions.

**Rocq** (`inversions.v:81`):
```coq
Definition maj s : nat := \sum_(i in descent_set s) (val i).+1.
```

**Audit:** ⚠ Convention shift. Our `descent_set s : {set 'I_n}` has
**0-indexed** positions. The `(val i).+1` shifts each position by 1
to recover Stanley's 1-indexing. So `maj s = ∑_{i ∈ descent_set s} (i+1)`,
which matches Stanley after the 0→1 index shift.

**Sanity:** for `s = [3,1,4,2]` (Stanley) = `[2,0,3,1]` (us),
`descent_set s = {0, 2}`, `maj s = (0+1) + (2+1) = 4`, matches
Stanley's `maj = 1 + 3 = 4`.

---

## Definition: `coinv_set` (co-inversion set)

**Stanley §1.3.3:** Used implicitly. The "co-inversions" are pairs
`(i, j)` with `i < j` and `w_i < w_j`. Together with inversions, they
partition the `\binom{n}{2}` pairs.

**Rocq** (`inversions.v:169-170`):
```coq
Definition coinv_set s : {set 'I_n.+1 * 'I_n.+1} :=
  [set ij : 'I_n.+1 * 'I_n.+1 | (ij.1 < ij.2) && (s ij.1 < s ij.2)].
```

**Audit:** ✓ Direct match. Used in proofs of `inv + coinv = \binom{n+1}{2}`.

---

# §1.3.4 — Foata's first fundamental bijection

## Definition: `is_desc_seq` (seq-level descent)

**Stanley §1.3.4:** Position `k` is a descent of word `w` if `w_k > w_{k+1}`.

**Rocq** (`foata.v:88-89`):
```coq
Definition is_desc_seq (w : seq nat) (k : nat) : bool :=
  nth 0 w k > nth 0 w k.+1.
```

**Audit:** ✓ Direct seq-level definition; `nth 0 w k` is the `k`-th
element (default 0 when out of range; never used out of range in
proofs). 0-indexed.

---

## Definition: `maj_seq` (seq-level major index)

**Stanley §1.3.4:** Same as `maj` but on a word. `maj_seq w = ∑_{k ∈ D(w)} (k+1)`
where positions are 0-indexed and the `+1` recovers Stanley's 1-indexing.

**Rocq** (`foata.v:92-93`):
```coq
Definition maj_seq (w : seq nat) : nat :=
  \sum_(k <- iota 0 (size w).-1 | is_desc_seq w k) k.+1.
```

**Audit:** ✓ Same convention as `maj` on `{perm}`. The seq form is
equivalent: `inv_eq_inv_seq` and `maj_eq_maj_seq` (in `foata.v`)
prove the seq and perm versions agree.

---

## Definition: `inv_seq` (seq-level inversion count)

**Rocq** (`foata.v:96-98`):
```coq
Definition inv_seq (w : seq nat) : nat :=
  \sum_(j <- iota 0 (size w))
    \sum_(i <- iota 0 j | nth 0 w i > nth 0 w j) 1.
```

**Audit:** ✓ Counts pairs `(i, j)` with `i < j` and `w_i > w_j`.

---

## Definition: `foata_step` (the per-letter Foata step)

**Stanley §1.3.4, "second fundamental transformation":** For an
existing word `u` and a new letter `a`, split `u` into blocks based on
whether `last(u) < a` (split at letters `< a`) or `last(u) > a` (split
at letters `> a`); cyclically rotate each block (last → front);
concatenate; append `a`.

**Rocq** (`foata.v:70-77`):
```coq
Definition foata_step (a : nat) (u : seq nat) : seq nat :=
  match u with
  | [::] => [:: a]
  | _ :: _ =>
      let x := last 0 u in
      let P := if x < a then (fun y : nat => y < a) else (fun y => a < y) in
      flatten (map cyc_last_to_front (split_blocks P u)) ++ [:: a]
  end.
```

**Audit:** ✓ Direct implementation of Stanley's recursive step.
`split_blocks P u` splits at P-letters; `cyc_last_to_front` is the
cyclic rotation; `++ [:: a]` appends the new letter.

---

## Definition: `foata` (the bijection on words)

**Stanley §1.3.4:** Apply `foata_step` letter-by-letter, left to
right.

**Rocq** (`foata.v:80-81`):
```coq
Definition foata (w : seq nat) : seq nat :=
  foldl (fun u a => foata_step a u) [::] w.
```

**Audit:** ✓ Left-fold of `foata_step` starting from the empty word.

**Sanity:** `foata [3;1;4;5;9;2;6] = [3;4;1;5;2;9;6]` (Stanley's
running example, p. 23, computation in `foata.v:108-132`).

---

## Definition: `foata_perm` (Foata bijection on permutations)

**Stanley §1.3.4:** The seq-level Foata bijection lifted to permutations.

**Rocq** (`foata.v:1529-1531`):
```coq
Definition foata_perm (s : {perm 'I_n.+1}) : {perm 'I_n.+1} :=
  seq_to_perm (foata_perm_to_seq_size s) (foata_perm_to_seq_uniq s)
              (foata_perm_to_seq_bnd s).
```

**Audit:** ✓ Wraps the seq-level `foata` into the `{perm}` type via
`seq_to_perm` (a packaging that proves the seq is a permutation).
The headline result `inv_maj_equidistr` (MacMahon) follows.

---

# §1.4 — Descents and Eulerian numbers

## Definition: `is_descent`

**Stanley §1.4, p. 30:** Position `i ∈ {1, ..., n-1}` is a descent of
`w ∈ S_n` if `w_i > w_{i+1}`.

**Rocq** (`descent.v:22-23`):
```coq
Definition is_descent s i : bool :=
  s (widen_ord (leqnSn n) i) > s (lift ord0 i).
```

**Where** `s : {perm 'I_n.+1}`, `i : 'I_n`.

**Audit:** ⚠ 0-indexed. `widen_ord (leqnSn n) i` casts `i : 'I_n` to
`i : 'I_n.+1` keeping the same numerical value (the position `i`).
`lift ord0 i` shifts `i : 'I_n` to `i + 1 : 'I_n.+1` (the position
`i+1`). So `is_descent s i := s i > s (i+1)`, matching Stanley
modulo 0-indexing.

---

## Definition: `descent_set`

**Stanley §1.4:** `D(w) = { i : w_i > w_{i+1} } ⊆ {1, ..., n-1}`.

**Rocq** (`descent.v:25`):
```coq
Definition descent_set s : {set 'I_n} := [set i | is_descent s i].
```

**Audit:** ⚠ 0-indexed. `descent_set s : {set 'I_n}` corresponds to
Stanley's `D(w) ⊆ {1, ..., n-1}` via the index shift `our i ↔ Stanley's (i+1)`.

**Sanity:** for `s = [2,0,3,1]` (= Stanley's `[3,1,4,2]`),
`descent_set s = {0, 2}`, corresponding to Stanley's `D(w) = {1, 3}`.

---

## Definition: `des`, `asc` (descent/ascent count)

**Stanley §1.4:** `des(w) = |D(w)|`, `asc(w) = (n-1) - des(w)`.

**Rocq** (`descent.v:27, 29`):
```coq
Definition des s : nat := #|descent_set s|.
Definition asc s : nat := n - des s.
```

**Audit:** ⚠ Note that `asc s = n - des s` where our `n` is the number
of descent positions (Stanley's `n - 1`). So our `asc s` = Stanley's
`(n - 1) - des(w)`.

---

## Definition: `eulerian` (Eulerian numbers)

**Stanley §1.4, p. 32:** `A(n, k)` is the number of permutations of
`[n]` with exactly `k` descents.

**Rocq** (`eulerian.v:14-15`):
```coq
Definition eulerian (n k : nat) : nat :=
  #|[set s : {perm 'I_n.+1} | des s == k]|.
```

**Audit:** ⚠ **Off-by-one.** Our `eulerian n k` counts perms of
`'I_n.+1`, i.e. `n+1` elements. So:

> **`eulerian n k` = Stanley's `A(n+1, k)`.**

Sanity: `eulerian 3 1 = 11` ↔ Stanley's `A(4, 1) = 11` (Stanley
table p. 36).

---

## Definition: `insert_max_perm` (insert max at position `p`)

**Stanley:** Implicit in the bijection used to derive the Eulerian
recurrence. For `t ∈ S_n` and `p ∈ {1, ..., n+1}`, define `σ ∈ S_{n+1}`
by inserting the value `n+1` at position `p` in the one-line form
of `t`.

**Rocq** (`eulerian.v:134-138, 157`):
```coq
Definition insert_max_fun (i : 'I_n.+2) : 'I_n.+2 :=
  match unlift p i with
  | Some j => widen_ord (leqnSn _) (t j)
  | None => ord_max
  end.

Definition insert_max_perm : {perm 'I_n.+2} := perm insert_max_fun_inj.
```

**Audit:** ✓ At position `p`, output `ord_max` (the value `n+1`); at
positions `lift p j`, output `t j` (cast to `'I_n.+2`).

`insert_max_perm_bij` is the headline: this map is a bijection
`{perm 'I_n.+1} × 'I_n.+2 ≃ {perm 'I_n.+2}`.

---

## Definition: `extract_max_perm` (inverse of insert_max)

**Rocq** (`eulerian.v:185, 203`):
```coq
Definition extract_max_fun (j : 'I_n.+1) : 'I_n.+1 :=
  odflt j (unlift ord_max (s (lift p j))).

Definition extract_max_perm : {perm 'I_n.+1} := perm extract_max_fun_inj.
```

**Audit:** ✓ For `s : {perm 'I_n.+2}` with `s p = ord_max`, removes
position `p` and the value `ord_max`, returning the standardised perm
of `'I_n.+1`.

---

## Definition: `beta` (set-refined descent count)

**Stanley §1.4:** `β_n(S)` is the number of permutations of `[n]`
with descent set exactly `S`.

**Rocq** (`beta.v:19-20`):
```coq
Definition beta (n : nat) (D : {set 'I_n}) : nat :=
  #|[set sigma : {perm 'I_n.+1} | descent_set sigma == D]|.
```

**Audit:** ⚠ Off-by-one. Our `beta n D` for `D : {set 'I_n}` counts
perms of `'I_n.+1`, i.e. `n+1` elements. So:

> **`beta n D` = Stanley's `β_{n+1}(D)`** with `D` interpreted as a
> 0-indexed subset of `{0, ..., n-1}` corresponding to Stanley's
> 1-indexed `S ⊆ {1, ..., n}`.

---

# §1.4 — q-analogues

## Definition: `q_int` (q-integer)

**Stanley §1.4 (or any q-analog reference):**
`[k]_q = 1 + q + q² + ... + q^{k-1}`.

**Rocq** (`qfact.v:25`):
```coq
Definition q_int (n : nat) : {poly int} := \sum_(i < n) 'X^i.
```

**Audit:** ✓ Sum of `X^i` for `i ∈ {0, ..., n-1}`. Direct match.

---

## Definition: `q_fact` (q-factorial)

**Stanley §1.4:** `[n]_q! = [1]_q · [2]_q · ... · [n]_q`.

**Rocq** (`qfact.v:26`):
```coq
Definition q_fact (n : nat) : {poly int} := \prod_(k < n.+1) q_int k.+1.
```

**Audit:** ⚠ Off-by-one. `\prod_(k < n.+1) q_int k.+1` is
`q_int 1 * q_int 2 * ... * q_int (n+1)`, so:

> **`q_fact n`** = `[1]_q · [2]_q · ... · [n+1]_q` = Stanley's
> **`[n+1]_q!`**.

---

## Definition: `q_eul_pol` (q-Eulerian polynomial, bivariate)

**Stanley §1.4:** `A_n(q, t) = ∑_{w ∈ S_n} q^{maj(w)} · t^{des(w)}`.

**Rocq** (`qeul.v:31, 37-38`):
```coq
Notation qpow k := (('X ^+ k : {poly int})%:P : {poly {poly int}}).

Definition q_eul_pol (n : nat) : {poly {poly int}} :=
  \sum_(σ : {perm 'I_n.+1}) qpow (maj σ) * 'X^(des σ).
```

**Audit:** ⚠ Off-by-one + notation. `q_eul_pol n` sums over
`{perm 'I_n.+1}` (Stanley's `S_{n+1}`), so:

> **`q_eul_pol n`** = Stanley's **`A_{n+1}(q, t)`**.

The outer `'X` is `t`; the inner `'X` (under `qpow`) is `q`.

Specializations (proven in the file):
- `q_eul_pol_t1 : (q_eul_pol n).[1] = q_fact n` — setting `t := 1`
  recovers `[n+1]_q!`.
- `q_eul_pol_q1 : q1_subst (q_eul_pol n) = eul_pol n` — setting
  `q := 1` recovers the classical Eulerian polynomial.

---

## Definition: `eul_pol` (classical Eulerian polynomial)

**Stanley §1.4:** `A_n(t) = ∑_{k ≥ 0} A(n, k) · t^k`.

**Rocq** (`qeul.v:58-59`):
```coq
Definition eul_pol (n : nat) : {poly int} :=
  \sum_(k < n.+1) (eulerian n k)%:R * 'X^k.
```

**Audit:** ⚠ Off-by-one (inherited from `eulerian`). Our `eul_pol n`
= Stanley's `A_{n+1}(t)`.

---

## Definition: `q1_subst` (substitute q := 1)

**Rocq** (`qeul.v:81-82`):
```coq
Definition q1_subst : {poly {poly int}} -> {poly int} :=
  map_poly (horner_eval (1 : int)).
```

**Audit:** ✓ Maps each coefficient (which is a `{poly int}` in the
inner ring `q`) to its evaluation at `q = 1`. Standard mathcomp
construction.

---

# §1.6.2 — Longest alternating subsequence

## Definition: `is_turn` (turning point)

**Stanley §1.6.2:** A position is a *turning point* of `w` if the
direction of `w` changes there.

**Rocq** (`altsub.v:41-42`):
```coq
Definition is_turn s (i : 'I_n) : bool :=
  is_descent s (widen_ord (leqnSn _) i) (+) is_descent s (lift ord0 i).
```

**Where** `s : {perm 'I_n.+2}`, `i : 'I_n` (so `is_turn` looks at
two consecutive descent slots in `'I_n.+1`).

**Audit:** ✓ XOR of two adjacent descent indicators ⇔ direction
changes between them. Note: the position type `'I_n` here means
"interior turn position" (between slot `i` and slot `i+1`, where slots
are descent slots in `'I_n.+1`).

---

## Definition: `turn_count`

**Rocq** (`altsub.v:44-45`):
```coq
Definition turn_count s : nat :=
  #|[set i : 'I_n | is_turn s i]|.
```

**Audit:** ✓ Cardinality of turning-point set.

---

## Definition: `is_alt` (alternating sequence of nats)

**Stanley §1.6.2:** A seq `x_1, x_2, ..., x_k` is alternating if
`x_1 < x_2 > x_3 < ...` or `x_1 > x_2 < x_3 > ...` (either parity).

**Rocq** (`altsub.v:71-77`):
```coq
Definition is_alt (xs : seq nat) : bool :=
  match xs with
  | [::] => true
  | [:: _] => true
  | x :: y :: xs' =>
      ((x < y) && alt_aux false y xs') || ((y < x) && alt_aux true y xs')
  end.
```

**Where** `alt_aux b x xs` checks that the rest of the sequence
alternates with the parity bit `b` (defined inductively).

**Audit:** ✓ Empty and singleton seqs are vacuously alternating;
otherwise we try both starting directions (up-down and down-up).

---

## Definition: `perm_seq` (perm as a seq of values)

**Rocq** (`altsub.v:84-85`):
```coq
Definition perm_seq n (s : {perm 'I_n.+2}) : seq nat :=
  [seq val (s i) | i <- enum 'I_n.+2].
```

**Audit:** ✓ The one-line form of `s`: `[s 0; s 1; ...; s (n+1)]` as
a seq of `nat`.

---

## Definition: `pick_seq` (subsequence at chosen positions)

**Rocq** (`altsub.v:97-98`):
```coq
Definition pick_seq n (s : {perm 'I_n.+2}) (I : {set 'I_n.+2}) : seq nat :=
  [seq val (s j) | j <- sort (fun a b => val a <= val b) (enum I)].
```

**Audit:** ✓ Sort the positions in `I` by value, then pick the
corresponding values from `s`. Used in `as_perm_max` to define what
"the subsequence at positions `I` is alternating" means.

---

## Definition: `as_perm_max` (longest alternating subseq, bijective form)

**Stanley §1.6.2:** `as(w) = max {|I| : w_I is alternating}` where
`w_I` is the subsequence at positions `I`.

**Rocq** (`altsub.v:105-106`):
```coq
Definition as_perm_max n (s : {perm 'I_n.+2}) : nat :=
  \max_(I : {set 'I_n.+2} | is_alt (pick_seq s I)) #|I|.
```

**Audit:** ✓ Direct match. Maximum over all index sets `I` whose
sorted-by-position picked seq is alternating.

---

## Definition: `as_perm` (longest alt subseq, direct formula)

**Rocq** (`altsub.v:109`):
```coq
Definition as_perm n (s : {perm 'I_n.+2}) : nat := (turn_count s).+2.
```

**Audit:** ✓ Stanley's characterization (Theorem in §1.6.2):
`as(w) = turn_count(w) + 2`. We take this as the definition; the
equivalence with the bijective form is the headline theorem
`as_perm_max_eq` (`altsub.v`).

---

# §1.6.3 — Toggle action and `ω`

## Definition: `sym_diff`, `toggle_at`

**Rocq** (`beta_omega.v:25-29`):
```coq
Definition sym_diff (n : nat) (D E : {set 'I_n}) : {set 'I_n} :=
  (D :\: E) :|: (E :\: D).

Definition toggle_at (n : nat) (D : {set 'I_n}) (i : 'I_n) : {set 'I_n} :=
  sym_diff D [set i].
```

**Audit:** ✓ Standard set-theoretic symmetric difference, and the
"toggle membership of `i`" operation.

---

## Definition: `omega_set` (Stanley's `ω`)

**Stanley §1.6.3:** For a descent set `D ⊆ {1, ..., n-1}` of a
permutation in `S_n`, `ω(D) ⊆ {1, ..., n-2}` records positions where
the descent indicator changes between consecutive descent slots.
(Used in the cd-index development.)

**Rocq** (`beta_omega.v:57-58`):
```coq
Definition omega_set (n : nat) (D : {set 'I_n.+1}) : {set 'I_n} :=
  [set k : 'I_n | (widen_ord (leqnSn n) k \in D) != (lift ord0 k \in D)].
```

**Audit:** ⚠ 0-indexed, with the standard widen/lift idiom.
`widen_ord _ k` is position `k` in `'I_n.+1`; `lift ord0 k` is
position `k+1`. So `k ∈ omega_set D` iff membership in `D` differs
between consecutive positions `k` and `k+1` — exactly Stanley's
ω-map.

---

## Definition: `alt_desc_set` (the alternating descent pattern)

**Stanley §1.6.3 (used in Cor 1.6.5):** The "alternating" descent set
`{1, 3, 5, ...} ∩ {1, ..., n-1}` (1-indexed) corresponds to the
even-indexed positions in 0-indexed form.

**Rocq** (`beta_swap.v:31-32`):
```coq
Definition alt_desc_set (n : nat) : {set 'I_n} :=
  [set i : 'I_n | ~~ odd i].
```

**Audit:** ⚠ 0-indexed. `~~ odd i` selects `i ∈ {0, 2, 4, ...}`. In
Stanley's 1-indexing this is `{1, 3, 5, ...}` — the "alternating
descent" pattern.

---

## Definition: `set_is_alt` (set-alternating predicate)

**Rocq** (`beta_swap.v:40-42`):
```coq
Definition set_is_alt (n : nat) (D : {set 'I_n}) : bool :=
  [forall i : 'I_n, [forall j : 'I_n,
     (val j == (val i).+1) ==> ((i \in D) != (j \in D))]].
```

**Audit:** ✓ For every consecutive pair `(i, i+1)`, membership
differs. Equivalent to "`D = alt_desc_set n` or `D = ~: alt_desc_set n`"
(proven as `set_is_alt_classify` in the same file).

---

## Definition: `compl_perm` (value-complement involution)

**Stanley §1.6.3:** Implicit. Map `σ ↦ σ'` where `σ'(i) = (n+1) - σ(i)`;
flips ascents and descents (so `D(σ') = ~: D(σ)`).

**Rocq** (`beta_swap.v:128-129`):
```coq
Definition compl_perm n (s : {perm 'I_n.+1}) : {perm 'I_n.+1} :=
  s * rev_perm_ord n.
```

where `rev_perm_ord` (from `descent.v:80`) is the permutation
`i ↦ rev_ord i = n - i`.

**Audit:** ✓ `compl_perm s i = rev_ord (s i) = n - s i` (proven
as `compl_permE` at line 131). The proven `descent_set_compl`
(line 160) gives `descent_set (compl_perm s) = ~: descent_set s`,
matching Stanley's value-complement.

---

# §1.4 (auxiliary) — Permutation-compression utilities

## Definition: `drop_perm`, `lift_perm`

**Stanley:** Used implicitly in inductive proofs (drop a position;
lift back).

**Rocq** (`perm_compress.v:24, 32, 50, 71`):
```coq
Definition drop_fun (i : 'I_n) : 'I_n := sval (unlift_some (drop_fun_ne i)).
Definition drop_perm : {perm 'I_n} := perm drop_fun_inj.

Definition lift_fun (i : 'I_n.+1) : 'I_n.+1 := ...
Definition lift_perm : {perm 'I_n.+1} := perm lift_fun_inj.
```

**Audit:** ✓ Helper constructions. `drop_perm` removes the value
`s ord_max` from a perm of `'I_n.+1`, producing a perm of `'I_n`.
`lift_perm` is the inverse.

**Naming caution.** Mathcomp also has a `lift_perm` in
`mathcomp/algebra/perm.v`. Some files use `perm.lift_perm` to
qualify; this matters in `perm_seq_bridge.v` and `cycles_rec.v`.

---

# Summary

| Section | Definitions audited | Convention notes |
|---------|---------------------|------------------|
| §1.3.1 cycles | `cycle_count`, `stirling_c` | Stirling matches directly. |
| §1.3.3 inv/maj | `is_inv`, `inv`, `maj`, `coinv_set` | `maj` shifts back to 1-indexed. |
| §1.3.4 Foata | `is_desc_seq`, `maj_seq`, `inv_seq`, `foata_step`, `foata`, `foata_perm` | Seq vs perm forms agree. |
| §1.4 descents | `is_descent`, `descent_set`, `des`, `asc` | 0-indexed positions. |
| §1.4 Eulerian | `eulerian`, `insert_max_perm`, `extract_max_perm`, `beta` | `eulerian n k = A(n+1, k)`. |
| §1.4 q-analogues | `q_int`, `q_fact`, `q_eul_pol`, `eul_pol`, `q1_subst` | `q_fact n = [n+1]_q!`. |
| §1.6.2 alt-subseq | `is_turn`, `turn_count`, `is_alt`, `perm_seq`, `pick_seq`, `as_perm_max`, `as_perm` | 0-indexed turning positions. |
| §1.6.3 toggle/ω | `sym_diff`, `toggle_at`, `omega_set`, `alt_desc_set`, `set_is_alt`, `compl_perm` | 0-indexed; `alt_desc_set` is even positions. |

**All entries audited as ✓ or ⚠ (matches Stanley modulo a noted
convention).** No ✗ entries.

If you want to verify any of these computationally:

```coq
(* In a Rocq REPL *)
From mathcomp_eulerian Require Import descent inversions.
Print descent_set.
Print maj.
(* etc. *)
```

Or simply open the `.v` files at the line numbers cited above.
