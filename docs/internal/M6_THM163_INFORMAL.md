> **Historical document — pre-formalization proof sketch (Milestone 6).**
> Paper-style scaffold for Stanley Theorem 1.6.3 (cd-index of S_n has
> nonnegative coefficients).  The theorem is not formalized as a
> standalone Rocq lemma — Fact #3 (`fact3`) supplies the substantive
> content.  Superseded by the blueprint chapter `ch_cdindex.tex` for
> current readers.  See [`README.md`](README.md).

# Milestone 6: Theorem 1.6.3 --- the cd-index of S_n has nonneg coefficients

**Source of truth.** Stanley, *Enumerative Combinatorics* vol. 1 (2nd ed.),
section 1.6.3, lines 336--371 of `refs/stanley_1_6_cdindex.txt`.

**Dependencies.**
- Milestone 5: Fact #3, `Phi_w(a+b, ab+ba) = Sum_{v in [w]} u_{D(v)}`.
- `psi.v`: `psi`, `psi_comm`, `psi_involutive`, Fact #2 axioms.
- `beta.v`: definition of `beta`.
- `beta_swap.v` section H: `omega_set`, `toggle_at_omega_bit_i_new`,
  `toggle_at_omega_strict_superset`.

---

## 1. Statement of Theorem 1.6.3

### 1.1 The ab-index Psi_n

For a permutation w of [n], define the descent set D(w) = {k : w[k] > w[k+1]}
and the characteristic monomial u_S = e_0 e_1 ... e_{n-2} where e_k = b if
k in S, e_k = a otherwise. The **ab-index** of S_n is

    Psi_n = Psi_n(a, b) = Sum_{w in S_n} u_{D(w)}
                         = Sum_{S <= [n-1]} beta(S) * u_S.      (1.63)

### 1.2 The cd-index Phi_n

For each permutation w, the min-max tree M(w) determines a classifier string
Phi'_w = f_0 f_1 ... f_{n-1} where f_i in {c, d, e} (see M5 note section
1.2). Setting e = 1 (delete e-factors) yields a cd-monomial Phi_w(c, d).
Since Phi_w depends only on the unlabeled tree shape, it is constant on the
M-equivalence class [w].

The **cd-index** of S_n is

    Phi_n = Sum_{[w]} Phi_w,

where the sum ranges over the E_n distinct M-equivalence classes [w] in S_n.

### 1.3 The theorem

**Theorem 1.6.3** (Stanley). *The ab-index Psi_n can be written as a
polynomial Phi_n in the variables c = a+b and d = ab+ba. This polynomial
is a sum of E_n monomials (hence has nonnegative integer coefficients).*

Equivalently: Psi_n = Phi_n(a+b, ab+ba).

---

## 2. Proof

The proof is a direct assembly from Fact #3. There are no new ideas.

**Step 1 (Grouping).** Partition S_n into M-equivalence classes [w]:

    Psi_n = Sum_{w in S_n} u_{D(w)}
          = Sum_{[w]} ( Sum_{v in [w]} u_{D(v)} ).                (1.64)

This is valid because M-equivalence classes partition S_n (reflexivity,
symmetry, and transitivity of M-equivalence follow from the group structure
of G_w; see M5 note section 1.3).

**Step 2 (Fact #3 applied to each class).** By Fact #3 (M5, equation 1.62):

    Sum_{v in [w]} u_{D(v)} = Phi_w(a+b, ab+ba).

Here Phi_w is a single cd-monomial with coefficient 1.

**Step 3 (Assembly).** Substituting Step 2 into Step 1:

    Psi_n = Sum_{[w]} Phi_w(a+b, ab+ba)
          = ( Sum_{[w]} Phi_w )(a+b, ab+ba)
          = Phi_n(a+b, ab+ba).

Since Phi_n is a sum of E_n cd-monomials (one per M-equivalence class,
each with coefficient 1), its coefficients are nonnegative integers. Some
distinct classes may produce the same cd-monomial (they do, for n >= 4),
so coefficients can exceed 1. QED.

**Example.** For n = 3 the two classes are [123] (Phi_w = cc) and [132]
(Phi_w = d), giving Phi_3 = c^2 + d. Then
Psi_3 = (a+b)^2 + (ab+ba) = aa + 2ab + 2ba + bb, matching beta values
beta({}) = beta({0,1}) = 1, beta({0}) = beta({1}) = 2.

---

## 3. What this means for beta(S)

### 3.1 beta(S) as a count of M-classes

From Psi_n = Phi_n(a+b, ab+ba) = Sum_{[w]} Phi_w(a+b, ab+ba), read off the
coefficient of u_S on both sides:

    beta(S) = |{ M-equivalence classes [w] : u_S appears in Phi_w(a+b, ab+ba) }|.

That is, beta(S) counts the number of M-classes whose cd-monomial, when
expanded via c -> a+b, d -> ab+ba, contains the monomial u_S. Each such
class contributes exactly 1 to the count (since Phi_w is a single monomial
with coefficient 1, and each expansion term is a distinct u_X).

### 3.2 The support of Phi_w(a+b, ab+ba) via the omega map

For a cd-monomial Phi_w = g_1 g_2 ... g_m (where each g_j is c or d, and
the degree is n-1 counting deg c = 1, deg d = 2), define

    S_w = { position of each d-factor in the degree-expanded indexing }.

More precisely: write Phi'_w = f_0 ... f_{n-1} (the cde-string, before
deleting e-factors); then S_w = {i-1 : f_i = d} (Stanley line 386).

The key observation (Stanley line 388--390, "easy to see"):

    Phi_w(a+b, ab+ba) = Sum_{X : omega(X) >= S_w} u_X.

In other words, u_X appears in the expansion of Phi_w iff omega(X) >= S_w.

**Proof sketch.** Each c-factor at internal position i contributes (a+b),
whose terms select "i in X" or "i not in X" independently. Each d-factor
at position i contributes (ab+ba), which forces "exactly one of i, i+1 in
X" --- i.e., i in omega(X). The e-factors are deleted (coefficient 1, no
choice). The condition "omega(X) >= S_w" collects exactly the positions
forced by d-factors.

### 3.3 Nonnegativity and monotonicity

From section 3.1:

    beta(S) = |{ [w] : omega(S) >= S_w }| >= 0.

This is manifestly nonneg. Moreover, if omega(S) <= omega(T) then every
class counted by beta(S) is also counted by beta(T), so beta(S) <= beta(T).
This is the weak form of Proposition 1.6.4.

---

## 4. Formalization strategy

### 4.1 What we actually need

The end goal is to close the two axioms in `beta_swap.v`:

```coq
Axiom beta_swap_monotone_both_in : forall n (D : {set 'I_n}) (i j : 'I_n),
  val j = (val i).+1 -> i \in D -> j \in D -> beta D <= beta (toggle_at D i).

Axiom beta_swap_lt_both_in : forall n (D : {set 'I_n}) (i j : 'I_n),
  val j = (val i).+1 -> i \in D -> j \in D -> beta D < beta (toggle_at D i).
```

These are a special case of **Proposition 1.6.4** (lines 382--395):

    omega(S) < omega(T)  ==>  beta(S) < beta(T)     (strict containment)

applied with T = toggle_at D i, using `toggle_at_omega_strict_superset` (or
the weaker `toggle_at_omega_bit_i_new` for the monotone case, plus a witness
argument for strict).

**We do NOT need Theorem 1.6.3 in full generality.** We need Proposition
1.6.4, whose proof uses:

(A) `Phi_w = Sum_{omega(X) >= S_w} u_X` (the support characterization),
(B) Phi_n has nonneg coefficients (Theorem 1.6.3),
(C) A witness cd-word for the strict inequality.

### 4.2 The minimal formalization path

The formalization should avoid building the full cd-index algebra. Instead:

**Key insight:** We can state Prop 1.6.4 directly in terms of beta and
omega_set, without mentioning Phi_n or cd-monomials at all. The proof
decomposes as:

1. **Weak monotonicity:** omega(S) <= omega(T) ==> beta(S) <= beta(T).
   This is the core content of Theorem 1.6.3. It can be formalized as:

   ```coq
   Lemma beta_omega_monotone n (S T : {set 'I_n.+1}) :
     omega_set S \subset omega_set T -> beta S <= beta T.
   ```

   One route: define beta(S) = |{[w] : omega(S) >= S_w}| and derive from
   the subset condition. But defining S_w requires M-classes and tree
   classifiers (heavy). An alternative: state this as an axiom and close it
   later when tree infrastructure lands.

2. **Strict witness:** For each k in omega(T) \ omega(S), the cd-word
   c^{k} d c^{n-3-k} has S_w = {k}, so it contributes to beta(T) but not
   beta(S). This gives strict inequality. Formally:

   ```coq
   Lemma beta_omega_strict n (S T : {set 'I_n.+1}) :
     omega_set S \proper omega_set T -> beta S < beta T.
   ```

3. **Bridge to axioms:** Combine with the existing omega infrastructure
   in beta_swap.v section H.

### 4.3 Recommended approach: two-axiom replacement

Replace the current two axioms in beta_swap.v with a single, more
mathematically natural axiom:

```coq
(* Prop 1.6.4, weak form: omega-monotonicity of beta *)
Axiom beta_omega_monotone : forall n (S T : {set 'I_n.+1}),
  omega_set S \subset omega_set T -> beta S <= beta T.
```

Then derive both `beta_swap_monotone_both_in` and `beta_swap_lt_both_in`
from it. The derivation of the strict version uses:

- `beta_omega_monotone` for the <= direction.
- The witness cd-word argument for strict inequality: pick k in
  omega(toggle_at D i) \ omega(D) (exists by `toggle_at_omega_bit_i_new`).
  Then there exists a set X with omega(X) = {k} (namely, take X so that
  exactly one of k, k+1 is in X and all other consecutive pairs agree).
  This X contributes to beta(toggle_at D i) but not beta(D).

However, formalizing the witness argument still requires showing that there
exists a permutation (or equivalently, an M-class) realizing the cd-word
c^k d c^{m-k} for each valid k. This is non-trivial.

**Pragmatic recommendation:** Keep the two axioms as stated. They are the
minimal axiomatic surface for the downstream `beta_alt_max` theorem, and
they directly encode the needed instances of Prop 1.6.4. When Milestones
1--5 land in Rocq (the tree infrastructure), closing them will be a clean
application of the omega-bridge already built in section H.

### 4.4 Estimated LOC

The assembly step (this milestone) itself is ~100 LOC once Milestones 1--5
are in place:

| Component | LOC | Notes |
|-----------|-----|-------|
| `Phi_n` as sum of class monomials | 20 | Definition + basic properties |
| `Psi_n = Phi_n(a+b, ab+ba)` | 30 | Direct from Fact #3 + partitioning |
| Nonneg coefficients | 10 | Immediate from definition |
| `beta_omega_monotone` (weak 1.6.4) | 20 | From support characterization |
| `beta_omega_strict` (strict 1.6.4) | 20 | Witness argument |

---

## 5. Connecting to beta_swap.v

### 5.1 The two axioms and what they encode

The axioms in `beta_swap.v` section C state: if i and j = i+1 are both
descents of D, then

    beta(D) <= beta(toggle_at D i)     (monotone)
    beta(D) <  beta(toggle_at D i)     (strict)

where `toggle_at D i` flips the membership of i in D (so i leaves D,
becoming an ascent, while j stays).

### 5.2 The omega-bridge (section H)

Section H of `beta_swap.v` establishes:

1. **`toggle_at_omega_bit_i_new`**: Under the both-in hypothesis, there
   exists k with widen_ord k = i and lift ord0 k = j such that k is NOT
   in omega(D) but IS in omega(toggle_at D i). This gives omega(D) != 
   omega(toggle_at D i) with a new element.

2. **`toggle_at_omega_strict_superset`**: Under the additional hypothesis
   that the predecessor position (i-1) is in D (or i = 0), we get the
   full strict containment omega(D) < omega(toggle_at D i).

The gap: `toggle_at_omega_strict_superset` requires an extra hypothesis
(predecessor in D or i = 0) that the axioms do not assume. When i > 0 and
i-1 is not in D, toggling i also flips the omega-bit at position i-1 OUT
of omega(D). So omega(toggle_at D i) is neither a subset nor a superset
of omega(D) in general --- it gains the bit at i but may lose the bit at
i-1.

### 5.3 How Prop 1.6.4 closes the gap

Proposition 1.6.4 as stated by Stanley does NOT require omega(S) <= omega(T)
to be witnessed by a single toggle. It handles arbitrary pairs S, T with
omega(S) < omega(T). The axioms in beta_swap.v are used in a context where
we can always arrange the needed containment:

**Route A (direct, for the conditional case):** When i = 0 or i-1 in D,
`toggle_at_omega_strict_superset` gives omega(D) < omega(toggle_at D i),
and Prop 1.6.4 applies directly.

**Route B (general case):** When i > 0 and i-1 not in D, one can show
via case analysis that beta(D) < beta(toggle_at D i) still holds, but
the omega-route requires a more refined argument. Specifically, one needs:

- omega(D) and omega(toggle_at D i) differ at exactly two bits: position
  i (gained) and position i-1 (lost).
- The cd-index provides the inequality because the "gained" bit contributes
  more to beta than the "lost" bit does (this is where the nonneg
  coefficients and the witness argument do real work).

This is the substantive content that Milestones 1--7 formalize.

### 5.4 The M6 -> M7 interface

M6 delivers: Phi_n has nonneg coefficients (this note's theorem).

M7 uses it to prove: beta_omega_monotone (weak Prop 1.6.4), then
beta_omega_strict (strict Prop 1.6.4), then derives the two axioms of
beta_swap.v section C from the omega-bridge infrastructure of section H.

---

## 6. Deliverables

### 6.1 Informal (this note)

This document constitutes the M6 informal proof note.

### 6.2 Rocq lemma statements (to be formalized when M1--M5 land)

```coq
(* --- Theorem 1.6.3: cd-index has nonneg coefficients --- *)

(* The ab-index equals a cd-polynomial with nonneg coefficients.
   Stated as: Psi_n = Sum over M-classes of Phi_w(a+b, ab+ba). *)
Lemma Psi_eq_cd_sum n :
  Psi n = \sum_(cls in M_classes n) Phi_w_expanded cls.

(* Each Phi_w contributes coefficient 1, so Phi_n has nonneg coefficients. *)
Lemma cd_index_nonneg n (m : cd_monomial) :
  0 <= coeff m (Phi n).

(* --- Proposition 1.6.4 --- *)

(* Support characterization: u_X appears in Phi_w(a+b, ab+ba) iff
   omega(X) >= S_w. *)
Lemma Phi_w_support n (w : {perm 'I_n}) (X : {set 'I_n}) :
  (u_X \in support (Phi_w_expanded (M_class w))) =
  (S_w w \subset omega_set X).

(* Weak monotonicity *)
Lemma beta_omega_monotone n (S T : {set 'I_n.+1}) :
  omega_set S \subset omega_set T -> beta S <= beta T.

(* Strict monotonicity *)
Lemma beta_omega_strict n (S T : {set 'I_n.+1}) :
  omega_set S \proper omega_set T -> beta S < beta T.

(* --- Closing the axioms --- *)

(* These replace the current Axiom declarations in beta_swap.v *)
Lemma beta_swap_monotone_both_in n (D : {set 'I_n}) (i j : 'I_n) :
  val j = (val i).+1 -> i \in D -> j \in D ->
  beta D <= beta (toggle_at D i).

Lemma beta_swap_lt_both_in n (D : {set 'I_n}) (i j : 'I_n) :
  val j = (val i).+1 -> i \in D -> j \in D ->
  beta D < beta (toggle_at D i).
```

### 6.3 File map

| File | Role |
|------|------|
| `M6_THM163_INFORMAL.md` | This note |
| `psi.v` | Facts #1--#3 (M2--M5) |
| `beta_swap.v` section H | omega-bridge (already formalized) |
| `beta_swap.v` section C | Axioms to be closed (M7) |
| Future `cdindex.v` | Theorem 1.6.3 + Prop 1.6.4 formalization |
