# Plan: `qeul.v` — q-Eulerian polynomials

> **Forward-looking design document.** Phase A of the §1.4 extension
> (joint inv/maj/des distribution).  Successor to §1.3.4's
> q-factorial work in `qfact.v`.

## 1. Goal

Stanley EC1 §1.4: the **q-Eulerian polynomial**

```
A_n(q, t) = \sum_{w ∈ S_n} q^{maj(w)} · t^{des(w)}
```

is the bivariate joint generating function for `(maj, des)` over
permutations.  Its specializations recover everything we have:

- `A_n(q, 1) = q-factorial [n]_q!`        (sum over all des-counts)
- `A_n(1, t) = classical Eulerian polynomial`  (drop the maj weight)

The headline goal: **define `A_n(q, t)` formally and prove these two
specializations**.

## 2. Polynomial type

Use mathcomp's `{poly {poly int}}` — polynomials in `t` with
coefficients in `{poly int}` (which carries our `q`).

```coq
Notation Q := {poly int}.        (* the q-coefficient ring *)
Notation Pqt := {poly Q}.        (* bivariate q,t polynomials *)
```

The "outer" indeterminate (call it `T : Pqt`, given by `'X` in `Pqt`'s
own scope) is `t`.  The "inner" indeterminate (call it `q : Q`) is
`'X` in `Q`'s scope.  Coercion of `Q` into `Pqt` lifts a univariate
q-polynomial into a constant t-polynomial.

## 3. Definitions

```coq
Definition q_eul_pol (n : nat) : Pqt :=
  \sum_(σ : {perm 'I_n.+1}) (q_int_inj 'X^(maj σ)) * 'X^(inv σ).
```

Wait — that's not quite right.  Let me re-derive.  We want the
**q-power** to be `q^maj` (in the inner ring) and the **t-power** to
be `t^des` (in the outer ring).

```coq
Definition q_eul_pol (n : nat) : Pqt :=
  \sum_(σ : {perm 'I_n.+1})
    (Q.qX_q^(maj σ))%:P * 'X^(des σ).
```

Where `(_:%:P)` is the constant-poly embedding `Q -> Pqt`, and the
inner `Q.qX_q := 'X : Q` is the q-indeterminate.

Cleanest definition:

```coq
Notation q := ('X : {poly int}).                          (* in Q-scope *)
Notation t := ('X : {poly {poly int}}).                   (* in Pqt-scope *)
Notation qpow k := ((q ^+ k) %:P : {poly {poly int}}).    (* q^k as Pqt *)

Definition q_eul_pol (n : nat) : {poly {poly int}} :=
  \sum_(σ : {perm 'I_n.+1}) qpow (maj σ) * t ^+ (des σ).
```

## 4. Specializations

### 4.1 `t = 1` gives the q-factorial

```coq
Theorem q_eul_pol_t1 n :
  (q_eul_pol n).[1] = q_fact n.
```

Proof: `_.[1]` evaluates the outer polynomial at `t = 1`, giving
`\sum_σ qpow (maj σ) * 1^(des σ) = \sum_σ qpow (maj σ)
                                 = \sum_σ q^(maj σ) = q_fact n` by
`maj_q_fact` from `qfact.v`.

The technical glue is bigops in mixed scopes; the result follows
from `horner_sum`, `hornerXn`, and `maj_q_fact`.

### 4.2 `q = 1` gives the classical Eulerian polynomial

```coq
Definition eul_pol (n : nat) : {poly int} :=
  \sum_(k < n.+1) (eulerian n k)%:R * 'X^k.

Theorem q_eul_pol_q1 n :
  (q_eul_pol n) ^^ id_at_q1 = eul_pol n.
```

Where `^^` is "apply to coefficients" — substitute `q = 1` into each
coefficient of the outer polynomial.  Or more cleanly, evaluate at
`q := 1` via the inner ring's `_.[1]`.

Result: `\sum_σ 1^(maj σ) * t^(des σ) = \sum_σ t^(des σ)
       = \sum_(k < n.+1) (eulerian n k) * t^k` (partition by
des-count using `beta_eulerian`).

## 5. Estimated effort

| Section | LOC | Difficulty |
|---------|-----|------------|
| poly imports + scope setup + notations | ~30 | low (but fiddly) |
| `q_eul_pol` def + small Compute sanity | ~20 | low |
| `q_eul_pol_t1` (specialization to q-factorial) | ~50 | medium |
| `q_eul_pol_q1` (specialization to Eulerian poly) | ~80 | medium-high |
| Optional: `eul_pol` matches `eulerian_explicit`-style | ~50 | low |
| **Total** | **~230 LOC** | |

## 6. Risks

1. **Bivariate poly idioms.**  `{poly {poly int}}` is workable but
   notation-heavy.  Inserting / extracting coefficients across the
   two layers needs care.  Consider a small `Notation` block at the
   top to make it readable.

2. **Scope discipline.**  `Open Scope ring_scope` is needed for
   poly operations, but `nat`-style operations in surrounding files
   need `%N` annotations.  Same gotcha as in `qfact.v`.

3. **Specialization at `q = 1`.**  The `^+ k` notation shifts when
   the underlying ring changes.  Use `horner_eval` or `map_poly`
   carefully; mathcomp has `comm_polyXn` and `map_polyZ` for the
   cross-coefficient operations.

## 7. Stretch goals (Phase A-2)

If A-1 lands cleanly, the next targets:

- **q-Eulerian recurrence** (Stanley Th 1.4.6):
  `A_{n+1}(q, t) = (1 + t([n+1]_q - 1)) A_n(q, t) +
                    t(1 - t) (q · ∂_q A_n)(q, t)`
  This requires polynomial differentiation in `q`.  Mathcomp has
  `deriv : {poly R} -> {poly R}` (univariate derivative).  Lifting
  to bivariate is straightforward.

- **Carlitz identity** (Stanley Cor 1.4.8):
  `∑_(k ≥ 0) [k+1]_q^n t^k = A_n(q, t) / ∏_(i=0)^n (1 - t q^i)`
  This needs formal power series, which mathcomp doesn't ship in
  the core.  Skippable for now.

## 8. Once `qeul.v` lands

- Add to `_CoqProject` and `make -j2`.
- Update `ch_inversions.tex` blueprint with a §"q-Eulerian polynomial"
  section.
- Mark §1.4 extension complete.
- Cross-link from the existing `eulerian_explicit` (the `q=1` case
  recovers the classical formula).

This will close the cycle: Stanley §1.3 (cycles + inversions) and
§1.4 (joint maj/des distribution) both fully formalized, with the
q-factorial as the "hub" identity.
