# Plan: `reflection.v` — André's reflection method

> **Status (after Session C-8).**  `experimental/reflection.v` (1751
> LOC) proves `euler_rec` end-to-end behind ONE precisely-stated
> `Admitted`: `sum_set_is_alt_eq_andre_sum` (the André recurrence in
> inner form, ~250-400 LOC to discharge).  The file is moved out of
> the active build chain (`_CoqProject` excludes it) to preserve the
> project-wide "0 axioms, 0 Admitted" invariant.  Build manually:
>     coqc -R . mathcomp_eulerian experimental/reflection.v
>
> **Forward-looking design document below.** Phase C of the Stanley
> §1.6 extension.  Builds on `beta_swap.v` (alternating descent set
> work) and `beta.v` (the `beta` count).

## 1. Goal

Stanley EC1 §1.6.4 — **André's reflection method** for the Euler
numbers $E_n$ counting alternating permutations.

In our setup, the alternating descent set is `alt_desc_set n`
(a `{set 'I_n}`), and the count of permutations with that exact
descent set is `beta (alt_desc_set n)`.  This is precisely $E_n$.

**Targets** (corrected after three-agent design session):

```coq
Definition euler n : nat := beta (alt_desc_set n).
(* euler n = A_{n+1} in Stanley's notation (count for length n+1) *)

Definition eulerA n : nat :=
  if n is k.+1 then euler k else 1.
(* eulerA n = A_n in Stanley's notation; base case eulerA 0 = 1 *)

(* Base cases *)
Lemma eulerA_0 : eulerA 0 = 1.       (* by def *)
Lemma eulerA_1 : eulerA 1 = 1.       (* euler 0 = 1, only id ∈ S_1 *)
Lemma eulerA_2 : eulerA 2 = 1.       (* euler 1 = 1, only [1;0] ∈ S_2 has descent {0} *)
Lemma eulerA_3 : eulerA 3 = 2.       (* euler 2 = 2 *)

(* The headline recurrence — CORRECTED from the prior plan *)
Theorem euler_rec n :
  2 * eulerA n.+2 =
    \sum_(k < n.+2) 'C(n.+1, k) * eulerA k * eulerA (n.+1 - k).
```

**Verification of the corrected recurrence:**
- n=0: LHS = 2·eulerA 2 = 2·1 = 2; RHS = C(1,0)·1·1 + C(1,1)·1·1 = 1+1 = 2. ✓
- n=1: LHS = 2·eulerA 3 = 2·2 = 4; RHS = C(2,0)·1·1 + C(2,1)·1·1 + C(2,2)·1·1 = 1+2+1 = 4. ✓
- n=2: LHS = 2·eulerA 4 = 2·5 = 10; RHS = 1·1·2 + 3·1·1 + 3·1·1 + 1·2·1 = 10. ✓

**The original plan's stated recurrence was WRONG** under our `alt_desc_set` convention.  Verified by hand-enumeration: at n=2, original LHS=10 vs RHS=6.

The recurrence captures André's bijective proof: given $\sigma \in
\Snp{n+1}$, let $j$ be the position of $n+1$.  The left subword
(positions $0, \dots, j-1$) can be rearranged uniquely into an
alternating perm of $\{j$ chosen values$\}$, and the right subword
(positions $j+1, \dots, n$) independently.  Summing over $j$ and
the choice of which $j$ values go left gives the convolution
$\sum_k \binom{n}{k} E_k E_{n-k}$.  The factor of $2$ accounts for
both alternation directions (down-up vs up-down).

## 2. The substantive bijection

For $\sigma \in \Snp{n+2}$ with $\descent_{\mathrm{alt}}$ pattern, let:

- $j := \sigma^{-1}(\mathrm{ord\_max})$ — position of the maximum.
- $L := \{\sigma_0, \dots, \sigma_{j-1}\}$, $R := \{\sigma_{j+1}, \dots, \sigma_n\}$.
- Both $L$ and $R$ inherit some alternating structure from
  $\descent_{\mathrm{alt}}$ in $\sigma$.

The classical statement: $L$ rearranged into a *decreasing-then-increasing*
form is alternating, and so is $R$; they're independent.

Counting: $\sum_j \binom{n+1}{j} \cdot E_{j} \cdot E_{n-j}$ where
$j$ ranges over valid positions of the max.  Position $j$ must be at a
"local max" in $\sigma$ (always true, since $\sigma_j = n+1$ is the
global max), but the alternating constraint restricts to $j$ where
both sides "fit" the pattern.

For the down-up convention, this gives the reflection identity
$2 E_{n+1} = \sum_k \binom{n}{k} E_k E_{n-k}$.

## 3. Estimated effort

| Section | LOC | Difficulty |
|---------|-----|------------|
| Definitions + base cases | ~30 | low |
| Position-of-max bijection setup | ~80 | medium |
| Alternating-restriction lemmas | ~120 | medium-high |
| Recurrence assembly via partition_big | ~100 | medium |
| Optional: closed-form via separate generating function | ~? | high (skip) |
| **Total (recurrence only)** | **~330 LOC** | |

## 4. Risks

1. **Two alternating conventions.**  Stanley's "alternating" comes in
   two flavors: down-up and up-down.  Our `alt_desc_set n` is one
   of them.  The recurrence's factor of $2$ comes from coupling the
   two; if our convention only counts one, the factor adjusts.
   Verify on small examples first.

2. **Position-of-max bijection.**  We have `insert_max_perm`/
   `extract_max_perm` in `eulerian.v` (used for `eulerian_rec` and
   `inv_q_fact`).  These bijections decompose
   $\Snp{n+2} \simeq \Snp{n+1} \times \mathrm{position}$, but the
   alternating-descent-set restriction is subtle.

3. **Subset-of-values sub-permutations.**  When $\sigma_0, \dots,
   \sigma_{j-1}$ are taken to be a perm of some $j$-element subset
   of $[n]$, this needs an explicit lift to $\Snp{j}$ (via "rank in
   sorted order") for the recurrence's $E_k$ on the LHS.  Mathcomp's
   `perm_of_inj` constructions can do this but it's bookkeeping.

## 5. Sanity checks (do FIRST)

Compute small examples:
- $E_0 = 1$ (empty perm).
- $E_1 = 1$ (single-element perm).
- $E_2 = 1$ (just $[0; 1]$ has alternating descent set $\{0\}$? Or
  $\{\}$?  Depends on convention).
- $E_3 = 2$.
- $E_4 = 5$.
- $E_5 = 16$.

Verify by `Compute beta (alt_desc_set k)` for $k = 0, \dots, 5$.
If the values don't match Stanley, the convention is misaligned and
needs fixing before any proof.

## 6. Sequential session plan

Following the Phase B model:

- **Session C-1:** definitions + base cases + sanity check. Confirm
  `beta (alt_desc_set n)` matches Euler numbers.
- **Session C-2:** position-of-max bijection + restriction lemmas.
- **Session C-3:** recurrence assembly.
- **Session C-4:** (if needed) close any remaining gaps.

## 7. What this DOESN'T cover

- The EGF $\sum E_n x^n / n! = \sec x + \tan x$ — needs formal power
  series, out of mathcomp core scope.
- Connection to Bernoulli/zeta numbers (also EGF territory).
- Specific closed-form formulas for $E_n$ in terms of Stirling numbers
  or other combinatorial objects (some exist but require additional
  machinery).

The recurrence alone is the substantive Phase C deliverable.
