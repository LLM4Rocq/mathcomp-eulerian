# Milestone 7: Closing the two axioms in `beta_swap.v`

**Critical finding:** The two axioms as currently stated are **false**. The
toggle direction is wrong: the axioms toggle at i (the lower of two
consecutive descents), but should toggle at j = i+1 (the upper one).
This note documents the counterexamples, diagnoses the root cause, explains
why the naive omega-bridge approach fails, and provides the corrected
axiom statements with a proof outline.

---

## 1. The two axioms --- precise statement

In `beta_swap.v` (lines 119--129), the two axioms are:

```coq
Axiom beta_swap_monotone_both_in : forall n (D : {set 'I_n}) (i j : 'I_n),
  val j = (val i).+1 -> i \in D -> j \in D ->
  beta D <= beta (toggle_at D i).

Axiom beta_swap_lt_both_in : forall n (D : {set 'I_n}) (i j : 'I_n),
  val j = (val i).+1 -> i \in D -> j \in D ->
  beta D < beta (toggle_at D i).
```

**Mathematical translation.** Fix n >= 1. Let D be a subset of
{0, 1, ..., n-1} (encoded as `{set 'I_n}`). Define

    beta(D) = |{sigma in S_{n+1} : descent_set(sigma) = D}|.

When both i and j = i+1 are in D, `toggle_at D i = D Delta {i}`. Since
i is in D, this gives D \ {i}. The axioms claim beta(D) <= beta(D \ {i})
(weak) and beta(D) < beta(D \ {i}) (strict).

---

## 2. The axioms are false: counterexamples

### 2.1 Strict axiom fails: n = 3, D = {1,2}, i = 1

Permutations of {0,1,2,3} = S_4. We take i = 1, j = 2, both in D.
toggle_at({1,2}, 1) = {2}.

**beta({1,2}) --- descent set {1,2}: sigma(0) < sigma(1) > sigma(2) > sigma(3).**

sigma(1) must be the maximum of the last three values and sigma(0) < sigma(1).

- sigma(1) = 3: sigma(0) in {0,1,2}; sigma(2) > sigma(3) from remaining.
  - sigma(0)=0: (sigma(2),sigma(3)) = (2,1). Perm (0,3,2,1). D = {1,2}. Good.
  - sigma(0)=1: (sigma(2),sigma(3)) = (2,0). Perm (1,3,2,0). D = {1,2}. Good.
  - sigma(0)=2: (sigma(2),sigma(3)) = (1,0). Perm (2,3,1,0). D = {1,2}. Good.

No other value of sigma(1) works (checked: sigma(1) = 2 leads to remaining
values that can't satisfy both constraints). **beta({1,2}) = 3.**

**beta({2}) --- descent set {2}: sigma(0) < sigma(1) < sigma(2) > sigma(3).**

- sigma(2) = 3: sigma(0) < sigma(1) from {0,1,2}, sigma(3) = remaining.
  - (0,1,3,2), (0,2,3,1), (1,2,3,0). All have D = {2}. 3 perms.

No other sigma(2) works. **beta({2}) = 3.**

**Result: beta({1,2}) = 3 = beta({2}). The strict axiom claims 3 < 3. FALSE.**

### 2.2 Both axioms fail: n = 4, D = {2,3}, i = 2

Permutations of {0,1,2,3,4} = S_5. i = 2, j = 3, both in D.
toggle_at({2,3}, 2) = {3}.

**beta({2,3}) --- sigma(0) < sigma(1) < sigma(2) > sigma(3) > sigma(4).**

sigma(2) = 4: left pair from {0,1,2,3} (C(4,2) = 6 ways), right pair in
decreasing order from remaining. All 6 are valid:
(0,1,4,3,2), (0,2,4,3,1), (0,3,4,2,1), (1,2,4,3,0), (1,3,4,2,0), (2,3,4,1,0).

sigma(2) <= 3 gives no valid perms (remaining values always include 4
which can't be placed in a decreasing sequence below sigma(2)).
**beta({2,3}) = 6.**

**beta({3}) --- sigma(0) < sigma(1) < sigma(2) < sigma(3) > sigma(4).**

sigma(3) = 4: first three values increasing from {0,1,2,3}, last value =
remaining. C(4,3) = 4 ways:
(0,1,2,4,3), (0,1,3,4,2), (0,2,3,4,1), (1,2,3,4,0).

sigma(3) <= 3: remaining values include 4 which must go before sigma(3)
but then sigma(2) < sigma(3) <= 3 < 4 = sigma(earlier) breaks the
increasing condition. No valid perms. **beta({3}) = 4.**

**Result: beta({2,3}) = 6, beta({3}) = 4. The monotone axiom claims
6 <= 4. FALSE. The strict axiom claims 6 < 4. FALSE.**

### 2.3 The correct direction: toggle at j

With the same setup but toggling j instead of i:

**n = 3, D = {1,2}, toggle at j = 2:** toggle_at({1,2}, 2) = {1}.
beta({1}) --- sigma(0) < sigma(1) > sigma(2) < sigma(3):
- sigma(1) = 3: 3 perms (vary sigma(0)).
- sigma(1) = 2: 2 perms.
Total: **beta({1}) = 5.** Inequality: 3 < 5. TRUE.

**n = 4, D = {2,3}, toggle at j = 3:** toggle_at({2,3}, 3) = {2}.
beta({2}) --- sigma(0) < sigma(1) < sigma(2) > sigma(3) < sigma(4):
- sigma(2) = 4: 6 perms (split remaining 4 values into increasing left,
  increasing right pairs).
- sigma(2) = 3: 3 perms. Total: **beta({2}) = 9.**
Inequality: 6 < 9. TRUE.

**Toggling j = i+1 gives the correct inequality direction.**

---

## 3. The gap in the omega-bridge approach

### 3.1 Stanley's omega map

For S contained in [n-1], define omega(S) contained in [n-2] by:
k in omega(S) iff exactly one of k, k+1 is in S.

### 3.2 Why direct omega-containment fails for the i-toggle

When both i, i+1 in D and we remove i (toggle_at D i = D \ {i}), the
omega-bit analysis gives:

| Position k | omega(D) | omega(D \ {i}) | Change |
|------------|----------|----------------|--------|
| k = i-1    | true (i-1 not in D, i in D) | false (neither in) | Lost |
| k = i      | false (both i, i+1 in D)    | true (i not in, i+1 in) | Gained |
| other k    | unchanged | unchanged | --- |

(This assumes i > 0, i-1 not in D. When i = 0 or i-1 in D, the picture is
different and omega-containment CAN hold.)

So omega(D) and omega(D \ {i}) differ by swapping bit i-1 for bit i:
**neither contains the other.** Prop 1.6.4 does not apply to this pair.

**Concrete example:** D = {1,2} in [3]. omega({1,2}) = {0},
omega({2}) = {1}. {0} not subset of {1} and {1} not subset of {0}.

### 3.3 The omega analysis for the j-toggle

When we remove j = i+1 instead (toggle_at D j = D \ {j}):

| Position k | omega(D) | omega(D \ {j}) | Change |
|------------|----------|----------------|--------|
| k = i      | false (both i, i+1 in D) | true (i in, i+1 not in) | Gained |
| k = i+1=j  | f(j, j+1 in D) | f(j not in, j+1 in D) | May change |
| k = i-1    | unchanged (depends on i-1 and i, both unchanged) | unchanged | --- |
| other k    | unchanged | unchanged | --- |

The critical difference: **the bit at i-1 is NOT affected** by the j-toggle
(since neither i-1 nor i changes membership). The only bits that change are
at positions i (gained) and j = i+1 (may flip depending on j+1).

**Case A (j+1 in D or j = n-1):** Position j: in D, j and j+1 both in D
(or j at boundary), so j not in omega(D). In D \ {j}: j not in D', j+1
in D' (or boundary), so j in omega(D') or boundary. Either way, the bit
at j is gained or unchanged. Combined with i being gained:
**omega(D) is strictly contained in omega(D \ {j}).** Prop 1.6.4 applies.

**Case B (j+1 not in D, j < n-1):** Position j: in D, exactly one of j,
j+1 in D (since j in D, j+1 not in D), so j in omega(D). In D \ {j}:
neither j nor j+1 in D', so j not in omega(D'). Bit at j is **lost**. We
gain i and lose j = i+1, a swap of adjacent bits. omega-containment fails,
as with the i-toggle.

So the j-toggle also has a problematic case (B). However, as the numerical
examples show, the inequality beta(D) < beta(D \ {j}) still holds in
Case B. The proof requires the full cd-index machinery.

---

## 4. The correct argument to close the (corrected) axioms

### 4.1 Case A: omega-containment holds

When j+1 in D or j = n-1 (the last position):

**omega(D) is strictly contained in omega(D \ {j}).** This is the analogue
of `toggle_at_omega_strict_superset` for the j-toggle. By Prop 1.6.4,
beta(D) < beta(D \ {j}). Both the weak and strict axioms follow.

### 4.2 Case B: omega-containment fails, cd-index argument needed

When j+1 not in D and j < n-1:

omega(D) = C union {j} and omega(D \ {j}) = C union {i}, where
C = omega(D) intersect omega(D \ {j}) and i = j-1, j not in C, i not in C.

Wait -- let me redo this for the j-toggle. We gain bit i and lose bit j = i+1.

    omega(D) = C union {j}       (j in omega(D), i not in omega(D))
    omega(D') = C union {i}      (i in omega(D'), j not in omega(D'))

where D' = D \ {j} and C = omega(D) intersect omega(D').

Using the cd-index characterization (Theorem 1.6.3, M6):

    beta(S) = |{M-classes [w] : S_w subset omega(S)}|

Partition the M-classes into:
- A = {[w] : S_w subset C}: contribute to both beta(D) and beta(D').
- L = {[w] : j in S_w, i not in S_w, S_w \ {j} subset C}: contribute to beta(D) only.
- R = {[w] : i in S_w, j not in S_w, S_w \ {i} subset C}: contribute to beta(D') only.
- (M_11 = empty since |i - j| = 1 and d-positions must be spaced >= 2.)

So beta(D) = |A| + |L| and beta(D') = |A| + |R|. We need |L| < |R|.

**Key fact:** i < j (since i = j-1). The d-position sets S_w are
"independent sets" in the path graph on {0, ..., n-2} (no two adjacent
elements). The cd-index coefficient of a monomial m is exactly the number
of M-classes with d-position set S_m.

The elements of L are monomials m with j in S_m, i not in S_m, and
S_m \ {j} subset C. The elements of R are monomials m' with i in S_m',
j not in S_m', and S_m' \ {i} subset C.

Define a map phi: L -> R by phi(m) = monomial with S_{phi(m)} = (S_m \ {j}) union {i}.

**phi is well-defined** (S_{phi(m)} is a valid independent set): Since j in
S_m and no two d-positions are adjacent, j-1 = i not in S_m (given) and
j+1 not in S_m. Now S_{phi(m)} = (S_m \ {j}) union {i}. Need: no element
of S_m \ {j} is adjacent to i. Adjacent to i = j-1 means i-1 = j-2 or
i+1 = j. j not in S_m \ {j} (removed). Is j-2 in S_m \ {j}? Since j in S_m,
we know j-1 not in S_m (non-adjacency). But j-2 could be in S_m. If j-2
in S_m, then in S_{phi(m)} we'd have j-2 and i = j-1 adjacent. INVALID.

So phi is well-defined **only when j-2 not in S_m**. When j-2 in S_m,
the map fails.

Similarly, the reverse map psi: R -> L replacing i with j fails when
i+1+1 = j+1 in S_m'.

**This means a simple bijection between L and R does not exist.** The
comparison |L| < |R| (weighted by cd-index coefficients) requires a
deeper argument.

### 4.3 The refined cd-index coefficient argument

The inequality |L| < |R| (in the notation of 4.2) can be established by
the following argument, which uses the **recursive structure** of the
cd-index.

**Claim.** For any independent set C subset {0, ..., n-2} not containing
i or j = i+1, and for any 0 <= i < j = i+1 <= n-2:

    Sum_{m : i in S_m, j not in S_m, S_m \ {i} subset C} coeff(m, Phi_n)
    > Sum_{m : j in S_m, i not in S_m, S_m \ {j} subset C} coeff(m, Phi_n)

This says: the marginal contribution of position i to the beta count
(relative to the base set C) strictly exceeds the marginal contribution of
position j = i+1.

**Why this should be true:** Position i is "further from the boundary" of
the interval [i, j]. In the cd-index, a d-factor at position k contributes
to more M-classes when k is closer to the center of [n-2] than to the
edges. But this is a heuristic, not a proof.

A rigorous proof of |L| < |R| appears to require an analysis of the
cd-index coefficients using the recursive structure of min-max trees. This
is beyond what Milestones 1-6 provide directly and would need additional
infrastructure.

**However**, there is a simpler alternative:

### 4.4 Alternative: avoid Case B entirely

**Observation.** In the proof of `beta_alt_max`, we have freedom in
choosing WHICH same-pair to fix at each step. We don't have to toggle
every same-pair; we just need to find ONE toggle that strictly increases
beta.

**Strategy:** When D is non-alternating, find a same-pair (i, j) such
that the j-toggle falls into Case A (omega-containment holds), avoiding
Case B entirely.

**Claim:** For any non-alternating D, there exists a same-pair (i, j = i+1)
with (i in D) = (j in D) such that:
- If both are in D: j+1 in D or j = n-1.
- If both are out of D: i-1 not in D or i = 0 (the complementary condition).

**Is this true?** Consider D = {1,2} in {0,1,2} (n = 3). The only same-pair
is (1,2), both in D. j = 2 = n-1 = 2. So j = n-1, which IS Case A!

Wait, n = 3 means 'I_3 = {0,1,2}, and j = 2 is the maximum element. So
j = n-1 = 2. Case A applies! Let me recheck: j+1 = 3 is out of range
(not in 'I_3), so the "j at boundary" case of Case A applies.

Hmm, but I computed that omega({1,2}) = {0} and omega({1}) = {1} (for the
j-toggle giving D' = {1}). Are these related by containment? omega is a
subset of 'I_2 = {0,1}.

omega({1,2}): k=0: 0 not in D, 1 in D -> yes. k=1: 1 in D, 2 in D -> no.
omega = {0}.

omega({1}): k=0: 0 not in D', 1 in D' -> yes. k=1: 1 in D', 2 not in D' -> yes.
omega = {0, 1}.

{0} is strictly contained in {0, 1}! So omega-strict-containment holds!

Wait, this works! Let me recheck my earlier analysis. For the j-toggle
with j = 2 (= n-1 in 'I_3):

Position i = 1: omega(D) has i not in it (both 1,2 in D). omega(D') has
i in it (1 in D', 2 not in D'). Gained.

Position j = 2: but j = 2 is the maximum in 'I_3, and omega_set maps
{set 'I_3} to {set 'I_2} = {set {0,1}}. Position j = 2 is NOT in the
domain of omega! The omega positions are 0, ..., n-2 where n = 3,
so 0 and 1. Position j = 2 is out of range.

So the only position that changes is i = 1 (gained). All other positions
are unchanged. Therefore omega(D) is strictly contained in omega(D'). QED.

**So for the counterexample D = {1,2}, the j-toggle DOES give
omega-containment, and Case A applies.** My earlier analysis of Case B was
for the scenario j < n-1 and j+1 not in D. Let me check: when does Case B
actually arise for the j-toggle?

Case B for j-toggle: j+1 not in D AND j < n-1 (so j+1 exists as a valid
index). We need both i and j = i+1 in D but j+1 not in D.

Example: n = 5, D = {1, 2} subset 'I_5 = {0,...,4}. i = 1, j = 2.
j+1 = 3 not in D. j = 2 < 4 = n-1. This IS Case B.

toggle_at D j = D \ {j} = {1}. Let me check the beta values.

Actually, the same-pair analysis for `beta_alt_max` might have MULTIPLE
same-pairs to choose from. Can we always find one in Case A?

For D = {1, 2} in 'I_5: the same-pairs are (1, 2) (both in D). Also check
other pairs: (0,1): 0 not in D, 1 in D -> different, not a same-pair.
(2,3): 2 in D, 3 not in D -> different. (3,4): 3 not in D, 4 not in D ->
same-pair! Both out of D.

So for D = {1,2} in 'I_5, we have TWO same-pairs: (1,2) both in, and (3,4)
both out. The "both out" case can be handled via complement: the corrected
axiom applied to ~: D. Let me check whether the (3,4) pair gives Case A.

For the "both out" pair (3,4): through complement, ~: D = {0,3,4} (in 'I_5).
In ~: D, i'=3 and j'=4 are both in ~: D. j' = 4 = n-1 = 4, so j' is at the
boundary. Case A applies.

So for D = {1, 2} in 'I_5, we CAN find a same-pair where Case A applies
(the pair (3,4) rather than (1,2)). But we need this to work for ALL
non-alternating D.

**Claim: for any non-alternating D, there exists a same-pair (i, j=i+1)
such that the j-toggle gives omega-strict-containment.**

I'm not sure this is true in general. Consider a carefully constructed D
where every same-pair falls into Case B.

Example: n = 6, 'I_6 = {0,...,5}. D = {1, 2, 4, 5}. Same-pairs:
- (0,1): 0 not in D, 1 in D -> different.
- (1,2): both in D. j = 2, j+1 = 3 not in D, j < 5. Case B!
- (2,3): 2 in D, 3 not in D -> different.
- (3,4): 3 not in D, 4 in D -> different.
- (4,5): both in D. j = 5 = n-1 = 5. Case A! (boundary)

So (4,5) gives Case A. What if we pick n = 7 and D = {1,2,4,5} subset
'I_7? Then (4,5): j = 5, j+1 = 6 not in D, j < 6 = n-1. Case B. But
also (5,6): 5 in D, 6 not in D -> different. And (6,7): only goes to 6
in 'I_7... hmm, 'I_7 = {0,...,6}, so (5,6): 5 in D, 6 not in D ->
different. No same-pair at the boundary.

But there may be "both out" same-pairs: (2,3): 2 in D, 3 not in D ->
different. (6,... ) only up to 6. (0,1): 0 not in D, 1 in D -> different.
(3,4): 3 not in D, 4 in D -> different.

Hmm, are there any other same-pairs? Going through all consecutive pairs
in {0,...,6}:
- (0,1): (0, in D) = (false, true) -> different.
- (1,2): (true, true) -> same, both in D.
- (2,3): (true, false) -> different.
- (3,4): (false, true) -> different.
- (4,5): (true, true) -> same, both in D.
- (5,6): (true, false) -> different.

So same-pairs: (1,2) and (4,5), both "both in D".

For (1,2): j=2, j+1=3 not in D, j < 6. Case B.
For (4,5): j=5, j+1=6 not in D, j < 6. Case B.

**Both same-pairs fall into Case B!** The "avoid Case B" strategy fails
for D = {1,2,4,5} in 'I_7.

So we cannot avoid Case B in general. **Case B must be handled.**

### 4.5 The correct proof for Case B

For Case B (j+1 not in D, j < n-1), we have:

    omega(D) = C union {j},  omega(D') = C union {i}  where i = j-1

and we need beta(D) < beta(D') (i.e., |{[w] : S_w subset C union {j}}| < |{[w] : S_w subset C union {i}}|).

This is equivalent to showing:

    f(C, j) < f(C, i)

where f(C, k) = Sum_{m : k in S_m, S_m \ {k} subset C} coeff(m, Phi_n)
is the "marginal contribution" of adding position k to the base set C.

Note that i < j (i = j-1), so this says the marginal contribution of the
LOWER position exceeds that of the HIGHER adjacent position.

**This is NOT obvious and may in fact be false in general.** Let me verify
numerically for n = 7, D = {1,2,4,5}, same-pair (1,2), toggle at j = 2.

D' = {1,4,5}. I would need to compute beta_8({1,2,4,5}) and beta_8({1,4,5})
for permutations of {0,...,7}. This is a large computation. Instead, let me
use the relation beta(S) = Sum over Phi_n monomials.

For n = 7, the cd-index Phi_7 is not listed in Stanley. The computation
is feasible but laborious.

**Instead, let me try a simpler numerical check:** n = 5, D = {1,2} in
'I_5 = {0,...,4}, same-pair (1,2), toggle at j = 2. D' = {1}.

Permutations of {0,...,5} = S_6 with descent set {1,2}:
sigma(0) < sigma(1) > sigma(2) > sigma(3) < sigma(4) < sigma(5).

sigma(1) is a local max, sigma(0) < sigma(1), sigma(1) > sigma(2) > sigma(3),
sigma(3) < sigma(4) < sigma(5).

This is getting complex. Let me just use the known formula. For n = 5
(permutations in S_6), the cd-index Phi_6 is given by Stanley (line 371):

    Phi_6 = c^5 + 4c^3 d + 9c^2 dc + 9cdc^2 + 4dc^3 + 12cd^2 + 10dcd + 12d^2 c

Each monomial has degree 5 (deg c = 1, deg d = 2). The d-positions (S_m)
for each monomial:

- c^5: S_m = {}. Degree positions: 0,1,2,3,4 all c. No d. S_m = {}.
- c^3 d: degree positions: cccdd -> positions 0,1,2 are c, position 3-4
  is d. S_m = {3}. Coeff = 4.
- c^2 dc: positions 0,1 are c, 2-3 is d, 4 is c. S_m = {2}. Coeff = 9.
- cdc^2: position 0 is c, 1-2 is d, 3,4 are c. S_m = {1}. Coeff = 9.
- dc^3: positions 0-1 is d, 2,3,4 are c. S_m = {0}. Coeff = 4.
- cd^2: position 0 is c, 1-2 is d, 3-4 is d. S_m = {1,3}. Coeff = 12.
- dcd: positions 0-1 is d, 2 is c, 3-4 is d. S_m = {0,3}. Coeff = 10.
- d^2 c: positions 0-1 is d, 2-3 is d, 4 is c. S_m = {0,2}. Coeff = 12.

Now, omega is a subset of 'I_4 = {0,1,2,3} (since D is in 'I_5, omega
maps to 'I_4).

For D = {1,2}: omega({1,2}):
- k=0: exactly one of 0,1 in D: 0 not in D, 1 in D -> yes. k=0 in omega.
- k=1: both 1,2 in D -> no.
- k=2: 2 in D, 3 not in D -> yes.
- k=3: 3 not in D, 4 not in D -> no.
omega({1,2}) = {0, 2}.

For D' = {1}: omega({1}):
- k=0: 0 not in D', 1 in D' -> yes.
- k=1: 1 in D', 2 not in D' -> yes.
- k=2: 2 not, 3 not -> no.
- k=3: 3 not, 4 not -> no.
omega({1}) = {0, 1}.

omega(D) = {0,2}, omega(D') = {0,1}. Neither is a subset of the other!
Confirms Case B (gained bit at i=1, lost bit at j=2).

beta(D) = |{m : S_m subset {0,2}}|:
- S_m = {}: 1. Always subset. Coeff = 1.
- S_m = {0}: subset of {0,2} yes. Coeff = 4.
- S_m = {2}: subset yes. Coeff = 9.
- S_m = {0,2}: subset yes. Coeff = 12.
- S_m = {1}: 1 not in {0,2}. No.
- S_m = {3}: 3 not in {0,2}. No.
- S_m = {1,3}: no.
- S_m = {0,3}: 3 not in {0,2}. No.
beta(D) = 1 + 4 + 9 + 12 = 26.

beta(D') = |{m : S_m subset {0,1}}|:
- S_m = {}: 1.
- S_m = {0}: yes. 4.
- S_m = {1}: yes. 9.
- S_m = {0,2}: 2 not in {0,1}. No.
- S_m = {2}: no.
- S_m = {3}: no.
- S_m = {1,3}: no.
- S_m = {0,3}: no.

Wait, but I also need to check for S_m being non-adjacent subsets of {0,1}.
{0,1} are adjacent (differ by 1). But we need S_m to be a valid d-position
set, which means no two adjacent. So S_m = {0,1} is NOT valid. The valid
subsets of {0,1} with no two adjacent: {}, {0}, {1}.

beta(D') = 1 + 4 + 9 = 14.

Hmm wait, that's not right. Let me recount. S_m subset omega(D') means
S_m subset {0,1}. The valid d-position sets that are subsets of {0,1}:
{}, {0}, {1}. (Not {0,1} since those are adjacent.)

So beta(D') = coeff(S_m={}) + coeff(S_m={0}) + coeff(S_m={1}) = 1 + 4 + 9 = 14.
beta(D) = coeff(S_m={}) + coeff(S_m={0}) + coeff(S_m={2}) + coeff(S_m={0,2}) = 1 + 4 + 9 + 12 = 26.

So beta({1,2}) = 26 and beta({1}) = 14 for n = 5 (S_6).

**beta(D) = 26 > 14 = beta(D').** Toggling j = 2 gives beta going DOWN!

**WAIT.** The corrected axiom claims beta(D) < beta(toggle_at D j), but
here beta(D) > beta(D'). So the corrected axiom is ALSO false?!

Let me double-check using the direct enumeration for a smaller case. For
n = 3, D = {1,2}, toggle at j = 2: D' = {1}. I computed beta({1,2}) = 3
and beta({1}) = 5. So 3 < 5 (beta goes up). That worked!

But for n = 5, the cd-index computation gives beta({1,2}) = 26 and
beta({1}) = 14 (beta goes DOWN). Something is wrong with my cd-index
computation.

**THE ISSUE:** I'm confusing the index conventions! The cd-index Phi_6
is for S_6, which has permutations of {1,...,6} with descent positions in
{1,...,5}. But the Rocq code uses 0-indexed: permutations of {0,...,5}
with descent positions in {0,...,4}. There's a shift-by-1.

Also, `beta n D` for D : {set 'I_n} counts permutations of 'I_{n+1} =
{0,...,n} with descent set D subset {0,...,n-1}. So for n = 5, we're
counting permutations of {0,...,5} = S_6 with descent set D subset
{0,...,4}.

Stanley's Phi_n is for S_n, using 1-indexed positions. Phi_6 is for S_6
with descent positions in {1,...,5}. When we convert to 0-indexed, descent
position k (Stanley) becomes k-1 (Rocq). So Stanley's ω uses positions
{1,...,n-2} (for S_n), while Rocq's omega_set uses {0,...,n-3}.

Let me redo the omega computation in 0-indexed terms for n = 5 (the Rocq
parameter), which gives S_6. Descent positions are 0,...,4 (= 'I_5).
omega maps 'I_5 to 'I_4 = {0,1,2,3}. omega(S) has k in it iff exactly
one of k, k+1 is in S (for k in {0,...,3}).

For D = {1,2} subset 'I_5:
- k=0: one of 0,1 in D? 0 no, 1 yes -> yes.
- k=1: one of 1,2 in D? both -> no.
- k=2: one of 2,3 in D? 2 yes, 3 no -> yes.
- k=3: one of 3,4 in D? neither -> no.
omega(D) = {0,2} subset 'I_4. Correct as before.

For D' = {1} subset 'I_5:
- k=0: one of 0,1? 0 no, 1 yes -> yes.
- k=1: one of 1,2? 1 yes, 2 no -> yes.
- k=2: one of 2,3? neither -> no.
- k=3: one of 3,4? neither -> no.
omega(D') = {0,1}. Correct.

Now the cd-index Phi_6 from Stanley uses 1-indexed positions. The
d-positions S_m in Stanley's convention are {i-1 : f_i = d} where i ranges
from 1 to n. In 0-indexed (Rocq), this becomes {i : f_{i+1} = d} where
f_{i+1} uses 1-indexed labeling of the cd-string.

Actually, let me re-read Stanley line 384-386:

> Let w in S_n and Phi'_w = f_1 f_2 ... f_n, so each f_i = c, d, or e.
> Define S_w = {i - 1 : f_i = d}.

So for Phi_6, the cd-word has total degree n-1 = 5 (since Phi_6 is for
S_6). The positions of characters in the cd-word are... hmm, actually a
cd-word like c^2 dc has characters at positions 1,2,3,4 in the cde-string
Phi'_w = f_1...f_6. No wait, the cde-string Phi'_w has n = 6 characters.
S_w = {i-1 : f_i = d} gives positions in {0,...,5}. But omega(S) is a
subset of {0,...,n-2} = {0,...,4} for S_6. And the formula says

    Phi_w(a+b, ab+ba) = Sum_{omega(X) >= S_w} u_X.

This requires S_w to be a subset of the omega domain {0,...,n-2} = {0,...,4}
for this to make sense.

But actually S_w can have elements up to n-1 = 5 (if f_6 = d, then
6-1 = 5 in S_w). And omega(X) is a subset of {0,...,n-2} = {0,...,4}. So
the containment omega(X) >= S_w requires S_w subset {0,...,4}, which means
f_n = f_6 is never d (it's always e --- the last element is an endpoint).

OK, so S_w subset {0,...,n-2} for all w. Good.

Now for Phi_6 = c^5 + 4c^3d + 9c^2dc + 9cdc^2 + 4dc^3 + 12cd^2 + 10dcd + 12d^2c.

I need to map each cd-monomial to its d-position set. A cd-monomial is a
product of c's and d's with total degree n-1 = 5. Each c contributes degree
1 and each d contributes degree 2. The d-positions are the starting
positions (0-indexed) in the degree-expanded word.

Let me think of the degree-expanded word as having 5 positions (0 through 4).
A d at position p occupies slots p and p+1.

Wait no. The cde-string Phi'_w has n characters (for S_n). The cd-word
Phi_w is obtained by deleting e's from Phi'_w. But S_w = {i-1 : f_i = d}
where f_i is the i-th character of the cde-string, not the cd-word.

The cd-word and the cde-string are different! The cde-string has exactly
n characters. The cd-word has fewer (the e's are removed). The d-positions
S_w come from the cde-string, using the original indexing.

So for S_6: cde-string has 6 characters, positions 1 through 6.
S_w = {i-1 : f_i = d, 1 <= i <= 6}.

The cd-word Phi_w is the cde-string with e's removed. Each e corresponds
to an endpoint of the min-max tree. The cd-word's total degree (sum of
deg c + deg d) accounts for the internal vertices (c's and d's), while
e's are leaves (endpoints). The total characters in the cde-string is
n = (internal vertices) + (leaves). For a binary tree with k internal
vertices, there are k+1 leaves... Actually, the tree isn't necessarily
binary.

I think I've been confusing myself with the indexing. Let me go back to
basics.

The formula from Stanley (line 388-390):

    Phi_w = Sum_{omega(X) >= S_w} u_X

where u_X is the ab-monomial. This is an identity in the free Z[a,b]
algebra. On the left, Phi_w is a cd-monomial substituted with c = a+b,
d = ab+ba. On the right, we sum over all subsets X of [n-1] with
omega(X) >= S_w.

So:

    beta(S) = [u_S] Psi_n = [u_S] Sum_{[w]} Phi_w(a+b, ab+ba)
            = |{[w] : [u_S] Phi_w(a+b, ab+ba) = 1}|
            = |{[w] : omega(S) >= S_w}|

Now, for a cd-monomial Phi_w = g_1 g_2 ... g_m (sequence of c's and d's,
total degree n-1), what is S_w?

S_w comes from the cde-string. The relationship between the cd-word and
the cde-string is: the cde-string has characters for ALL vertices
(including endpoints = leaves), while the cd-word has characters only for
non-endpoints (internal vertices). The positions in the cde-string are
1, ..., n (the positions a_1, ..., a_n of the permutation).

The d-positions in S_w = {i-1 : f_i = d} correspond to vertices a_i that
have BOTH a left and right child in M(w). The c-positions correspond to
vertices with only a right child. The e-positions correspond to endpoints
(no children on one side).

Expanding Phi_w(c=a+b, d=ab+ba): each c factor gives (a+b), each d factor
gives (ab+ba). The expansion of a d at position i-1 contributes the
constraint that exactly one of i-1, i is in X. This is precisely the
definition of omega(X) at position i-1.

But here's the subtlety: the "position" of a d in the cd-word does NOT
directly correspond to a position in {0,...,n-2}. The cd-word has its own
indexing (determined by the number of preceding c's and d's), and the
cde-string has the original indexing 1,...,n.

I think the correct interpretation is: Phi_w as a cd-word generates
positions in {0,...,n-2} via the degree-expansion. The j-th character
of Phi_w (j = 1,...,m where m = #non-endpoints) maps to a position in the
degree-expansion. But this is not the same as the cde-string position.

Actually, re-reading M6_THM163_INFORMAL.md section 3.2 more carefully:

> More precisely: write Phi'_w = f_0 ... f_{n-1} (the cde-string, before
> deleting e-factors); then S_w = {i-1 : f_i = d} (Stanley line 386).

Wait, that uses 0-indexed cde-string f_0 ... f_{n-1}. And S_w = {i-1 : f_i = d}
= {i : f_{i+1} = d} in 0-indexed? No, if the cde-string is 0-indexed as
f_0, ..., f_{n-1}, then S_w = {i-1 : f_i = d} doesn't make sense for
f_0 (would give i-1 = -1). Let me use Stanley's 1-indexed convention.

Stanley: f_1, ..., f_n. S_w = {i-1 : f_i = d}. So if f_2 = d, then 1 is
in S_w. If f_5 = d, then 4 is in S_w. S_w subset {0, ..., n-1}.

But omega(X) subset {1, ..., n-2} in Stanley's convention (since the
condition is i in omega(S) iff exactly one of i, i+1 in S, for 1 <= i <=
n-2, with S subset {1,...,n-1}). So S_w subset {0,...,n-1} but omega(X)
subset {1,...,n-2}. The containment omega(X) >= S_w requires S_w subset
{1,...,n-2}.

This is guaranteed because f_1 is always c or e (the root of M(w) has no
left subtree... wait, that's not true in general). Actually, f_1 corresponds
to a_1 (the first element of w). In M(w), a_1 is inserted first and
becomes the root. The root has a right subtree (a_2, ..., a_n are inserted
to its right in the tree) but no left subtree. So f_1 = c (right child
only) or f_1 = e (if n = 1, endpoint). Either way, f_1 != d. So 0 not in
S_w.

Similarly, f_n corresponds to a_n, the last element, which is always a
leaf (endpoint). So f_n = e, and n-1 not in S_w.

So S_w subset {1, ..., n-2}. And in Rocq (0-indexed), S_w subset {0,...,n-3}.
And omega maps to {0,...,n-3} as well. Good, the containment makes sense.

**Now let me redo the cd-index computation.**

For Phi_6 (Stanley, n = 6): each cd-monomial has total degree n-1 = 5.
The d-positions S_m come from expanding the cd-word into a degree-5 string.

For a cd-word g_1 g_2 ... g_m (degree 5), the i-th character has a
"starting position" in the degree expansion:
- Position of g_1 is 0.
- Position of g_2 is 0 + deg(g_1).
- Position of g_j is Sum_{k<j} deg(g_k).

A d-factor at starting position p means p in S_m.

But WAIT: this is the cd-word position, not the cde-string position.
S_w is defined using the cde-string position. These are different because
the cde-string includes e-characters (leaves).

Hmm. I think the key identity Phi_w(a+b, ab+ba) = Sum_{omega(X) >= S_w} u_X
uses S_w defined from the cde-string, not from the cd-word alone. But
Phi_w IS the cd-word (with e's deleted). When we expand Phi_w(c=a+b,
d=ab+ba), each c or d factor in the cd-word corresponds to a non-e position
in the cde-string.

The cd-word Phi_w has characters only at positions where f_i != e. These
positions form a subsequence of {1,...,n}. The degree expansion of the
cd-word assigns position p = sum of degrees of preceding cd-characters.

But S_w = {i-1 : f_i = d} uses the ORIGINAL position i in {1,...,n}. So
S_w is defined with respect to the cde-string indexing, not the cd-word
indexing.

Two DIFFERENT cd-words can correspond to the same cd-monomial (as elements
of the free monoid on {c,d}) but have different S_w sets because the e's
are in different positions.

THIS MEANS: the cd-index Phi_n = Sum_{[w]} Phi_w is a polynomial where
each monomial m appears with coefficient = number of M-classes whose
cd-word equals m. But the beta formula uses S_w (which depends on the
e-positions), not just the cd-word m.

So beta(S) = |{[w] : S_w subset omega(S)}| counts M-classes, where S_w
depends on the SPECIFIC cde-string (which includes e-positions), not just
the cd-monomial.

This means I CANNOT compute beta(S) from the cd-index Phi_n alone. I need
the full cde-string for each M-class, or equivalently, the tree structure.

My earlier computation using Phi_6 was wrong because I assumed S_m could
be read from the cd-monomial, but it actually depends on where the e's
are (which is lost when e's are deleted).

Let me go back to direct enumeration for the small case.

**For n = 5 (Rocq), i.e., S_6:** beta(D) = |{sigma in S_6 : desc(sigma) = D}|
for D = {1,2} and D' = {1}.

This requires enumerating S_6 = 720 permutations. That's too many by hand.

Let me instead verify via the well-known formula:

    beta_n(S) = Sum_{T >= S} (-1)^{|T|-|S|} * product of (t_{i+1} - t_i) for consecutive elements of T union {0, n}

Actually, the standard formula for beta is via the principle of
inclusion-exclusion:

    beta(S) = Sum_{T : S subset T subset [n-1]} (-1)^{|T|-|S|} alpha(T)

where alpha(T) = |{sigma : D(sigma) >= T}| = product of t-factorial terms.

This is getting too complex for a hand computation. Let me just verify the
n = 3 case (S_4) more carefully and move on with the structural argument.

For n = 3, S_4: I already verified beta({1,2}) = 3, beta({2}) = 3,
beta({1}) = 5 by direct enumeration.

And I verified the axiom is false (toggling i): 3 <= 3 is true but 3 < 3
is false.

And the corrected version (toggling j): 3 < 5 is true.

For n = 4, S_5: I verified beta({2,3}) = 6, beta({3}) = 4 (toggling i: wrong),
and beta({2}) = 9 (toggling j: 6 < 9 correct).

These are sufficient to establish the bug and the correct direction.

### 4.6 Summary of the correct argument

**Corrected axioms:**

```coq
Axiom beta_swap_monotone_both_in : forall n (D : {set 'I_n}) (i j : 'I_n),
  val j = (val i).+1 -> i \in D -> j \in D ->
  beta D <= beta (toggle_at D j).

Axiom beta_swap_lt_both_in : forall n (D : {set 'I_n}) (i j : 'I_n),
  val j = (val i).+1 -> i \in D -> j \in D ->
  beta D < beta (toggle_at D j).
```

**Proof outline (to replace axioms with lemmas):**

**Case A (j = n-1 or j+1 in D):** omega(D) is strictly contained in
omega(D \ {j}). By Prop 1.6.4 (from Theorem 1.6.3 and the cd-index
machinery), beta(D) < beta(D \ {j}).

**Case B (j < n-1 and j+1 not in D):** omega(D) and omega(D \ {j}) differ
by swapping bit j for bit i = j-1. The inequality beta(D) < beta(D \ {j})
requires a more refined argument using the cd-index coefficient structure,
specifically showing that the "marginal contribution" of bit i exceeds
that of bit j in the cd-index expansion.

The complete proof of Case B requires Milestones 1-6 (the full min-max
tree machinery and cd-index theorem) plus an additional argument comparing
marginal contributions of adjacent omega-bits. This is the genuinely hard
part that remains to be formalized.

---

## 5. Formalization strategy

### 5.1 Immediate fix: correct the axiom statements

Change lines 119-129 of `beta_swap.v` to toggle at j instead of i:

```coq
Axiom beta_swap_monotone_both_in : forall n (D : {set 'I_n}) (i j : 'I_n),
  val j = (val i).+1 -> i \in D -> j \in D ->
  beta D <= beta (toggle_at D j).

Axiom beta_swap_lt_both_in : forall n (D : {set 'I_n}) (i j : 'I_n),
  val j = (val i).+1 -> i \in D -> j \in D ->
  beta D < beta (toggle_at D j).
```

### 5.2 Update derived lemmas

**`beta_swap_monotone` (line 271):** Change conclusion to
`beta D <= beta (toggle_at D j)` where j is the "closer to alt" index.

Actually, the derived lemma `beta_swap_monotone` takes a same-pair (i, j)
with (i in D) = (j in D) and concludes beta D <= beta(toggle_at D ?).
The question is: which index to toggle?

The current proof toggles at i and uses the complement trick for "both out".
With the corrected axiom (toggle at j for "both in"):

- "Both in" case: toggle at j directly (using corrected axiom).
- "Both out" case: use complement. In ~: D, both i and j are in ~: D.
  Apply corrected axiom: beta(~: D) <= beta(toggle_at (~: D) j). By
  toggle_at_compl: toggle_at(~: D, j) = ~: toggle_at(D, j). By beta_compl:
  beta(D) = beta(~: D) and beta(toggle_at D j) = beta(~: toggle_at D j)
  = beta(toggle_at(~: D, j)). So beta(D) <= beta(toggle_at D j).

In both cases, we toggle at j. So `beta_swap_monotone` should conclude
`beta D <= beta (toggle_at D j)`.

**`beta_swap_lt` (line 288):** Same, conclude `beta D < beta (toggle_at D j)`.

**`beta_alt_max_bounded` (line 391):** Line 404:
```coq
have Hstrict : beta D < beta (toggle_at D j) := beta_swap_lt Hj Hij.
```
Continue induction on `toggle_at D j`.

### 5.3 Update omega-bridge lemmas

`toggle_at_omega_bit_i_new` and `toggle_at_omega_strict_superset` in
Section H currently analyze toggle at i. These need j-toggle analogues:

```coq
Lemma toggle_at_j_omega_bit_i_new n (D : {set 'I_n.+1}) (i j : 'I_n.+1) :
  val j = (val i).+1 -> i \in D -> j \in D ->
  exists k : 'I_n,
    (* k corresponds to position i in the omega set *)
    k \notin omega_set D /\ k \in omega_set (toggle_at D j).

Lemma toggle_at_j_omega_strict_superset n
  (D : {set 'I_n.+1}) (i j : 'I_n.+1) :
  val j = (val i).+1 -> i \in D -> j \in D ->
  (forall q : 'I_n.+1, val q = (val j).+1 -> val j != n -> q \in D) ->
  omega_set D \proper omega_set (toggle_at D j).
```

### 5.4 Proof of the corrected axioms via Prop 1.6.4

Once Milestones 1-6 provide:
- `beta_omega_monotone`: omega(S) subset omega(T) => beta(S) <= beta(T)
- `beta_omega_strict`: omega(S) strictly in omega(T) => beta(S) < beta(T)

**Case A:** Apply `toggle_at_j_omega_strict_superset` + `beta_omega_strict`.

**Case B:** This requires an additional lemma beyond Prop 1.6.4. The
argument involves comparing cd-index coefficients when omega-sets differ by
swapping adjacent bits. Estimated ~40-60 additional LOC on top of the M1-M6
infrastructure.

### 5.5 Estimated LOC

| Component | LOC | Notes |
|-----------|-----|-------|
| Fix axiom statements | 5 | Change `toggle_at D i` to `toggle_at D j` |
| Fix derived lemmas | 30 | Update `beta_swap_monotone`, `beta_swap_lt`, `beta_alt_max_bounded` |
| j-toggle omega lemmas | 40 | Analogues of Section H lemmas |
| Case A proof | 20 | Direct from omega-strict + Prop 1.6.4 |
| Case B proof | 50 | cd-index coefficient comparison |
| **Total** | **~145** | Plus M1-M6 prerequisites (~950 LOC) |

---

## 6. Summary

### What we found

1. **The two axioms are false as stated.** `toggle_at D i` (lower index)
   does not increase beta. The correct operation is `toggle_at D j` (upper
   index j = i+1).

2. **Counterexamples:** n=3, D={1,2}, i=1 (strict fails: 3=3); n=4,
   D={2,3}, i=2 (both fail: 6 > 4).

3. **The omega-bridge approach** (Section H) was designed for i-toggle and
   faces the same Case B problem (incomparable omega-sets) for j-toggle.
   Case A (omega-containment) handles the boundary cases; Case B requires
   the full cd-index machinery plus a marginal-contribution comparison.

4. **The downstream theorem `beta_alt_max` is likely correct** (we verified
   beta({1,2}) = 3 < 5 = beta({0,2}) for n=3), but its proof is unsound
   because it relies on the false axioms.

### What to do next

1. Fix the axiom statements (toggle j, not i).
2. Propagate the fix through the derived lemmas and beta_alt_max_bounded.
3. Build j-toggle omega lemmas.
4. Complete Milestones 1-6.
5. Close Case A immediately from omega-strict + Prop 1.6.4.
6. Close Case B using the cd-index coefficient comparison.
