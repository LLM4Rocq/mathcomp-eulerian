# Plan: Stanley EC1 §1.3 (Cycles and Inversions)

> **Status snapshot — Session 1 (2026-05-01).** Phases 1, 2, and 6
> partially landed; Phases 3-5 not yet started.  Specifically:
>
> - Phase 1 (`cycles.v`) — definitions + `stirling_c_row_sum_fact`
>   landed; **Stirling recurrence deferred** (needs the
>   `lift_perm`-based cycle-count change argument, ~150–200 LOC).
> - Phase 2 (`inversions.v`) — `inv`, `maj` definitions + `inv_id`,
>   `maj_id` landed; **bounds and reversal symmetry deferred**.
> - Phase 6 — blueprint chapter `ch_inversions.tex` landed and
>   published with the rest.
>
> Both Stirling-recurrence and Foata's-bijection work were attempted in
> the autonomous run but proved to be tasks that need *interactive*
> work with iterative `rocq_check` testing — too much risk in a
> single autonomous burst (each helper bijection has subtle
> correctness invariants).  Honest scope re-estimate at the end of
> this document.

## 0. Session-1 wrap-up — three-agent analysis of the Stirling rec

A second autonomous session attempted Phase 1's hardest piece, the
Stirling cycle-number recurrence

```
stirling_c n.+1 k.+1 = n * stirling_c n k.+1 + stirling_c n k.
```

A team of three subagents (mathematician / Rocq expert / devil's
advocate) was launched in parallel to scope the proof.  Their
converged conclusion is preserved in
[`/workspace/cycles_rec.v`](../../cycles_rec.v) (architecture sketch,
**not in `_CoqProject`** to preserve the main project's
"0 axioms 0 admits" invariant).  The headlines:

- **Strategy.** Use `porbits_mul_tperm` (mathcomp `perm.v`) which
  governs cycle-count change under multiplication by a transposition.
  This avoids reproving cycle-count change from the porbit
  decomposition for every case.

- **Two helper lemmas needed:**
  - **H1**: `cycle_count (perm.lift_perm ord_max ord_max s) =
    (cycle_count s).+1` — extending with a fixed point adds one cycle.
  - **H2**: `cycle_count (perm.lift_perm ord_max j s) =
    cycle_count s` for `j ≠ ord_max` — inserting into an existing
    cycle preserves the count.

  H2 follows from H1 plus `porbits_mul_tperm` once we have the right
  conjugation/decomposition relating `perm.lift_perm ord_max j s` to
  `perm.lift_perm ord_max ord_max s`.  H1 is the harder one; it
  needs an explicit `porbits` decomposition into a singleton
  `[set ord_max]` and `lift ord_max @: P` images of the `porbits s`.

- **Severe gotcha — `lift_perm` shadowing.**  `perm_compress.v`
  defines its own `lift_perm` with a different signature.  In any
  file that imports `perm_compress`, mathcomp's must be qualified as
  `perm.lift_perm`, `perm.lift_perm_id`, `perm.lift_perm_lift`.
  This trips up casual rewrites; ~30 minutes of confusion in the
  first attempt before recognized.

- **Estimated effort.**  Devil's advocate: 1-3 working days for the
  full recurrence + Foata.  Both Stirling-rec and Foata are tasks
  that need *interactive* `rocq_step_multi` iteration — autonomous
  attempts in a single session have a high probability of churning
  on subtle orbit/cycle invariants.

The path forward is documented in `cycles_rec.v` as a scaffold for
the next interactive session.

## 1. Scope

Stanley EC1 §1.3 covers four self-contained topics that compose naturally
with the existing `descent.v` / `eulerian.v` / `beta.v` chain:

| § | Topic | Stanley result |
|---|-------|----------------|
| §1.3.1 | Cycle representation of permutations; cycle type | Definition of `c(w)` (number of cycles); Stirling cycle numbers `c(n, k)` |
| §1.3.2 | Counting permutations by cycle structure | Stirling recurrence `c(n+1, k) = n·c(n, k) + c(n, k-1)`; row sum `∑_k c(n, k) = n!` |
| §1.3.3 | Inversions: `inv(w) = #{(i,j) : i < j ∧ w(i) > w(j)}` | Equidistribution `inv ≡ maj` via Foata's bijection |
| §1.3.4 | q-analog of factorial | `[n]_q! = ∏_{k=1}^n (1 + q + … + q^{k-1})` is the generating function for both `inv` and `maj` over `S_n` |

The headline of §1.3 is the **classical inv/maj equidistribution** (going back
to MacMahon, with Foata's beautiful bijective proof).  Combined with the
Eulerian/Stanley work we already have, this gives the trio
`des / inv / maj` that's the foundation of permutation enumeration.

## 2. What's already in place

**From `descent.v` / `eulerian.v` / `beta.v`:**
- `is_descent s i`, `descent_set s : {set 'I_n}`, `des s` — descents (Stanley §1.4).
- `eulerian n k` — descent-number distribution.
- `beta D` — set-refined descent count.
- `rev_perm s` — order-reversing permutation, used for `des(rev) = n - des(s)`
  (we'll mirror this for `inv`).

**From mathcomp (no new dev needed):**
- `porbit s x : {set T}` — the orbit of `x` under `s` (i.e., the cycle
  through `x` in the cycle decomposition).
- `porbits s : {set {set T}}` — the full cycle decomposition as a set
  partition; lemmas in `mathcomp/algebra/perm.v`.
- `porbits_setP`, `card_porbit_neq0`, `eq_porbit_mem`, etc.

So the cycle side of §1.3 is mostly *naming* mathcomp lemmas in
Stanley's vocabulary; the inversion/maj side is genuinely new.

## 3. File topology

Three new files, all leaves on the existing dependency graph:

```
ordinal_reindex.v
   └─ perm_compress.v
        └─ descent.v ─────────────── eulerian.v ──── beta.v ─── beta_swap.v
              │                          (existing)
              ├─→ inversions.v          [NEW §1.3.3-4]
              │
              └─→ cycles.v              [NEW §1.3.1-2]

[NEW] foata.v                          (depends on descent.v + inversions.v)
   └─ Foata's bijection + the inv-maj equidistribution theorem.
```

| New file | Contents | Stanley reference | Estimated LOC |
|----------|----------|-------------------|---------------|
| `cycles.v` | `cycle_count s := #|porbits s|`, Stirling cycle numbers `stirling_c n k`, recurrence, row sum | §1.3.1 + §1.3.2 | ~350 |
| `inversions.v` | `is_inv s i j`, `inv_set s : {set 'I_n × 'I_n}`, `inv s : nat`, `maj s := \sum_(i in descent_set s) val i.+1`, basic identities | §1.3.3 first half | ~400 |
| `foata.v` | Foata's first/second fundamental bijection; `inv ≡ maj` over `S_n` (equidistribution); q-factorial generating function | §1.3.3-4 | ~700 |

**Total new code:** ~1450 LOC across 3 files.  None of the new files
touch existing files; the refactor is purely additive.

## 4. Per-file outline

### 4.1 `cycles.v`

**Definitions:**
- `cycle_count (s : {perm 'I_n}) : nat := #|porbits s|`.
- `Definition stirling_c : nat -> nat -> nat` — fuel-recursive on the
  Stirling cycle recurrence.

**Theorems:**
- `cycle_count_id : cycle_count (1 : {perm 'I_n}) = n` (identity has `n`
  fixed points = `n` singleton cycles).
- `cycle_count_card_sum : ∑_(s : {perm 'I_n}) k^(cycle_count s) =
   ∏_(i < n) (k + i)` — Stanley's Cor 1.3.6 (rising factorial).
- `stirling_c_rec : c(n+1, k) = n * c(n, k) + c(n, k-1)`.
- `stirling_c_row_sum : ∑_k c(n, k) = n!`.
- `stirling_c_eq_count : c(n, k) = #|{s : {perm 'I_n} | cycle_count s == k}|`
  — the connection between Stirling numbers and cycle distributions.

**Risks:**
- The Stirling recurrence proof needs an "insert max into a cycle"
  bijection analogous to `insert_max_perm` in `eulerian.v`.  Should be
  cleaner because we're inserting into a fixed-point cycle rather than
  reasoning about descents.
- mathcomp's `porbits` is a `{set {set T}}`, not a `seq`; its cardinality
  fits well with `\sum`.

### 4.2 `inversions.v`

**Definitions:**
- `is_inv (s : {perm 'I_n}) (i j : 'I_n) : bool := (i < j) && (s j < s i)`.
- `inv_set s : {set 'I_n * 'I_n} := [set ij | is_inv s ij.1 ij.2]`.
- `inv s : nat := #|inv_set s|`.
- `maj s : nat := \sum_(i in descent_set s) val i.+1` — Stanley's major index.
  (The `+1` corrects for our 0-indexing: Stanley's positions are `1..n-1`.)

**Theorems:**
- `inv_id : inv 1 = 0` and `maj_id : maj 1 = 0`.
- `inv_le : inv s <= 'C(n, 2)` and `maj_le : maj s <= 'C(n, 2)` —
  upper bounds.
- `inv_rev_perm : inv (rev_perm s) = 'C(n, 2) - inv s` — reversal flips
  inversions (mirrors `des_rev_perm` in `descent.v`).
- `maj_rev_perm` — analogous statement for major index.
- `inv_max : inv (rev_perm 1) = 'C(n, 2)` (max inv is the order-reversing
  perm).
- `maj_max : maj (rev_perm 1) = 'C(n, 2)` (same).

**Risks:**
- The upper bound `'C(n, 2)` requires the binomial library
  (already imported in `eulerian.v`).
- The `maj` definition requires summing over `{set 'I_n}`; mathcomp's
  `\sum` over finsets is standard.

### 4.3 `foata.v`

This is the substantive file; it builds **Foata's first fundamental
bijection** `φ : S_n → S_n` characterized by `inv(w) = maj(φ(w))` and uses
it to prove inv-maj equidistribution.

**Definitions:**
- `foata_first : {perm 'I_n} -> {perm 'I_n}` — recursively defined on
  the rightmost letter.
- `foata_second : {perm 'I_n} -> {perm 'I_n}` — Stanley's "Foata's second
  bijection" (the one used in §1.3.3 directly).

**Theorems:**
- `foata_first_inv_maj : inv s = maj (foata_first s)`.
- `foata_first_bij : bijective foata_first` (in fact: involution).
- **Headline:** `inv_maj_equidistr : ∀ k,
   #|{s : {perm 'I_n} | inv s == k}| = #|{s : {perm 'I_n} | maj s == k}|`
   — Stanley's classical result, MacMahon's equidistribution.
- **q-factorial corollary:**
  `inv_q_fact : ∑_(s : {perm 'I_n}) q^(inv s) = ∏_(i < n) (∑_(j < i.+1) q^j)`
   in `int[q]` (or `nat[q]`).  Same statement holds for `maj` by
   equidistribution.

**Risks (medium-to-high):**
- Foata's bijection is intricate to formalize cleanly.  The first
  bijection has a nice recursive structure (insert last letter, do an
  inversion-recording dance); the second is more elegant
  combinatorially but harder to state.  Plan A: prove Foata first, then
  derive equidistribution.  Plan B (fallback): prove equidistribution
  via generating functions without an explicit bijection — needs
  `mathcomp-analysis` or a hand-rolled `nat[q]` polynomial type.
- The q-factorial generating function lives in `nat[q]` or `int[q]`;
  we could either import a polynomial library or stick to the
  cardinality identities and skip the formal q-version.

## 5. Effort estimate

| Phase | Content | Estimate |
|-------|---------|----------|
| Phase 1 | `cycles.v` — definitions + Stirling recurrence | 1 week |
| Phase 2 | `inversions.v` — defs + bounds + reversal symmetry | 1 week |
| Phase 3 | `foata.v` — Foata's first bijection | 2 weeks |
| Phase 4 | `foata.v` — inv-maj equidistribution | 1 week |
| Phase 5 | Optional — q-factorial generating function | 1 week (skippable) |
| Phase 6 | Blueprint chapter `ch_inversions.tex` | 2 days |

**Total:** 5–6 weeks single-developer for §1.3 cycles + inversions +
equidistribution.  Optional q-factorial adds another week.

## 6. Risks and walls

- **Foata's bijection is the hardest part.**  Plan A (explicit
  bijection) gives the most informative formalization but the proof is
  long.  Plan B (generating functions via Worpitzky-style inversion)
  re-uses the technique that worked for `eulerian_explicit`.
- **No proof-term blowup expected.**  Unlike the cd-index work, all the
  proofs here stay at the level of finite-set cardinalities and basic
  counting; no `psi`-style fuel-Fixpoints, no tree-shape inductions.
- **mathcomp gap.**  We may need to upstream a small lemma about
  `porbits` if Stanley's framing doesn't match the mathcomp
  formulation.  Should be a minor patch.
- **Blueprint maintenance.**  Adding a new chapter means new
  `\rocq{...}` cross-refs to maintain (~30–40 new declarations).

## 7. What this *doesn't* cover

This plan stops at §1.3.  The natural next extensions, in order of
adjacency:

- **§1.6.2 — Longest alternating subsequences** (extends `beta_alt_max`).
- **§1.6.4 — André reflection method** (alternative proof of the Euler
  number formula).
- **§1.4 q-Eulerian polynomials** (combines inversions + descents).

Stay away from §1.5 (RSK / Young tableaux) and §1.8 (partition
identities) for now — those are major projects in their own right and
overlap with `mathcomp-extra`.

## 8. Build / verification gates

Each phase ends with the standard gates:

```bash
make clean && make -j2                                   # full .vo build
coqchk -R . mathcomp_eulerian mathcomp_eulerian.foata    # axiom-free
echo 'From mathcomp_eulerian Require Import foata. \
      Print Assumptions inv_maj_equidistr.' \
  | rocq top -R . mathcomp_eulerian
# expected: "Closed under the global context"
```

## 9. Repository diff at completion

```
_CoqProject                       +3 entries
cycles.v                          new (~350 LOC)
inversions.v                      new (~400 LOC)
foata.v                           new (~700 LOC)
PROOF_STATEMENTS.md               +1 section
FORMAL_VS_STANLEY.md              +entries for §1.3
blueprint/src/ch_inversions.tex   new chapter
blueprint/src/content.tex         +1 \input line
README.md                         minor update
```
