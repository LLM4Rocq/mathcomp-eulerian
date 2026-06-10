# Reading Guide for Mathematicians

> **Audience.** A combinatorialist who knows Stanley *Enumerative
> Combinatorics I* (EC1) and wants to verify or build on the formal
> statements in this repository. You do **not** need to read mathcomp
> idioms or tactics — this guide tells you exactly which lines to look
> at and how to translate the types back to ordinary mathematics.

## What this document covers

1. The single big convention shift: 0-indexing.
2. How our types map to Stanley's notation.
3. A worked example: take Stanley's permutation `[3, 1, 4, 2]` and
   trace it through our formal definitions.
4. How to use the rest of the repository: blueprint, definitions
   audit, source files.

If you only have 5 minutes, read §3 (the worked example).

---

## 1. Indexing convention — the single thing to internalize

**Stanley uses 1-based indexing. We use 0-based.**

| Stanley | Us |
|---------|------|
| Permutation of `[n] = {1, ..., n}` | Permutation of `'I_n = {0, ..., n-1}` |
| Position `i ∈ {1, ..., n}` | Position `i : 'I_n` (i.e., `i ∈ {0, ..., n-1}`) |
| Descent at position `i` if `w_i > w_{i+1}`, with `i ∈ {1, ..., n-1}` | Descent at position `i : 'I_n` if `s(i) > s(i+1)`, with `i ∈ {0, ..., n-1}` |
| Descent set `D(w) ⊆ {1, ..., n-1}` | `descent_set s : {set 'I_n}` |
| Inversion = pair `(i, j)` with `i < j` and `w_i > w_j` | Same, with `i, j : 'I_n.+1` |

**Implication for off-by-ones.** Stanley says `S_n` for permutations
of `n` elements; the descent-set lives in subsets of `{1, ..., n-1}`,
so its parameter is `n - 1`. In our code, when we declare
`Variable n : nat` and write `{perm 'I_n.+1}`, our `n` is **already**
"Stanley's `n` minus 1." So our `n` is the maximum valid descent
position; Stanley's `n` is `our n + 1` = the number of elements.

Or, said directly:

> **Our `{perm 'I_n.+1}` = Stanley's `S_{n+1}`.**

If you want Stanley's `S_n`, write `{perm 'I_n}` (no `.+1`).

---

## 2. Type translation table

| Stanley | Us | Notes |
|---------|------|-------|
| `S_n` (permutations of `n` elements) | `{perm 'I_n}` | Often appears as `{perm 'I_n.+1}` for Stanley's `S_{n+1}` (positions 0..n have n descent slots) |
| `w = (w_1, ..., w_n)` | `s : {perm 'I_n.+1}`, treated as a function `'I_n.+1 → 'I_n.+1` | Apply with `s i` |
| `D(w)` (descent set) | `descent_set s` | A `{set 'I_n}` |
| `des(w)` (descent count) | `des s = #\|descent_set s\|` | `nat` |
| `inv(w)` (inversion count) | `inv s` | `nat` |
| `maj(w) = ∑_{i ∈ D(w)} i` | `maj s = ∑_{i ∈ descent_set s} (val i + 1)` | `(val i + 1)` shifts our 0-indexed `i` back to Stanley's 1-indexed |
| `c(w)` (cycle count) | `cycle_count s` | `nat`; uses mathcomp's `porbits` |
| `S ⊆ {1, ..., n-1}` | `S : {set 'I_n}` | `'I_n` is the finite type `{0, ..., n-1}` |
| `β_n(S)` (count perms with descent set exactly `S`) | `beta D` | `nat`; takes `D : {set 'I_n}` |
| `A(n, k)` (Eulerian number) | `eulerian (n-1) k` | **Off-by-one!** Our `eulerian n k` counts perms of `'I_n.+1` (i.e., `n+1` elements) with `k` descents. So Stanley's `A(n, k) = our eulerian (n-1) k`. |
| `c(n, k)` (Stirling cycle number) | `stirling_c n k` | Direct match: counts perms of `'I_n` with `k` cycles. |

### Permutation as function vs. sequence

Stanley sometimes writes `w = (w_1, ..., w_n)` and sometimes
`w : [n] → [n]`. We always use the function form:

- `s : {perm 'I_n.+1}` is a *bijection* `'I_n.+1 → 'I_n.+1`.
- `s i` is the value at position `i`.
- mathcomp's `{perm T}` is the sigma-type of `T → T` paired with a
  proof of bijectivity. For our purposes, it behaves exactly like a
  permutation.

---

## 3. Worked example

Take Stanley's permutation `w = [3, 1, 4, 2] ∈ S_4`. (Stanley would
write the values as `w_1 = 3, w_2 = 1, w_3 = 4, w_4 = 2`.)

### As Rocq

In our code, `w` is a `{perm 'I_4}`. Concretely:

```
s 0 = 2     (Stanley's w_1 = 3 → 0-indexed value 2)
s 1 = 0     (Stanley's w_2 = 1 → 0-indexed value 0)
s 2 = 3     (Stanley's w_3 = 4 → 0-indexed value 3)
s 3 = 1     (Stanley's w_4 = 2 → 0-indexed value 1)
```

We shift values by 1 too (Stanley's `{1, 2, 3, 4}` → our `{0, 1, 2, 3}`),
so `w_i` becomes `s (i-1) = w_i - 1`. Stanley's "3 1 4 2" becomes our
"2 0 3 1". Our `n = 3` (since we'd use `{perm 'I_4} = {perm 'I_n.+1}`
with `n = 3`).

### Descent set

**Stanley:** `D(w) = {i : w_i > w_{i+1}} = {1, 3}` because
`w_1 = 3 > 1 = w_2` and `w_3 = 4 > 2 = w_4`.

**Our code:** look at `is_descent` in `descent.v:22-23`:

```coq
Definition is_descent s i : bool :=
  s (widen_ord (leqnSn n) i) > s (lift ord0 i).
```

For `i : 'I_3` (positions 0, 1, 2):
- `i = 0`: `s 0 > s 1` → `2 > 0` ✓ descent.
- `i = 1`: `s 1 > s 2` → `0 > 3` ✗ ascent.
- `i = 2`: `s 2 > s 3` → `3 > 1` ✓ descent.

So `descent_set s = {0, 2} : {set 'I_3}`. **Translation:** add 1 to
each element, get `{1, 3}` — matches Stanley.

### des, inv, maj

| Statistic | Stanley value | Our value | Verify |
|-----------|---------------|-----------|--------|
| `des(w)` | 2 | `des s = #\|{0, 2}\| = 2` | ✓ |
| `inv(w)` | 3 | `inv s = 3` | pairs `(1,2): 3>1`, `(1,4): 3>2`, `(3,4): 4>2` |
| `maj(w)` | `1 + 3 = 4` | `maj s = (0+1) + (2+1) = 4` | The `(val i + 1)` in `inversions.v:81` shifts back |

### Cycles

**Stanley:** `w = (1, 3, 4, 2)` written cycle-wise: 1→3, 3→4, 4→2,
2→1. One cycle. `c(w) = 1`.

**Our code:** `cycle_count s = #|porbits s|`. The orbit of 0 is
{0, 2, 3, 1} = all of `'I_4`, so `cycle_count s = 1`. ✓

---

## 4. How to use the rest of the repository

### Layered access

| If you want to... | Read this |
|-------------------|-----------|
| Verify a single definition | `docs/DEFINITIONS_AUDIT.md` (side-by-side Stanley/Rocq) |
| Read the math expository, with hyperlinks to formal results | The HTML blueprint at `blueprint/web/index.html` (or the deployed [GitHub Pages site](https://llm4rocq.github.io/mathcomp-eulerian/)) |
| See the actual proof of a result | The `.v` source file (linked from blueprint via `\rocq{...}`) |
| Understand which Stanley sections are formalized | `PROOF_STATEMENTS.md` |
| Find historical/planning context | `docs/internal/` and `docs/plans/` |

### Recommended reading order

1. **This guide** (you are here) — 10 minutes.
2. **`DEFINITIONS_AUDIT.md`** — 30-60 minutes. Verify the
   25 definitions translate as you expect; flag any that don't.
3. **The blueprint** for the theorems and proofs at the level you
   want.
4. **The `.v` files** only when you need to verify a specific proof.

### Source files quick map

| File | Stanley topic | Status |
|------|---------------|--------|
| `descent.v` | §1.4 — descents, descent set | ✅ |
| `eulerian.v` | §1.4 — Eulerian numbers `A(n, k)` | ✅ |
| `beta.v` | §1.4 — set-refined count `β_n(S)` | ✅ |
| `inversions.v` | §1.3.3 — `inv`, `maj` | ✅ |
| `cycles.v` | §1.3.1, §1.3.2 — cycles, Stirling `c(n, k)` | ✅ |
| `cycles_rec.v` | §1.3.2 — Stirling cycle recurrence | ✅ |
| `stirling_fiber.v` | §1.3.2 — algebraic decomposition route | ✅ |
| `foata.v` | §1.3.4 — Foata bijection, `inv ≡ maj` | ✅ |
| `qfact.v` | §1.4 — q-factorial generating function | ✅ |
| `qeul.v` | §1.4 — q-Eulerian polynomial `A_n(q, t)` | ✅ |
| `altsub.v` | §1.6.2 — longest alternating subsequence | ✅ |
| `beta_omega.v` | §1.6.3 — toggle action `ω` | ✅ |
| `beta_swap.v` | §1.6.3 — alternating descent set, Stanley Cor 1.6.5 | ✅ |
| `reflection.v` | §1.6.4 — André reflection, `euler_rec` | ✅ |

✅ = kernel-validated, axiom-free, in active build chain.

### Verifying axiom-freeness yourself

In any `.v` file, after a theorem, you can ask:

```coq
Print Assumptions descent.des_id.
(* > Closed under the global context *)
```

"Closed under the global context" means **no axioms or admits are
used** anywhere in the proof's transitive dependencies. The whole
active build chain is axiom-free.

---

## 5. Common gotchas

### Gotcha 1: descent positions vs. permutation positions

The permutation `s : {perm 'I_n.+1}` has `n+1` positions
(`'I_n.+1 = {0, ..., n}`). Descents live between consecutive
positions, so the descent set is in `{set 'I_n}`, not `{set 'I_n.+1}`.
This is why our `n` parameter is "Stanley's `n` minus 1."

### Gotcha 2: `widen_ord` and `lift ord0`

In `descent.v:22-23`:
- `widen_ord (leqnSn n) i` casts `i : 'I_n` to `i : 'I_n.+1` *with the
  same numerical value*. So if `i = 1 : 'I_3`, then
  `widen_ord _ i = 1 : 'I_4`.
- `lift ord0 i` shifts `i : 'I_n` up to `i + 1 : 'I_n.+1`. So if
  `i = 1 : 'I_3`, then `lift ord0 i = 2 : 'I_4`.

Together, `is_descent s i := s i > s (i+1)`, exactly Stanley's
definition of descent.

### Gotcha 3: Eulerian number off-by-one

Stanley writes `A(n, k)` for the number of permutations of `[n]`
with `k` descents. Our `eulerian n k` is the number of permutations
of `'I_n.+1` (i.e., `n+1` elements) with `k` descents. So:

> **`eulerian n k = A(n+1, k)` in Stanley's notation.**

If a theorem in the repo says `eulerian 3 1 = 11`, that's Stanley's
`A(4, 1) = 11`, which you can check in Stanley's table on p.36.

### Gotcha 4: `maj` shifts back to 1-indexed

Stanley defines `maj(w) = ∑_{i ∈ D(w)} i`, summing 1-indexed
positions. Our descent set has 0-indexed positions, so `maj s` adds
1 to each element of the sum:

```coq
Definition maj s : nat := \sum_(i in descent_set s) (val i).+1.
```

`(val i).+1` is `i + 1`, restoring Stanley's 1-indexing.

---

## 6. Where to flag concerns

If, during your audit, you find:

- A definition that doesn't match Stanley → file an issue or PR
  against `DEFINITIONS_AUDIT.md` with the discrepancy.
- A theorem statement you suspect is wrong → check the proof or
  look at small cases (`Compute` sometimes works, otherwise
  hand-verify on `n = 2, 3, 4`).
- A convention that's unclear → propose an addition to this guide.

The repo is set up to make *the math the audit*; the proofs are
just kernel-checked compositions of the audited definitions. If the
definitions are right, the rest is mechanical.
