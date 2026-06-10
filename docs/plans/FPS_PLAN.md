# Formal Power Series (FPS) Plan — modular GF library + Stanley generating-function results

**Decisions taken** (maintainer, 2026-06-10): `mathcomp-classical` is
allowed (the audience is mathematicians; standard classical axioms are
fine); the library lives in a **subdirectory now** (split-out later);
license **Apache-2.0** (same as the host repo); phase order after
phase 1 is **2 → 3 → 4**; phase-3 demos are **#1 (exp/log round-trip on
the geometric series) and #2 (Stirling-cycle EGF)** — Bell numbers
dropped.

**Status (2026-06-10): PHASE 1 COMPLETE** — `fps/` (fps.v, fps_deriv.v,
fps_egf.v, fps_trig.v, fps_ode.v) and `stanley_egf.v` all land with 0
admits; `Print Assumptions stanley_1_6_1` = the classical trio.
**PHASE 2 COMPLETE** (same day) — `worpitzky.v` (axiom-free Worpitzky +
`coef_eul_pol`), `fps/fps_ogf.v` (negative binomial), `stanley_ogf.v`
(`stanley_1_4`, the §1.4 Eulerian OGF over `{fps int}`).
**PHASE 3 COMPLETE** — `fps/fps_comp.v` (composition + chain rule, via
the truncation bootstrap to `\Po`), `fps/fps_explog.v` (exp/log group
laws over com-unit-rings with invertible naturals; demo #1
`exp(log (1−x)⁻¹) = (1−x)⁻¹`), `stirling_egf.v` (demo #2,
`stirling_cycle_egf : Σ (Σ c(n,k)tᵏ) xⁿ/n! = (1−x)^(−t)` over
`{fps {poly rat}}`).
**PHASE 4 PART 1 COMPLETE** — `qbin.v` (Gaussian binomials, axiom-free,
q-Pascal + q=1 specialization) and `carlitz.v` (`q_staircase`: the
Carlitz denominator `Π(1−qⁱx)` inverted by the Gaussian-binomial gf,
over `{fps {poly int}}`).
**PHASE 4 PART 2 COMPLETE** — `qeul_rec.v` (axiom-free: maj of an
insertion from the descent-set lemmas, rank sums producing q-integers,
`q_eulerian n k` and the Carlitz recurrence
`B(n+1,k+1) = [k+2]_q B(n,k+1) + q^(k+1)[n+1-k]_q B(n,k)` via the
insert-max bijection with `q^maj` weights), `qworpitzky.v` (axiom-free:
q-integer/Gaussian-binomial calculus incl. the complementary absorption
`[k+1][n,k+1] = [n-k][n,k]`, the q-Pascal splitting step, `q_worpitzky`,
`coef_q_eul_pol`), and the final packaging in `carlitz.v`:
`carlitz : (Σ_m ([m+1]_q)^(n+1) x^m) · Π_(i<n+2)(1−qⁱx) = q_eul_pol n`
over `{fps {poly int}}` (+ division/inverse forms).  **The FPS plan is
fully delivered**; remaining ideas (Lagrange inversion, library
split-out, truncated companion) are stretch items below.

**Phase-1 headline.** Stanley EC1, **Proposition 1.6.1**: the exponential
generating function of the Euler numbers,

```
  ∑_n E_n x^n / n!  =  sec x + tan x
```

as an identity of *formal* power series (no analysis), with `E_n` our
`eulerA n` (`reflection.v`), so it plugs directly into the proved André
recurrence `euler_rec`.

**Later phases (explicitly wanted, planned below).**
Stanley §1.4 OGF identities (Worpitzky / `∑_m (m+1)^n x^m =
A_n(x)/(1−x)^{n+1}`), composition + exp/log + exponential-formula
material, and q-analogue hooks connecting `qfact.v` / `qeul.v`
(Carlitz's q-Worpitzky as the anchor).

**Standing goal.** The FPS layer is **modular and reusable**: a
self-contained sub-library `fps/` depending only on mathcomp (+
`mathcomp-classical`), with its own namespace, no imports from the
eulerian development, extractable later into a standalone repo / opam
package.

---

## 1. Survey: what exists

### 1.1 hivert/FormalPowerSeries (inspiration, not a dependency)

https://github.com/hivert/FormalPowerSeries — the most developed mathcomp
FPS formalization: `tfps.v` (truncated series, axiom-free, units over any
base ring), `fps.v`/`invlim.v` (full FPS as inverse limits, over
`mathcomp-classical`), `catalan*.v` (six Catalan proofs: algebraic
equation + Newton, Lagrange inversion, holonomic ODE).

Why inspiration only:
1. **Toolchain**: targets mathcomp 2.3 / Coq 8.18–8.20 + `multinomials`;
   we are on Rocq 9.1.1 / mathcomp 2.5.0; not released on opam.
2. **License**: GPL-3.0 vs our Apache-2.0 — *no code copying*; we reuse
   the lemma inventory, API shape, and proof strategies (his holonomic-ODE
   Catalan proof is the blueprint for our sec+tan argument), with citation.
3. His full-FPS layer goes through inverse limits; since we accept
   classical axioms from the start, a **direct construction on sequences
   is simpler** (§2.1) and we skip the truncated layer entirely.

### 1.2 What our toolchain provides (verified 2026-06-10)

- `mathcomp-classical` 1.16 (`boolp.v`): `gen_eqMixin`, `gen_choiceMixin`,
  and — important — **pre-installed eqType/choiceType instances on
  `forall`-types** (`boolp.v:394–398`). So `nat -> R` is already a
  choiceType once `boolp` is imported; a wrapper record for `{fps R}`
  inherits everything needed to mount `GRing` structures. Axioms involved:
  functional/propositional extensionality + constructive indefinite
  description — the same trio mathcomp-analysis uses.
- `mathcomp/algebra/qpoly.v`: `{poly %/ 'X^(n.+1)}` is a com-unit-algebra
  over a field (smoke-tested over `rat`). With classical axioms allowed we
  **don't need it as the carrier**; noted as a fallback/an axiom-free
  companion only.
- `rat` (char-0 field), `int`, `{poly int}` — phase 2/4 work over
  *non-field* coefficient rings, which drives a design choice in §2.2.
- In-repo combinatorial inputs already proved: `euler_rec`
  (`reflection.v`), Eulerian numbers + recurrence (`eulerian.v`),
  Eulerian polynomial `eul_pol` and q-Eulerian `q_eul_pol` (`qeul.v`),
  `inv_q_fact` / `maj_q_fact` (`qfact.v`), Stirling cycle material
  (`cycles_rec.v`, `stirling_fiber.v`).

### 1.3 What mathcomp does not have

No formal exp/sin/cos/sec/tan series, no EGF/binomial-convolution
calculus, no FPS composition or ODE-uniqueness. (`mathcomp-analysis` has
*convergent* series — different object, out of scope.)

---

## 2. Design

### 2.1 Single carrier: `{fps R}` over mathcomp-classical

```coq
Record fps (R : nzRingType) := FPS { fpscoef :> nat -> R }.
Notation "{ 'fps' R }" := (fps R).
Notation "f ``_ n" := (fpscoef f n).
```

- eq/choice: inherited from `boolp`'s instances on `nat -> R` via the
  subtype; equality of series is genuine Leibniz equality (funext turns
  coefficientwise equality into `=`; provide `fpsP : f = g <-> f =1 g`).
- Zmodule: coefficientwise. Ring: Cauchy product
  `(f * g)``_n = \sum_(k < n.+1) f``_k * g``_(n-k)`.
- **Ring-axiom bootstrap trick**: coefficient `n` of any product depends
  only on coefficients `≤ n`, so each axiom (assoc, distr, …) at
  coefficient `n` reduces to the same identity in `{poly R}` for the
  degree-`n` truncations `\poly_(i < n.+1) f``_i`. We reuse mathcomp's
  polynomial ring instead of re-fighting triangular bigop exchanges.
  Expected to shrink the ring-axiom section to ~dozens of lines.
- Algebra structure over `R` (`*:` coefficientwise); `lalgType`/`algType`,
  `comRingType` for commutative `R`.
- **Units over any `comUnitRingType`** (not just fields):
  `f \is a unit  <->  f``_0 \is a unit`, inverse by coefficient
  recursion `g_0 = (f_0)^-1`, `g_{n+1} = -(f_0)^-1 * Σ_{k<n+1} f_{n+1-k} g_k`.
  This generality is *load-bearing*: phase 2 (Worpitzky over `int`) and
  phase 4 (q-series over `{poly int}`) invert series like `1 - q^i x`
  whose base rings are not fields — only the constant coefficient must be
  a unit.
- Polynomial embedding `poly_fps : {poly R} -> {fps R}` (injective ring
  morphism), `'Xf := poly_fps 'X`, valuation basics.

What we *gain* vs the earlier two-layer (axiom-free) draft: a real
`comUnitRingType`/`algType` with the whole `GRing` theory and `ring`-style
rewriting at the FPS level; flat derivative `{fps R} -> {fps R}` (no
dependent truncation indices); no truncation-coherence lemma family.
What we *lose*: nothing needed here (decidability of `=` was never real).

### 2.2 Axiom policy (project-level)

- The **existing combinatorial chain stays 0-axiom** — nothing under the
  current 33 files changes.
- `fps/*` and the bridge files (`stanley_egf.v`, later `worpitzky.v`, …)
  use `mathcomp-classical`'s standard axioms (funext, propext,
  constructive indefinite description). `Print Assumptions` on the new
  headline theorems will list exactly these.
- Docs (`README`, `PROOF_STATEMENTS.md`, formal companion) get a
  per-layer axiom statement: *"core: closed under the global context;
  generating-function layer: classical axioms of mathcomp-classical, as
  in mathcomp-analysis"*. The `coqchk` audit step records the same.
- CI/Docker: add `rocq-mathcomp-classical` to the dependency set
  (already in the local opam switch; `Dockerfile` and
  `.github/workflows/blueprint.yml` need the package added).

### 2.3 Repository layout

```
fps/                      # imports mathcomp + mathcomp-classical ONLY
  README.md               # standalone-ready: scope, axioms, API tour
  fps.v fps_deriv.v fps_egf.v fps_trig.v fps_ode.v        (phase 1)
  fps_ogf.v               (phase 2)
  fps_comp.v fps_explog.v (phase 3)
stanley_egf.v             # main project: bridge files import both sides
worpitzky.v               # (phase 2)  — dependency points one way only
...
# _CoqProject:  -R fps mathcomp_fps  + file entries
```

Apache-2.0 headers throughout `fps/` (same license as host). Split-out
later via `git filter-repo`; opam name to decide at that point
(working name: `rocq-fps`).

---

## 3. Phase 1 — EGF core and Stanley Prop 1.6.1

### 3.1 Mathematical route

1. **Workhorse (EGF calculus).** `egf a := \fps (a n / n`!%:R)` over a
   char-0 field; *binomial convolution = EGF product*:
   `egf a * egf b = egf (fun n => Σ_(k ≤ n) 'C(n,k)%:R * a k * b (n-k))`
   (via `bin_fact`).
2. **Euler ODE.** `A := egf (fun n => (eulerA n)%:R)`. Then `euler_rec`
   + `eulerA 0 = eulerA 1 = 1` give exactly
   `2%:R *: A^` = 1 + A ^+ 2` and `A``_0 = 1`
   (coefficient `n`: LHS `2E_{n+1}/n!`; RHS `[n=0] + Σ C(n,k)E_kE_{n−k}/n!`).
3. **Standard series.** `sinf`, `cosf` by explicit coefficients;
   `secf := cosf^-1` (unit: constant coefficient 1), `tanf := sinf * secf`.
   Facts: `sinf^` = cosf`, `cosf^` = - sinf` (immediate);
   `sinf ^+ 2 + cosf ^+ 2 = 1` by the derivative trick (zero derivative +
   constant term); `y := secf + tanf` satisfies `2%:R *: y^` = 1 + y ^+ 2`,
   `y``_0 = 1` (ring algebra + Pythagoras).
4. **ODE uniqueness** (char-0): solutions of `2 y' = c + y²` with equal
   constant coefficient coincide — strong induction on the coefficient
   index (`2(n+1)%:R` invertible). Try the generic `y' = P(y)`,
   `P : {poly F}` version (reusable, hivert-style); fall back to the
   quadratic instance if dependent-degree bookkeeping fights back.
5. **Conclusion.**
   ```coq
   Theorem stanley_1_6_1 :
     egf (fun n => (eulerA n)%:R) = secf + tanf :> {fps rat}.
   Corollary euler_egf_coef n :
     (eulerA n)%:R = n`!%:R * (secf + tanf)``_n.
   ```
6. **Cheap stretch.** Parity refinement: `secf` even, `tanf` odd ⇒
   secant numbers `E_{2k}` and tangent numbers `E_{2k+1}` (Stanley's full
   statement of 1.6.1).

### 3.2 Files and estimates

(×1.5 history buffer built into the ranges.)

| File | Contents | Est. LOC |
|---|---|---|
| `fps/fps.v` | carrier, eq/choice via boolp, zmod/ring (poly bootstrap), com/algebra, **units over `comUnitRingType`** + inverse recursion, `fpsP`, poly embedding, `'Xf` | 450–650 |
| `fps/fps_deriv.v` | `f^`` (flat), additivity/scaling/**Leibniz**, power rule, primitive (char 0), `derivative 0 + constant ⇒ equal` | 150–250 |
| `fps/fps_egf.v` | `egf`, **binomial-convolution workhorse**, `egf`↔shift↔derivative, factorial/binomial `rat` kit | 200–300 |
| `fps/fps_trig.v` | `expf, sinf, cosf, secf, tanf`; derivatives; Pythagoras; parity; sec+tan ODE | 250–400 |
| `fps/fps_ode.v` | ODE uniqueness (generic `y' = P(y)` or quadratic) | 100–200 |
| `stanley_egf.v` | `euler_rec` ⇒ ODE ⇒ `stanley_1_6_1` + corollaries + parity stretch | 200–350 |

Phase-1 total ≈ **1350–2150 LOC**.

### 3.3 Milestones

- **M0 (½ session)** — scaffolding: `fps/` + `_CoqProject` + CI deps
  (`rocq-mathcomp-classical` in Dockerfile/workflow); `{fps R}` with
  zmodule instance compiling. *Accept: full `make` green.*
- **M1 (1–2 sessions)** — `fps.v` complete: ring via poly bootstrap,
  units over `comUnitRingType`. *Accept: `(1 - 'Xf)^-1` geometric-series
  sanity lemma; no admits.* (Riskiest milestone — front-loaded.)
- **M2 (1 session)** — `fps_deriv.v` + `fps_egf.v`. *Accept: workhorse
  lemma proved generically.*
- **M3 (1–2 sessions)** — `fps_trig.v` + `fps_ode.v`. *Accept:
  Pythagoras + sec/tan ODE + uniqueness.*
- **M4 (1 session)** — `stanley_egf.v` + docs (PROOF_STATEMENTS §18,
  companion chapter, README axiom policy, catalog/PDF regen).
  *Accept: `Print Assumptions stanley_1_6_1` = exactly the classical trio.*

---

## 4. Phase 2 — OGF toolkit and Stanley §1.4 (Worpitzky)

**Headline.**
```coq
Theorem stanley_1_4_worpitzky n :              (* over {fps int} *)
  \fps ((m.+1 ^ n)%:R) * (1 - 'Xf) ^+ n.+1 = poly_fps (eul_pol n).
```
(stated multiplied-out to avoid division; the `A_n(x)/(1−x)^{n+1}` display
form follows since `(1 - 'Xf)` is a unit — constant coefficient `1`, a
unit *in `int`*, which is why §2.1 insists on general unit rings).
`eul_pol` already exists (`qeul.v:68`) with
`sum_des_eq_eul_pol : eul_pol n = Σ_w t^{des w}` — the combinatorial side
is in place.

**New material.**
- `fps/fps_ogf.v`: `ogf`-style helpers; geometric series; **negative
  binomial**: `((1 - 'Xf)^-1) ^+ k.+1 ``_m = 'C(m + k, k)%:R`; coefficient
  calculus for `poly_fps p * f`. (Est. 250–400 LOC.)
- `worpitzky.v` (main project): the combinatorial **Worpitzky identity**
  `(m.+1) ^ n = Σ_k A(n,k) * 'C(m + n - k, n)` — by induction via the
  Eulerian recurrence (`eulerian.v`), or directly from
  `sum_des_eq_eul_pol` by counting (each `w` with `des w = k` injects
  `m+n−k choose n`-many ways — Stanley's barred-permutation argument);
  pick whichever lands first. Then the OGF form by coefficient
  extraction. (Est. 300–500 LOC — the combinatorial identity is the real
  content here.)

*Accept:* both display forms proved; `eulerian.v`/`qeul.v` untouched
(bridge-only).

---

## 5. Phase 3 — composition, exp/log, exponential-formula material

- `fps/fps_comp.v`: composition `f \o g` for `g``_0 = 0` (well-defined
  coefficientwise via finite sums; the `n`-th coefficient only sees
  `g^1..g^n`), associativity-with-conditions, **chain rule**, units/
  inverse interplay. (Est. 400–600 LOC — the hardest single file in the
  whole plan; budget accordingly.)
- `fps/fps_explog.v`: `expf`/`logf` with the group laws
  `expf (f + g) = expf f * expf g` (`f,g` with zero constant term),
  `logf (expf f) = f`, `expf (logf (1 + f)) = 1 + f`; derivative
  characterizations. (Est. 200–300 LOC.)
- Demos / anchors in the main project (decided: #1 and #2):
  1. `expf (logf (1 - 'Xf)^-1) = (1 - 'Xf)^-1` — smoke test;
  2. **Stirling-cycle EGF** (Stanley §1.3): two-variable
     `Σ_{n,k} c(n,k) t^k x^n/n! = (1−x)^{−t}` formalized over
     `{fps {poly rat}}` via the `cycles_rec.v` recurrence — same
     recurrence⇒ODE pattern as 1.6.1, and it exercises non-trivial
     coefficient rings.
  (Bell numbers dropped — would require new set-partition
  combinatorics.)
- The **general exponential formula** (species/assemblies level, EC2
  §5.1) is a research-sized layer (needs a partition-structures
  framework); kept as a separate go/no-go decision after the demos —
  the demos already deliver the working calculus mathematicians use.

(Est. phase total 800–1300 LOC.)

---

## 6. Phase 4 — q-analogue hooks (Carlitz)

Connect `qfact.v` / `qeul.v` to the FPS layer. Everything is series in
`x` with coefficients in `{poly int}` (the `q`-ring) — no new carrier
needed; `{fps {poly int}}` works because units only need unit constant
coefficient (§2.1).

- Bridge `q`-kit: `q_int`, `q_fact`, `q_bin` as elements/identities in
  `{fps {poly int}}`; products `\prod_(i < k) (1 - q^i *: 'Xf)` and their
  inverses.
- **Headline: Carlitz's q-Worpitzky** (q-analogue of phase 2, Stanley
  §1.4 exercises / (1.41)-area):
  ```
  Σ_m ([m+1]_q)^n x^m = q_eul_pol n (x) / Π_{i=0..n} (1 − q^i x)
  ```
  stated multiplied-out over `{fps {poly int}}`, using `q_eul_pol`
  (`qeul.v:41`) and its proved `t=1` / `q=1` specializations as sanity
  corollaries (must recover phase 2's Worpitzky at `q = 1`).
- Stretch: q-binomial theorem `Π (1 + q^i x) = Σ q^{C(k,2)} qbin(n,k) x^k`
  as a finite-product warm-up (polynomial identity, may not even need
  FPS — good first task of the phase).

(Est. 400–700 LOC. The combinatorial q-Worpitzky proof is the unknown;
the `q_eul_pol` recurrence in `qeul.v` is the intended engine.)

---

## 7. Risks and mitigations

| Risk | Mitigation |
|---|---|
| HB instance mounting on a function-type wrapper (universe/coercion quirks with `boolp` instances) | M0 proves out the full instance stack on a toy before anything else; hivert's `fps.v` and mathcomp-analysis's function-space instances are working precedents to *read* (not copy) |
| Cauchy-product ring axioms turn into bigop slogs | poly-truncation bootstrap (§2.1); if a specific axiom resists, prove it directly — `poly.v`'s own proofs are the roadmap |
| inverse-coefficient recursion well-definedness (strong recursion over `nat`) | standard `Fix`/fuel or `nat_rect` on bounded prefixes; uniqueness comes free from ring theory afterwards |
| dependent-degree issues in generic `y' = P(y)` uniqueness | quadratic fallback is fully sufficient for phases 1–3 |
| `rat`/factorial arithmetic noise | one kit section in `fps_egf.v` (`fact_neq0`, `'C(n,k)%:R` fraction, `pchar_rat`) |
| composition (phase 3) is genuinely hard | it is *isolated*: phases 1, 2, 4 do not depend on it; schedule allows reordering 3 ↔ 4 |
| Worpitzky/Carlitz combinatorial identities underestimated | both have two independent proof routes (recurrence induction vs direct counting); phase gates are per-identity, so partial landings still ship the toolkit files |
| axiom-policy drift in docs | M4 includes the doc sweep; `rocq_verify`-style audit text updated once, quoted everywhere else |

---

## 8. Deferred / v-later

- Lagrange–Bürmann inversion + Catalan demo (natural after phase 3).
- Axiom-free truncated companion (`{poly %/ 'X^(n.+1)}`-backed) for users
  who need it — the smoke test shows it's viable; only worth doing on
  demand.
- Generalize EGF beyond fields (ℚ-algebras with explicit `n!`-inverses).
- Upstreaming conversations: hivert (after M3, share the API), mathcomp
  (the units-over-`comUnitRingType` layer is a plausible contribution).

## 9. Remaining open questions

1. Opam package name at split-out time (working name `rocq-fps`).

(Resolved 2026-06-10: phase order 2 → 3 → 4; phase-3 demos #1 and #2.)
