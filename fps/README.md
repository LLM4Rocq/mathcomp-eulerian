# mathcomp_fps — formal power series for combinatorics

A self-contained Rocq/mathcomp library of **formal power series** aimed at
enumerative combinatorics (ordinary and exponential generating functions),
designed to be reusable outside its host repository.

- **Namespace:** `mathcomp_fps` (mapped from this directory).
- **Dependencies:** `rocq-mathcomp-algebra`, `rocq-mathcomp-classical` —
  nothing from the host project; the host's bridge files import this
  library, never the other way around.
- **License:** Apache-2.0 (same as the host repository).
- **Plan / roadmap:** `../docs/plans/FPS_PLAN.md` (phases: EGF + Stanley
  Prop 1.6.1; Worpitzky; composition/exp-log; q-analogues).

## Design

`{fps R}` is the type of coefficient sequences `nat -> R` (wrapped in a
record). Equality of series is genuine Leibniz equality: the classical
axioms of `mathcomp-classical` (functional extensionality + the generic
eqType/choiceType mixins — the same axiom set as mathcomp-analysis) let us
mount the whole `GRing` hierarchy:

| Structure | Base ring `R` | Provided by |
|---|---|---|
| `eqType`, `choiceType` | any `Type` | `gen_eqMixin` / `gen_choiceMixin` |
| `zmodType` | `zmodType` | coefficientwise |
| `comNzRingType`, `algType R` | `comNzRingType` | Cauchy product |
| `comUnitRingType` | `comUnitRingType` | prefix recursion |

Highlights:

- **Polynomial bootstrap.** Ring axioms are not proved by bigop juggling:
  coefficient `n` of a product factors through the degree-`n` polynomial
  truncations (`coef_fpsM_trunc`), so associativity/commutativity are
  inherited from `{poly R}`.
- **Units over any `comUnitRingType`** (no field needed):
  `f \is a GRing.unit  <->  f``_0 \is a GRing.unit` (`fps_unitE`), with
  inverse coefficients computed by the recurrence
  `i_0 = (f_0)^-1`, `i_{m+1} = -(f_0)^-1 \sum_{k<=m} f_{m+1-k} i_k`.
  This matters for series over `int` or `{poly int}` (q-series).
- **Polynomial embedding** `poly_fps : {poly R} -> {fps R}` is an injective
  ring morphism; `'Xf` is the series x.
- Sanity theorem: `fps_inv_onesubX : (1 - 'Xf)^-1 = fps_geom` (geometric
  series), over any `comUnitRingType`.

## Files

| File | Content |
|---|---|
| `fps.v` | carrier, algebraic structures, units, polynomial embedding, geometric series |

(Coming per the plan: `fps_deriv.v`, `fps_egf.v`, `fps_trig.v`,
`fps_ode.v`, then `fps_ogf.v`, `fps_comp.v`, `fps_explog.v`.)

## Axioms

`Print Assumptions` on any result here lists at most the classical trio of
`mathcomp-classical` (`functional_extensionality_dep`,
`propositional_extensionality`, `constructive_indefinite_description`).
The host repository's combinatorial core remains axiom-free; only the
generating-function layer uses these.

## Inspiration

The design follows the lemma inventory and goals of
[hivert/FormalPowerSeries](https://github.com/hivert/FormalPowerSeries)
(GPL-3.0) without sharing code: that library builds full series as inverse
limits of truncated series; we build them directly on sequences (classical
axioms make the direct route simple) and bootstrap ring axioms through
`{poly R}`.
