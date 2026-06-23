# mathcomp-eulerian

A Rocq / MathComp formalization of permutation **descent statistics**,
**Eulerian numbers**, and the **set-refined β-numbers** of Stanley
*Enumerative Combinatorics I* §1.4 + §1.6, including a full development
of the **cd-index** via Stanley's ψᵢ operators on min-max trees.

The headline theorem is **Stanley Corollary 1.6.5** (the alternating
descent set strictly maximizes β):

```coq
Lemma beta_alt_max n (D : {set 'I_n}) :
  ~~ set_is_alt D -> beta D < beta (alt_desc_set n).
```

`beta_alt_max` is closed under the global context — no axioms, no
admits.

## Status

- **49 / 49** maintained `.v` files compile to full `.vo`.
- **0 `Admitted`** in the active build chain.
- **Axiom policy, per layer**: the combinatorial core (everything under
  `mathcomp_eulerian` except `stanley_egf.v`) uses **0 axioms** beyond
  Rocq's standard core; the generating-function layer (`fps/`, namespace
  `mathcomp_fps`, plus the bridge `stanley_egf.v`) uses exactly the
  standard classical axioms of `mathcomp-classical` (functional/
  propositional extensionality + indefinite description), as does
  mathcomp-analysis.
- `coqchk` validates the entire library.
- The headline theorems `beta_alt_max` (Stanley Cor 1.6.5) and
  `omega_proper_beta_lt` (Stanley Prop 1.6.4) both report
  "Closed under the global context" via `Print Assumptions`.
- `stanley_1_6_1` (`stanley_egf.v`): **Stanley Prop 1.6.1**,
  `sum E_n x^n/n! = sec x + tan x` as formal power series over `rat`,
  built on the new reusable FPS sub-library [`fps/`](fps/) and the
  André recurrence `euler_rec` (`reflection.v`).
- `worpitzky` (`worpitzky.v`, axiom-free) and `stanley_1_4`
  (`stanley_ogf.v`): **Worpitzky's identity** and its Stanley §1.4
  packaging `sum (m+1)^(n+1) x^m = A_n(x)/(1-x)^(n+2)` over `{fps int}`.
- `stirling_cycle_egf` (`stirling_egf.v`): the **Stirling-cycle egf**
  `sum_n (sum_k c(n,k) t^k) x^n/n! = (1-x)^(-t)` over `{fps {poly rat}}`,
  via the new composition / exp / log layer of [`fps/`](fps/).
- `q_eulerian_rec` (`qeul_rec.v`), `q_worpitzky` (`qworpitzky.v`) — both
  axiom-free — and `carlitz` (`carlitz.v`): **Carlitz's q-analogue of
  Stanley §1.4**, `sum_m ([m+1]_q)^(n+1) x^m
  = (sum_w q^maj(w) x^des(w)) / prod_(i<n+2) (1-q^i x)` over
  `{fps {poly int}}`, from the q-Eulerian (maj,des)-insertion recurrence
  and the q-staircase.

## Build

Requires Rocq ≥ 9.0 and MathComp ≥ 2.5
(`all_ssreflect`, `fingroup`, `perm`, `binomial`, `ssrint`, `ssralg`).

```bash
make clean && make -j2
```

To check axiom-freeness end-to-end:

```bash
coqchk -R . mathcomp_eulerian mathcomp_eulerian.beta_swap

echo 'From mathcomp_eulerian Require Import beta_swap. \
      Print Assumptions beta_alt_max.' \
  | rocq top -R . mathcomp_eulerian
```

## Installation (opam)

The library is packaged for opam. Install it directly from git, pinned to a
tagged release for reproducibility:

```bash
opam pin add rocq-mathcomp-eulerian \
  git+https://github.com/LLM4Rocq/mathcomp-eulerian.git#v0.1.0
```

This builds with `coq_makefile` and installs the `mathcomp_eulerian` and
`mathcomp_fps` libraries under `user-contrib/`, so downstream developments can
`From mathcomp_eulerian Require Import beta_swap.` (and `From mathcomp_fps
Require Import …`) with no `-R` flag. Dependencies: `rocq-mathcomp-ssreflect`,
`rocq-mathcomp-algebra`, `rocq-mathcomp-classical`.

## Where to read

A mathematician familiar with Stanley EC1 should start with the
mathematician-facing docs in this order:

| Document | What it gives you |
|----------|-------------------|
| **The formal companion PDF** at https://llm4rocq.github.io/mathcomp-eulerian/eulerian_formal.pdf (source: [`docs/formal/`](docs/formal/)) | A 92-page Stanley-style reading. 9 narrative chapters covering all of §1.3, §1.4, §1.6.2, §1.6.3 (the project headline), and §1.6.4 (André's reflection method, fully proved). Every formal block carries a clickable GitHub link and a "Decoded" line in plain math. Appendix A is an auto-generated catalog of all 870 named results in the build chain. **Best single artifact for a Stanley reader.** |
| [`docs/READING_GUIDE.md`](docs/READING_GUIDE.md) | A shorter 10-minute orientation: index conventions, type translations, a worked example walking through Stanley's `[3,1,4,2]` in our formal types. Also a markdown alternative if you'd rather not read the PDF. |
| [`docs/DEFINITIONS_AUDIT.md`](docs/DEFINITIONS_AUDIT.md) | Side-by-side audit of every formal definition vs. Stanley's informal one, with file:line citations and a 1-line verdict per definition. The trust artifact in markdown form. |
| The **blueprint** at https://llm4rocq.github.io/mathcomp-eulerian/ (source: [`blueprint/`](blueprint/)) | Interactive paper-style document with a clickable dependency graph. Every theorem links back to its Rocq lemma. |
| [`PROOF_STATEMENTS.md`](PROOF_STATEMENTS.md) | Per-result informal statement with verification status and Stanley page reference. |
| [`FORMAL_VS_STANLEY.md`](FORMAL_VS_STANLEY.md) | Older theorem-by-theorem map (focused on §1.4 + §1.6.3 cd-index). |

Historical milestone-by-milestone informal proof notes (`M2`–`M7_*_INFORMAL.md`) are kept in [`docs/internal/`](docs/internal/) for the record; their content is subsumed by the blueprint chapters above.

Stanley *Enumerative Combinatorics* Vol. 1, 2nd ed. (Cambridge, 2012),
§1.4 (descents and Eulerian polynomials) and §1.6.3 (the cd-index of
permutations) is the underlying source. The aligned excerpts are in
`refs/stanley_1_4_descents.txt` and `refs/stanley_1_6_cdindex.txt`.

## Notation alignment

Stanley writes `Sn` for permutations of `[n]` and `D(w) ⊆ [n−1]` for
the descent set. We use `{perm 'I_{n+1}}` and `{set 'I_n}` — the
indices shift by 1 because we 0-index, but the mathematical content
matches. Stanley's `βn(S)` is exactly our `beta D`. The full glossary
is in [`FORMAL_VS_STANLEY.md`](FORMAL_VS_STANLEY.md).

## File structure

The 23 maintained files are listed in topological order in
`_CoqProject`. Briefly:

```
ordinal_reindex -> perm_compress -> descent -> eulerian -> beta
                                            -> beta_omega -> beta_bridge

mmtree -> psi_core -> psi_comm -> psi_descent_v2 -> psi_descent_thms
      -> psi_cdindex_defs -> psi_cdindex_tree_shape
      -> psi_cdindex_tree_hlc -> psi_cdindex_tree
      -> psi_cdindex_core -> psi_cdindex_witness
      -> psi_cdindex_support_defs -> psi_cdindex_support
      -> perm_seq_bridge -> beta_swap
```

The two chains meet at `perm_seq_bridge.v`, which proves Stanley
Prop 1.6.4 (`omega_proper_beta_lt`); `beta_swap.v` then derives
Cor 1.6.5 (`beta_alt_max`).

For a per-file table with verification status and roles, see
[`PROOF_STATEMENTS.md`](PROOF_STATEMENTS.md).

## Conventions

- Lemma names follow MathComp style: `snake_case`, conclusion-based
  (`des_rev_perm`, `beta_eulerian`, `omega_proper_beta_lt`).
- `eulerian n k` is indexed so that `n` is "permutation size minus
  one" and `k` ranges over `0..n`. This avoids `n.-1` in the
  recurrence.
- "Set-alternating" (`set_is_alt D`) means every consecutive pair
  `(i, i+1)` has differing membership in `D`. There are two such
  sets on `'I_n` (offset by 1); they have equal β by reversal
  symmetry.
- All proofs are kernel-checked at `Qed`. No `Axiom`, `Parameter`,
  `Conjecture`, `Admitted`, or `admit` in the active build chain.

## Repository layout

- Maintained `.v` files at the root, listed in `_CoqProject`.
- Mathematician-facing docs at the root: `README.md`,
  `PROOF_STATEMENTS.md`, `FORMAL_VS_STANLEY.md`, and the
  `M*_INFORMAL.md` series.
- Internal planning / refactor history under `docs/internal/`.
- Stanley source excerpts under `refs/`.
- Archived prototypes (with `.txt` extension to keep them off the
  build) under `archive/`.
