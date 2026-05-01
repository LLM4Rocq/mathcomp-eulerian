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

- **23 / 23** maintained `.v` files compile to full `.vo`.
- **0 axioms** (beyond Rocq's standard core), **0 `Admitted`** in the
  active build chain.
- `coqchk` validates the entire library.
- The headline theorems `beta_alt_max` (Stanley Cor 1.6.5) and
  `omega_proper_beta_lt` (Stanley Prop 1.6.4) both report
  "Closed under the global context" via `Print Assumptions`.

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

## Where to read

A mathematician familiar with Stanley EC1 should start with these three
documents:

| Document | What it gives you |
|----------|-------------------|
| [`PROOF_STATEMENTS.md`](PROOF_STATEMENTS.md) | Per-result informal statement with verification status and Stanley page reference. The **table of contents** for the formal development. |
| [`FORMAL_VS_STANLEY.md`](FORMAL_VS_STANLEY.md) | Maps each formal definition / theorem to its statement in Stanley EC1 Chapter 1. The **notation glossary**. |
| The `M*_INFORMAL.md` series ([M2](M2_PSI_INFORMAL.md), [M3](M3_COMMUTATIVITY_INFORMAL.md), [M4](M4_DESCENT_EFFECT_INFORMAL.md), [M5](M5_FACT3_INFORMAL.md), [M6](M6_THM163_INFORMAL.md), [M7](M7_CLOSING_AXIOMS_INFORMAL.md)) | Module-by-module informal proof notes — paper-style mathematical reading of each milestone. |

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
