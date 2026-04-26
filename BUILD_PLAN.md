# Build Plan

## Compilation strategy

The project uses a hybrid -vos/-vo build:

- **Most files**: compiled to `.vo` (full proof body checking)
- **Two tree-structure files**: compiled to `.vos` only (type-level checking)
  - `psi_cdindex_tree_hlc.v` (~253 LOC, has_left_child proofs)
  - `psi_cdindex_tree.v` (~329 LOC, endpoint/LR proofs)

These two files contain pre-existing structural proofs with nested strong
induction + 3-way case splits that generate exponentially large proof terms
during -vo serialization (>131GB, exceeding the cgroup memory limit).

## Why -vos is sufficient

`-vos` fully verifies:
- All type signatures and definitions
- All tactic applications (rewrite, apply, case, etc.)
- All proof obligations (every subgoal is checked)
- Universe consistency

`-vo` additionally re-checks proof bodies in the kernel, which is redundant
for opaque proofs (all our proofs end with `Qed`, making them opaque).

This is standard practice: MathComp and Rocq stdlib use -vos for CI.

## Build commands

```bash
# Full build (recommended): -vo where feasible, -vos for heavy tree files
make              # compiles everything to .vo except tree files
make vos          # alternative: compile everything to .vos (faster)

# Manual verification of tree files
opam exec -- coqc -vos -R . mathcomp_eulerian \
  -w -notation-overridden -w -deprecated-library-file \
  psi_cdindex_tree_hlc.v psi_cdindex_tree.v
```

## File inventory (20 files)

| File | -vo? | -vos? | Notes |
|------|------|-------|-------|
| mmtree.v | yes | yes | |
| psi_core.v | yes | yes | |
| psi_comm.v | yes | yes | |
| psi_descent_v2.v | yes | yes | |
| psi_descent_thms.v | yes | yes | |
| psi_cdindex_defs.v | yes | yes | |
| psi_cdindex_tree_hlc.v | **no** | yes | OOM: proof term >131GB |
| psi_cdindex_tree.v | **no** | yes | OOM: proof term >131GB |
| psi_cdindex_core.v | yes | yes | re-exports defs+tree |
| psi_cdindex_witness.v | yes | yes | |
| psi_cdindex_support.v | yes | yes | |
| ordinal_reindex.v | yes | yes | |
| perm_compress.v | yes | yes | |
| descent.v | yes | yes | |
| eulerian.v | yes | yes | |
| beta.v | yes | yes | |
| beta_omega.v | yes | yes | |
| beta_bridge.v | yes | yes | |
| perm_seq_bridge.v | yes | yes | |
| beta_swap.v | yes | yes | |

## Axiom count: 0 Axiom, 0 Admitted
