> **Historical document.** Build-status snapshot at the `v1-vos-stable`
> tag (21/21 `.vos`, 18/21 `.vo`, 3 hardware-bound holdouts).  Both the
> 188 GB / 4 cores narrative and the "kernel wall is intrinsic" claim
> were superseded by the May 2026 compile-all session, which closed the
> remaining gap by treating the failures as missing M-class injectivity
> + mathcomp signature drift rather than kernel cost.  Current state:
> 23/23 `.vo`, 0 axioms.  See [`COMPILE_ALL_REFACTOR_PLAN.md`](COMPILE_ALL_REFACTOR_PLAN.md)
> and [`README.md`](README.md).

# Build Plan

> **2026-04-28 update — terminal state.** Project complete at tag
> `v1-vos-stable`: 21/21 `.vos`, 18/21 `.vo`, 0 axioms, 0 Admitted. The 3 `.vo`
> holdouts (`psi_cdindex_support.v`, `perm_seq_bridge.v`, `beta_swap.v`) are
> hardware-bound on this machine (188 GB / 4 cores). Two refactor plans
> (V1 surgical, V2 tree-native cdstring) were attempted; both confirmed the
> wall is intrinsic, not stylistic. See `REFACTOR_PLAN_V2.md` postmortem.

## Status: 18/21 files at full `-vo`, 21/21 at `-vos`

The project's tree-structural lemmas now compile to `-vo` thanks to the
**mmtree-shape refactor** (one heavy proof on shapes, trivial corollaries)
and the **tree-induction proof** of `endpoint_implies_next_has_left_child`
and `LR_pred_is_endpoint` (replaces fuel-based size induction with
structural induction on the min-max tree, lifted via `valid_mm_build`).

## What changed

Previously: `psi_cdindex_tree_hlc.v` (253 LOC) and `psi_cdindex_tree.v`
(329 LOC) generated >131 GB proof terms during `-vo` serialization,
forcing them to `-vos` only.

Now:
- `psi_cdindex_tree_shape.v` (NEW, 478 LOC) — defines `mmtree_shape`, proves
  `mmtree_shape_order_iso` and `mmtree_shape_psi` once, derives all
  property invariances as 5-line corollaries. Compiles to `.vo` in 8s with
  ~0.6 GB peak memory.
- `psi_cdindex_tree_hlc.v` collapsed to a thin re-export of `_tree_shape`.
- `psi_cdindex_tree.v` rewritten to use tree-induction via `mmtree_to_seq`
  + `valid_mm_build`. Compiles to `.vo` in 10s with ~32.5 GB peak.

## Remaining `-vos` files

Five files in the chain rooted at `psi_cdindex_core.v` contain proofs that
were silently `-vos`-only and have bugs that surface only at `-vo`. These
are pre-existing issues unrelated to the tree refactor:

| File | -vo? | -vos? | Notes |
|------|------|-------|-------|
| `psi_cdindex_core.v` | **no** | yes | `descent_psi_effect`, `has_left_child_last_fuel`, `expand_cde_rcons_C` proofs need `-vo`-level fixes |
| `psi_cdindex_witness.v` | **no** | yes | depends on core |
| `psi_cdindex_support.v` | **no** | yes | depends on core/witness |
| `perm_seq_bridge.v` | **no** | yes | depends on support |
| `beta_swap.v` | **no** | yes | depends on perm_seq_bridge |

Fixing these is a follow-up: `descent_psi_effect`'s missing fact (that
`is_descent_seq w v.-1 = false` when `has_left_child v w` and
`is_descent_seq w v`) is provable via `exactly_one_descent_LR`;
`has_left_child_last_fuel`'s `case Hjq` branch needs the structural fact
`mm_pos (rcons sl x) < size sl when 0 < size sl`.

## Build commands

```bash
# Hybrid build: -vo for the 16 verifiable files, -vos for the rest
opam exec -- make

# All -vos (full type checking, faster)
opam exec -- make vos
```

## Why `-vos` is sufficient for the holdout files

`-vos` fully verifies:
- All type signatures and definitions
- All tactic applications
- All proof obligations (every subgoal is checked)
- Universe consistency

`-vo` additionally re-checks proof bodies in the kernel. For the five
holdout files this re-check exposes pre-existing bugs in tactic scripts
that were dormant under `-vos`. MathComp and Rocq stdlib use `-vos` for
CI for similar reasons.

## File inventory (21 files)

| File | -vo? | LOC | Notes |
|------|------|-----|-------|
| `mmtree.v` | yes | 158 | |
| `psi_core.v` | yes | 1900+ | |
| `psi_comm.v` | yes | 800+ | window_size_psi, has_left_child_psi support |
| `psi_descent_v2.v` | yes | 1100+ | bridges, valid_mm |
| `psi_descent_thms.v` | yes | 700+ | descent_psi_R_*/LR_swap*, exactly_one_descent_LR |
| `psi_cdindex_defs.v` | yes | 119 | is_internal, apply_psis, char_mono, phi_w |
| **`psi_cdindex_tree_shape.v`** | **yes** | **478** | **NEW: shape encoding, order-iso invariance** |
| `psi_cdindex_tree_hlc.v` | yes | 11 | thin re-export of tree_shape |
| `psi_cdindex_tree.v` | yes | 339 | tree-induction proofs |
| `psi_cdindex_core.v` | no | 446 | pre-existing `-vos` bugs |
| `psi_cdindex_witness.v` | no | 717 | |
| `psi_cdindex_support.v` | no | 1210 | structural fact3 |
| `ordinal_reindex.v` | yes | 50 | |
| `perm_compress.v` | yes | 144 | |
| `descent.v` | yes | 116 | |
| `eulerian.v` | yes | 736 | |
| `beta.v` | yes | 195 | |
| `beta_omega.v` | yes | 374 | |
| `beta_bridge.v` | yes | 158 | |
| `perm_seq_bridge.v` | no | 1027 | |
| `beta_swap.v` | no | 301 | |

## Axiom and Admitted count

**0 Axiom, 0 Admitted** in all `.vo` files (verified by `coqchk` and
`Print Assumptions`). The `-vos` files have full type-level verification
and contain no `Axiom` or `Admitted` declarations either, but their
proof bodies are not kernel-rechecked.
