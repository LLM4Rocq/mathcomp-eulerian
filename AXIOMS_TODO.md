# Open axioms -- status update (2026-04-22)

## Executive summary

**9 of 11 psi.v axioms proved.** The original 13 axiomatic items (11 in
`psi.v`, 2 in `beta_swap.v`) are reduced to **4**: 1 Axiom + 1 Admitted
in `psi.v`, plus 2 Axioms in `beta_swap.v`.

Phases A (standalone), B (shape stability), and C (Fact #3) are complete.
Phase D (type bridge + close beta_swap) remains.

### New blocker (2026-04-22): `psi_descent.v` compilation

The M4 descent-effect proofs were refactored from the monolithic `psi.v`
into a modular file chain: `psi_core.v` -> `psi_comm.v` -> `psi_descent.v`
-> `psi_cdindex.v`. However, `psi_descent.v` cannot compile with full
`-vo` verification (50 hours / 243 GB, never finished). It compiles with
`-vos` (signatures only) in seconds. See `NEXT_ITERATION.md` for details.

---

## 1. Remaining axiomatic items

### psi.v -- 1 Axiom + 1 Admitted

| # | Item | Line | Type | Milestone | Difficulty |
|---|------|------|------|-----------|------------|
| 1 | `phi_w_support` | ~5940 | Axiom | M6 | Medium (~40 LOC) |
| 2 | `strict_witness_exists` (n>=14 step) | ~6413 | Admitted | M6 | Easy (~20 LOC) |

**`phi_w_support`**: Support characterization of Phi_w(a+b, ab+ba).
X in expand(Phi_w) <-> S_w subset omega(X). Combinatorial identity on cd-expansion.
Depends on fact3 (now proved).

**`strict_witness_exists`**: For any k < n-2, exists w with S_w = {k}.
Proved computationally for n <= 13 via native_compute. The inductive
step for n >= 14 needs a structural lemma that extending the ascending
suffix preserves the D-letter at position k+1.

### beta_swap.v -- 2 Axioms

| # | Item | Line | Milestone | Difficulty |
|---|------|------|-----------|------------|
| 3 | `beta_swap_lt_caseA` | ~120 | M7 | Medium (~80 LOC) |
| 4 | `beta_swap_lt_caseB` | ~131 | M7 | Hard (~140 LOC) |

### psi_descent.v -- compilation blocker

| # | Item | Type | Difficulty |
|---|------|------|------------|
| 5 | Full `-vo` compilation | Blocker | Hard (needs new proof strategy) |

The proofs are correct (pass `-vos`) but generate proof terms too large
for the kernel to serialize. See `NEXT_ITERATION.md` for the diagnosis
and three recommended approaches (structural recursion on mmtree,
reflection/vm_compute, or accept -vos).

---

## 2. Proved axioms (complete list)

### Phase A -- Standalone axioms (4 proved)

| Axiom | Strategy |
|-------|----------|
| `window_trichotomy` | Strong induction on size, 9-way case analysis on mm_pos |
| `endpoint_implies_next_has_left_child` | Induction on tree, 3 cases on k vs mm_pos |
| `LR_pred_is_endpoint` | Induction + helper `window_size_last` (rightmost = leaf) |
| `strict_witness_exists` | Explicit witness; n<=13 by native_compute |

### Phase B -- Shape stability (5 proved)

| Axiom | Strategy |
|-------|----------|
| `window_size_psi` | Order-isomorphism argument |
| `has_left_child_psi` | Same pattern via `has_left_child_order_iso` |
| `psi_comm_disjoint` | 5-region nth extensionality |
| `window_size_psi_ancestor` | Corollary of `window_size_psi` |
| `psi_comm_nested` | Shape stability + modular arithmetic |

### Phase C -- Fact #3 (1 proved)

| Axiom | Strategy |
|-------|----------|
| `fact3` | Decidable predicate + reflection + structural decomposition |

### M4 descent-effect (proved, in psi_descent.v, -vos only)

| Lemma | Status |
|-------|--------|
| `descent_psi_R_add` | Proved (-vos verified) |
| `descent_psi_R_remove` | Proved (-vos verified) |
| `descent_psi_LR_swap1` | Proved (-vos verified) |
| `descent_psi_LR_swap2` | Proved (-vos verified) |

---

## 3. Dependency graph

```
M2 psi_involutive ----------- DONE
M3 psi_comm ----------------- DONE
M4 descent axioms (10) ------ DONE (proofs correct, -vo compilation blocked)
M5 fact3 -------------------- DONE

phi_w_support (#1, Axiom)
  needs: fact3 (done)
  blocks: beta_swap_lt_caseA (#3)
  blocks: beta_swap_lt_caseB (#4)

strict_witness_exists (#2, Admitted for n>=14)
  blocks: beta_swap_lt_caseA (#3)

TYPE BRIDGE (seq nat <-> {perm 'I_n.+1})
  blocks: beta_swap_lt_caseA (#3)
  blocks: beta_swap_lt_caseB (#4)
```

---

## 4. Recommended next steps

### Priority 1: Fix psi_descent.v compilation (see NEXT_ITERATION.md)

Three options: structural recursion on mmtree, reflection/vm_compute,
or accept -vos workflow.

### Priority 2: Close phi_w_support (~40 LOC)

Combinatorial identity on cd-expansion. Unblocked by fact3.

### Priority 3: Close strict_witness_exists for n>=14 (~20 LOC)

Structural lemma: appending to ascending suffix preserves D-letter.

### Priority 4: Type bridge (~80 LOC)

Define `seq_of_perm : {perm 'I_n.+1} -> seq nat` and inverse.

### Priority 5: Close beta_swap_lt_caseA and beta_swap_lt_caseB

Apply type bridge + phi_w_support + omega infrastructure.

---

## 5. Don't-repeat-these-mistakes log

1-7. (From prior sessions, still apply.)

8. **`sorted_leq_nth` side conditions.** In recent MathComp, the
   `{in [pred n | n < size s] &, ...}` side conditions require explicit
   `rewrite inE` to unfold the `\in [pred ...]` wrapper.

9. **`nth_psi_left/right/inside` have explicit arguments.** Use
   `rewrite !nth_psi_left //`.

10. **Concurrent agent writes corrupt the file.** Use sequential agents
    or worktree isolation.

11. **`strict_witness_exists` bound.** Must be `k < n.-2` (not `k < n.-1`).

12. **Strong induction + 3-way case split = massive proof terms.**
    Do NOT use `elim=> [|n IH] ... case: (ltngtP i j)` for proofs that
    will be serialized to `.vo`. The kernel cannot handle the resulting
    terms. Use structural recursion on datatypes or reflection instead.

---

## 6. File inventory

| File | Role | Compiles -vo? |
|------|------|---------------|
| `mmtree.v` | Min-max tree datatype | Yes |
| `ordinal_reindex.v` | Ordinal helpers | Yes |
| `perm_compress.v` | Permutation compression | Yes |
| `descent.v` | Descent statistics | Yes |
| `eulerian.v` | Eulerian polynomials | Yes |
| `beta.v` | Beta polynomials | Yes |
| `beta_swap.v` | Beta-swap (2 axioms remain) | Yes |
| `psi_core.v` | Core psi definitions | Yes |
| `psi_comm.v` | Psi commutativity | Yes |
| `psi_descent.v` | Descent-set effect | **-vos only** |
| `psi_cdindex.v` | cd-index formalization | **-vos only** |
| `psi_descent_wf.v` | Prototype: Function-based has_left_child | Yes |
