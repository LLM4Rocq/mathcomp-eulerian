# Open axioms — status after Phases A–C (2026-04-17)

## Executive summary

**9 of 11 psi.v axioms proved.** The original 13 axiomatic items (11 in
`psi.v`, 2 in `beta_swap.v`) are reduced to **4**: 1 Axiom + 1 Admitted
in `psi.v`, plus 2 Axioms in `beta_swap.v`.

Phases A (standalone), B (shape stability), and C (Fact #3) are complete.
Phase D (type bridge + close beta_swap) remains.

---

## 1. Remaining axiomatic items

### psi.v — 1 Axiom + 1 Admitted

| # | Item | Line | Type | Milestone | Difficulty |
|---|------|------|------|-----------|------------|
| 1 | `phi_w_support` | ~5940 | Axiom | M6 | Medium (~40 LOC) |
| 2 | `strict_witness_exists` (n≥14 step) | ~6413 | Admitted | M6 | Easy (~20 LOC) |

**`phi_w_support`**: Support characterization of Φ_w(a+b, ab+ba).
X ∈ expand(Φ_w) ↔ S_w ⊆ ω(X). Combinatorial identity on cd-expansion.
Depends on fact3 (now proved).

**`strict_witness_exists`**: For any k < n-2, ∃ w with S_w = {k}.
Proved computationally for n ≤ 13 via native_compute. The inductive
step for n ≥ 14 needs a structural lemma that extending the ascending
suffix preserves the D-letter at position k+1.

**Bug fix (2026-04-17):** Bound corrected from `k < n.-1` to `k < n.-2`
(original statement was unprovable — last position always has
window_size = 1).

### beta_swap.v — 2 Axioms

| # | Item | Line | Milestone | Difficulty |
|---|------|------|-----------|------------|
| 3 | `beta_swap_lt_caseA` | ~120 | M7 | Medium (~80 LOC) |
| 4 | `beta_swap_lt_caseB` | ~131 | M7 | Hard (~140 LOC) |

**Case A** (j at boundary or j+1 ∈ D): ω(D) ⊊ ω(toggle_at D j) by
`toggle_at_j_omega_strict_superset`. Prop 1.6.4 gives β(D) < β(toggle).
Gap: type bridge from seq-level to finset-level.

**Case B** (j+1 ∉ D): ω-sets differ by adjacent swap (bit i enters,
bit j leaves). Requires cd-index marginal-contribution comparison.
See M7_CLOSING_AXIOMS_INFORMAL.md §4.5.

---

## 2. Proved axioms (this session, 2026-04-17)

### Phase A — Standalone axioms (4 proved)

| Axiom | Strategy |
|-------|----------|
| `window_trichotomy` | Strong induction on size, 9-way case analysis on mm_pos |
| `endpoint_implies_next_has_left_child` | Induction on tree, 3 cases on k vs mm_pos |
| `LR_pred_is_endpoint` | Induction + helper `window_size_last` (rightmost = leaf) |
| `strict_witness_exists` | Explicit witness `iota 1 k ++ [k+2;k+1] ++ iota (k+3) ...`; n≤13 by native_compute |

### Phase B — Shape stability (5 proved)

| Axiom | Strategy |
|-------|----------|
| `window_size_psi` | Order-isomorphism argument: `mm_pos_order_iso` + `window_size_order_iso` |
| `has_left_child_psi` | Same pattern via `has_left_child_order_iso` |
| `psi_comm_disjoint` | 5-region nth extensionality + `window_at_psi_disjoint` |
| `window_size_psi_ancestor` | Trivial corollary of `window_size_psi` |
| `psi_comm_nested` | Proved using shape stability + modular arithmetic |

### Phase C — Fact #3 (1 proved)

| Axiom | Strategy |
|-------|----------|
| `fact3` | Decidable `check_fact3` predicate + `check_fact3P` reflection + structural decomposition |

### Previously proved (before this session)

All M2 infrastructure (T1–T7), M4 descent-effect axioms (10 lemmas),
`psi_involutive`, `psi_comm`, and all rank-shift algebra were proved
in prior sessions.

---

## 3. Dependency graph (updated)

```
M2 psi_involutive ─────────── DONE ✓
M3 psi_comm ────────────────── DONE ✓ (via window_trichotomy + disjoint + nested)
M4 descent axioms (10) ─────── DONE ✓
M5 fact3 ───────────────────── DONE ✓

phi_w_support (#1, Axiom)
  └── needs: fact3 ✓
  └── blocks: beta_swap_lt_caseA (#3)
  └── blocks: beta_swap_lt_caseB (#4)

strict_witness_exists (#2, Admitted for n≥14)
  └── blocks: beta_swap_lt_caseA (#3)

TYPE BRIDGE (seq nat ↔ {perm 'I_n.+1})
  └── blocks: beta_swap_lt_caseA (#3)
  └── blocks: beta_swap_lt_caseB (#4)
```

---

## 4. Recommended next steps (Phase D)

### Step 1: Close `phi_w_support` (~40 LOC)

Combinatorial identity on cd-expansion. Now unblocked by fact3.

### Step 2: Close `strict_witness_exists` for n≥14 (~20 LOC)

Structural lemma: appending to the ascending suffix preserves the
D-letter at position k+1 in the min-max tree.

### Step 3: Type bridge (~80 LOC)

- Define `seq_of_perm : {perm 'I_n.+1} -> seq nat` and inverse.
- Bridge `is_descent_seq ↔ is_descent`, `omega_seq ↔ omega_set`.
- Bridge M-class counting to `beta`.

### Step 4: Close `beta_swap_lt_caseA` and `beta_swap_lt_caseB`

Apply type bridge + phi_w_support + omega infrastructure from §H.

**Total remaining: ~260 LOC.**

---

## 5. Don't-repeat-these-mistakes log

All entries from prior sessions still apply, plus:

8. **`sorted_leq_nth` side conditions.** In recent MathComp, the
   `{in [pred n | n < size s] &, ...}` side conditions require explicit
   `rewrite inE` to unfold the `\in [pred ...]` wrapper before arithmetic
   rewrites can fire.

9. **`nth_psi_left/right/inside` have explicit arguments.** Don't write
   `rewrite (nth_psi_left Hlt)` — use `rewrite !nth_psi_left //`.

10. **Concurrent agent writes corrupt the file.** Running multiple agents
    on the same `.v` file in parallel causes regressions. Use sequential
    agents for the same file, or worktree isolation.

11. **`strict_witness_exists` bound.** The original `k < n.-1` is wrong.
    Must be `k < n.-2` (last position always has window_size = 1).

---

## 6. Files and documentation

| File | LOC | Role | Status |
|------|-----|------|--------|
| `mmtree.v` | 158 | M1: min-max tree inductive + round-trip | Complete |
| `psi.v` | ~6450 | M2–M6: ψᵢ operators, cd-index infrastructure | 1 Axiom + 1 Admitted |
| `beta_swap.v` | ~900 | Target: β-swap lemmas, ω-bridge, alt-max | 2 Axioms |
| `M2_PSI_INFORMAL.md` | ~820 | ψᵢ definition and involutivity proof | Reference |
| `M2_SUBTASKS.md` | ~160 | Decomposition of psi_involutive into T1–T7 | All done |
| `M3_COMMUTATIVITY_INFORMAL.md` | ~860 | Commutativity proof | All done |
| `M4_DESCENT_EFFECT_INFORMAL.md` | ~1100 | Descent-set effect proof | All done |
| `M5_FACT3_INFORMAL.md` | ~400 | Fact #3 proof | Done |
| `M6_THM163_INFORMAL.md` | ~370 | Theorem 1.6.3 assembly | In progress |
| `M7_CLOSING_AXIOMS_INFORMAL.md` | ~925 | Axiom-closing analysis | Phase D |
| `refs/stanley_1_6_cdindex.txt` | — | Stanley EC1 §1.6 source text | Reference |
