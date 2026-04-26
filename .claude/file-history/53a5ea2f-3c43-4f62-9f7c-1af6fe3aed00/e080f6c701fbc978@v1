# Next iteration plan — 4 axiomatic items remaining (2026-04-17)

## What just happened

**Phases A–C complete.** 9 of 11 psi.v axioms proved in one session:

- Phase A: `window_trichotomy`, `endpoint_implies_next_has_left_child`,
  `LR_pred_is_endpoint`, `strict_witness_exists` (n≤13)
- Phase B: `window_size_psi`, `has_left_child_psi`, `psi_comm_disjoint`,
  `window_size_psi_ancestor`, `psi_comm_nested`
- Phase C: `fact3` (Fact #3 identity, the hardest single axiom)

Key infrastructure added: `mm_pos_order_iso`, `window_size_order_iso`,
`has_left_child_order_iso`, `check_fact3` decidable predicate, ~40
helper lemmas total.

Bug fix: `strict_witness_exists` bound corrected from `k < n.-1` to
`k < n.-2` (original was unprovable).

---

## Remaining axiomatic items (4 total)

### psi.v — 1 Axiom + 1 Admitted

| # | Item | Line | Type | Difficulty |
|---|------|------|------|------------|
| 1 | `phi_w_support` | ~5940 | Axiom | Medium (~40 LOC) |
| 2 | `strict_witness_exists` (n≥14) | ~6413 | Admitted | Easy (~20 LOC) |

### beta_swap.v — 2 Axioms

| # | Item | Line | Difficulty |
|---|------|------|------------|
| 3 | `beta_swap_lt_caseA` | ~120 | Medium (~80 LOC) |
| 4 | `beta_swap_lt_caseB` | ~131 | Hard (~140 LOC) |

---

## Dependency graph

```
fact3 ──────────────────────── DONE ✓
psi_involutive, psi_comm ───── DONE ✓
All M4 descent axioms ──────── DONE ✓

phi_w_support (#1)
  └── needs: fact3 ✓
  └── blocks: beta_swap_lt_caseA (#3)

strict_witness_exists n≥14 (#2)
  └── blocks: beta_swap_lt_caseA (#3)

TYPE BRIDGE (seq nat ↔ {perm 'I_n.+1})
  └── blocks: #3, #4

beta_swap_lt_caseB (#4)
  └── needs: type bridge + cd-index marginal comparison
```

---

## Recommended attack order

### Phase D.1: Close psi.v (~60 LOC, parallel)

1. **`phi_w_support`** (~40 LOC) — Support characterization: X ∈
   expand(Φ_w) ↔ S_w ⊆ ω(X). Direct from the cd-expansion structure.
   See `M6_THM163_INFORMAL.md` §3.2.

2. **`strict_witness_exists`** n≥14 (~20 LOC) — Structural lemma:
   `witness_perm (n+1) k` extends `witness_perm n k` by appending to
   ascending suffix, preserving the D-letter at position k+1. The
   `check_strict_witness` boolean is already defined; need to show it's
   true for all valid (n,k) via the extension property.

### Phase D.2: Type bridge (~80 LOC)

Define the bijection between `seq nat` and `{perm 'I_n.+1}`:

```coq
Definition seq_of_perm (n : nat) (p : {perm 'I_n.+1}) : seq nat :=
  [seq val (p i) | i <- enum 'I_n.+1].

Definition perm_of_seq (w : seq nat) : ... (* inverse *)
```

Bridge lemmas:
- `is_descent_seq w k ↔ is_descent (perm_of_seq w) k`
- `omega_seq S ↔ omega_set (finset_of_seq S)`
- M-class counting: `|{[w] : S_w ⊆ ω(S)}| = beta S`

### Phase D.3: Close beta_swap axioms (~140 LOC)

**Case A** (~40 LOC): Combine type bridge + `phi_w_support` +
`toggle_at_j_omega_strict_superset` (already proved in §H).

**Case B** (~100 LOC): The hardest remaining piece. Requires
showing that gaining ω-bit i compensates for losing ω-bit j = i+1
in the cd-index expansion. See `M7_CLOSING_AXIOMS_INFORMAL.md` §4.5.

**Total remaining: ~280 LOC across 3 sub-phases.**

---

## Don't-repeat-these-mistakes log

All entries from AXIOMS_TODO.md §5 apply, plus:

10. **Concurrent agent writes corrupt the file.** Running multiple agents
    on `psi.v` in parallel caused 3 regressions (lost proofs of
    window_trichotomy, LR_pred_is_endpoint, strict_witness_exists).
    Solution: use sequential agents for the same file. Restore from
    `.claude/file-history/` if regressions occur.

11. **`strict_witness_exists` bound.** `k < n.-1` → `k < n.-2`.

---

## File reference

| File | Role | Status |
|------|------|--------|
| `psi.v` (~6450 LOC) | M2–M6 infrastructure | 1 Axiom + 1 Admitted |
| `beta_swap.v` (~900 LOC) | M7 target | 2 Axioms |
| `mmtree.v` (~158 LOC) | M1 min-max tree | Complete |
| `M6_THM163_INFORMAL.md` | Theorem 1.6.3 assembly | Reference for #1 |
| `M7_CLOSING_AXIOMS_INFORMAL.md` | Axiom-closing analysis | Reference for #3–#4 |
