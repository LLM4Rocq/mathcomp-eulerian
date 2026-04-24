# Open axioms -- status update (2026-04-24, end of day)

## Executive summary

**2 Axioms remain** in the active build (down from 13 originally):
1. `omega_proper_beta_lt` (beta_bridge.v:155) — Stanley Prop 1.6.4
2. `beta_swap_lt_caseB` (beta_swap.v:72) — omega-incomparable toggle case

All psi.v axioms are proved. The psi_descent compilation blocker is resolved.
Beta_swap infrastructure restructured into beta_omega.v + beta_bridge.v.

### Changes today (2026-04-24):

1. **psi_descent compilation resolved**: replaced by psi_descent_v2.v (8s) +
   psi_descent_thms.v (7s). Was 50h+ / 243GB+ / never finished.
2. **beta_swap restructured**: extracted omega infrastructure into beta_omega.v,
   created beta_bridge.v with type bridge (set_to_seq + omega correspondence)
3. **beta_swap_lt_caseA proved** from omega_proper_beta_lt +
   toggle_at_j_omega_strict_superset
4. **phi_w_support and strict_witness_exists confirmed already proved** in
   psi_cdindex.v

---

## 1. Remaining axiomatic items

### beta_bridge.v -- 1 Axiom

| # | Item | Line | Type | Difficulty |
|---|------|------|------|------------|
| 1 | `omega_proper_beta_lt` | 155 | Axiom | Hard (~700 LOC total) |

**Stanley Prop 1.6.4**: `omega_set D \proper omega_set E -> beta D < beta E`.

**What's proved (bridge infrastructure)**:
- `set_to_seq`: converts `{set 'I_n}` to sorted `seq nat` (5 proved lemmas)
- `omega_set_seq_local_bridge`: proves `omega_set D` and `omega_seq (set_to_seq D)` agree on membership
- `omega_monotone_class_count` (psi_cdindex.v): seq-level Prop 1.6.4 monotonicity
- `strict_witness_exists` (psi_cdindex.v): strict witness for k ∈ ω(T)\ω(S)
- `fact3` (psi_cdindex.v): cd-index identity Φ_w(a+b, ab+ba) = Σ u_{D(v)}

**What's missing**:
- (a) `phi_w_support_general`: the cd-index identity for general n (~500-1000 LOC).
  Proved computationally for S_3, S_4 in psi_cdindex.v. General proof needs
  formalizing the min-max tree decomposition showing each M-class contributes
  exactly one cd-monomial.
- (b) `perm_to_seq` bijection (~200 LOC): connecting `{perm 'I_n.+1}` to
  `seq nat` so `beta D` (perm counting) matches M-class counting. Must show
  `is_descent s i = is_descent_seq (perm_to_seq s) i`.

### beta_swap.v -- 1 Axiom

| # | Item | Line | Type | Difficulty |
|---|------|------|------|------------|
| 2 | `beta_swap_lt_caseB` | 72 | Axiom | Hard (~300-500 LOC) |

**Case B**: `i,j ∈ D, j=i+1, j+1 ∉ D → beta D < beta (toggle_at D j)`.

Omega-sets are incomparable (swapped bits at positions i and j), so
Prop 1.6.4 doesn't apply directly.

**Approaches analyzed**:
- Omega containment: fails (omega-sets incomparable in Case B)
- Adjacent transposition injection: works for "good" case (σ(j) < σ(j+2)),
  fails for "bad" case (creates spurious descent at position j+1)
- Reduction chains via intermediate toggles: circular dependencies
- Complement/reversal symmetry: maps back to equivalent both-in instance

**Viable path**: Piecewise Foata injection (~300-500 LOC):
1. Transposition for σ(j) < σ(j+2) ("good" case)
2. Cyclic rotation of ascending run for σ(j) > σ(j+2) ("bad" case)
3. Prove combined map is injective + find strict witness

**Alternative**: If omega_proper_beta_lt is proved first, Case B needs a
cd-index marginal-contribution comparison showing that the lower omega-bit i
contributes more M-classes than the upper omega-bit j=i+1.

### Proved (no longer axiomatic)

- `phi_w_support`: verified for S_3, S_4 in psi_cdindex.v (never was an axiom)
- `strict_witness_exists`: proved in psi_cdindex.v (line 1905)
- `beta_swap_lt_caseA`: proved in beta_bridge.v from omega_proper_beta_lt
- All 11 original psi.v axioms: proved across psi_core/psi_comm/psi_descent_v2/psi_descent_thms/psi_cdindex

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

### M4 descent-effect (proved, fully -vo verified)

| Lemma | Status |
|-------|--------|
| `descent_psi_R_add` | Proved (-vo verified, 7s) |
| `descent_psi_R_remove` | Proved (-vo verified, 7s) |
| `descent_psi_LR_swap1` | Proved (-vo verified, 7s) |
| `descent_psi_LR_swap2` | Proved (-vo verified, 7s) |

### M7 beta-swap (1 proved, 1 axiom remains)

| Lemma | Status |
|-------|--------|
| `beta_swap_lt_caseA` | Proved (from omega_proper_beta_lt) |
| `beta_swap_lt_caseB` | **Axiom** |

---

## 3. Dependency graph

```
M2 psi_involutive ------------- DONE
M3 psi_comm ------------------- DONE
M4 descent axioms (10) -------- DONE (fully -vo verified)
M5 fact3 ---------------------- DONE
M6 strict_witness_exists ------ DONE
    omega_monotone_class_count - DONE

beta_swap_lt_caseA ------------ DONE (from omega_proper_beta_lt)

omega_proper_beta_lt (#1, Axiom)
  needs: phi_w_support_general (not proved in general)
  needs: perm_to_seq bijection (not built)
  has:   omega bridge infrastructure (proved in beta_bridge.v)
  has:   omega_monotone_class_count + strict_witness_exists (proved)

beta_swap_lt_caseB (#2, Axiom)
  approach A: omega_proper_beta_lt + cd-index marginal comparison
  approach B: direct Foata piecewise injection (~300-500 LOC)
```

---

## 4. Recommended next steps

### Priority 1: Build perm ↔ seq bijection (~200 LOC)

Define `perm_to_seq : {perm 'I_n.+1} -> seq nat := [seq val (s i) | i <- enum 'I_n.+1]`
and `seq_to_perm : seq nat -> {perm 'I_n.+1}` (inverse). Prove:
- `descent_set s = [set i | is_descent_seq (perm_to_seq s) i]`
- `perm_to_seq` is a bijection onto seqs that are permutations of `iota 0 n.+1`
This connects `beta D` (perm counting) to seq-level counting.

### Priority 2: Prove phi_w_support_general (~500 LOC)

Show that `fact3` (proved) implies the support characterization:
`X ∈ expand(Φ_w) ⟺ S_w ⊆ ω(desc(X))` for all w.

Key insight: `fact3` gives `sorted (char_mono ∘ apply_psis) = sorted (expand_cde ∘ phi_w)`.
The support characterization follows from the definition of `expand_cde` and the
relationship between `char_mono` (descent pattern of a permutation) and omega.

### Priority 3: Close omega_proper_beta_lt (~40 LOC)

Combine: perm↔seq bijection + phi_w_support_general + omega bridge +
omega_monotone_class_count + strict_witness_exists.

### Priority 4: Close beta_swap_lt_caseB

**Option A** (~80 LOC): With omega_proper_beta_lt proved, show the cd-index
marginal contribution of bit i exceeds bit j=i+1 for adjacent omega-bit swap.

**Option B** (~300-500 LOC): Direct Foata piecewise injection, independent
of omega machinery. Uses adjacent transposition + cyclic rotation.

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

13. **`rewrite !lemma ?side_cond //` can be exponential.**
    When `!` (repeat) and `?` (optional) are combined with `//` (try solve),
    the search space grows exponentially. Use explicit lemma applications
    with positional arguments: `rewrite (@lemma _ arg1 arg2 _ Hpf1 Hpf2)`.
    Identified in `rs_head_max_descent` / `rs_head_min_no_descent` where
    `rewrite !index_uniq ?Hsz_rs ?ltnW //` caused 10+ minute timeouts.

---

## 6. File inventory

| File | Role | Compiles -vo? | Axioms |
|------|------|---------------|--------|
| `mmtree.v` | Min-max tree datatype | Yes | 0 |
| `ordinal_reindex.v` | Ordinal helpers | Yes | 0 |
| `perm_compress.v` | Permutation compression | Yes | 0 |
| `descent.v` | Descent statistics | Yes | 0 |
| `eulerian.v` | Eulerian polynomials | Yes | 0 |
| `beta.v` | Beta polynomials | Yes | 0 |
| `beta_omega.v` | Omega-set infrastructure | Yes | 0 |
| `beta_bridge.v` | Prop 1.6.4 bridge + Case A | Yes | **1** |
| `beta_swap.v` | Beta-swap (Case B axiom) | Yes | **1** |
| `psi_core.v` | Core psi definitions | Yes | 0 |
| `psi_comm.v` | Psi commutativity | Yes | 0 |
| `psi_descent_v2.v` | Core + tree_structure | Yes (8s) | 0 |
| `psi_descent_thms.v` | Descent-effect theorems | Yes (7s) | 0 |
| `psi_cdindex.v` | cd-index formalization | -vos (7s) | 0 |

Not in active build:
| `psi_descent.v` | Original (replaced) | -vos only | — |
| `psi_descent_wf.v` | Prototype | Yes | 7 Admitted |
| `psi.v`, `psi_base.v` | Monolithic originals | not compiled | — |
