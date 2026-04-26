# Axioms status — COMPLETE (2026-04-24)

## Executive summary

**0 Axioms remain.** All 13 original axioms have been resolved:
- 11 proved across psi_core/psi_comm/psi_descent_v2/psi_descent_thms/psi_cdindex
- 1 proved via cd-index bridge (omega_proper_beta_lt, in perm_seq_bridge.v)
- 1 eliminated as **mathematically false** (beta_swap_lt_caseB)

The final theorem `beta_alt_max` (alternating descent set maximises beta)
is fully proved with **zero axioms and zero Admitted**.

---

## 1. Resolved items (this session)

### omega_proper_beta_lt — PROVED (was Axiom in beta_bridge.v)

**Stanley Prop 1.6.4**: `omega_set D \proper omega_set E -> beta D < beta E`.

Proved in `perm_seq_bridge.v` via M-class injection argument:
1. `phi_w_support_general` (proved in psi_cdindex.v): X ∈ expand_cde(Φ_w) iff S_w ⊆ ω(desc(X))
2. `omega_monotone_class_count` (proved in psi_cdindex.v): subset monotonicity
3. `strict_witness_exists` (proved in psi_cdindex.v): strict witness for k ∈ ω(E)\ω(D)
4. `class_map` injection within M-classes + `char_mono_class_inj` injectivity
5. `seq_to_perm` / `perm_to_seq` bijection for type bridge

Infrastructure in perm_seq_bridge.v (~580 LOC):
- perm_to_seq / seq_to_perm with round-trip lemmas
- is_descent_perm_seq: descent equivalence perm ↔ seq
- char_mono_perm_to_seq: char_mono(perm_to_seq s) = descent_to_bvec(descent_set s)
- M-class helpers: apply_psis_revK, powerset_internal_apply_psis, char_mono_class_inj
- Omega bridge: omega_set_seq_bridge_bounded connecting finset and seq levels

### beta_swap_lt_caseB — ELIMINATED (was Axiom in beta_swap.v)

**The axiom was FALSE.** Counterexample:
- n=3, D={0,1}, i=0, j=1, q=2 (not in D)
- toggle_at {0,1} 1 = {0}
- beta({0,1}) = 3 = beta({0}) — equality, not strict inequality

The downstream theorem `beta_alt_max` is still TRUE, proved by a completely
different (and much simpler) argument:
1. `omega_set_alt_full`: ω(alt_desc_set) = setT (full set)
2. `not_set_is_alt_omega_not_full`: non-alternating D has ω(D) ≠ setT
3. `omega_proper_beta_lt`: ω(D) ⊊ ω(alt) = setT ⟹ β(D) < β(alt)

This bypasses the entire beta-swap chain (6 intermediate lemmas removed).

### phi_w_support_general — PROVED (in psi_cdindex.v)

Support characterization for cd-index expansion (~350 LOC added):
- `expand_cde_mem_iff`: X ∈ expand_cde(m) iff all D-offset transitions hold
- `has_transition_omega_seq`: bit transition ↔ omega_seq membership
- `cde_total_width_phi_w`: total cd-width of phi_w = (size w).-1
- `D_offsets_phi_w_eq_S_w_seq`: D-offsets match S_w_seq
- Main theorem proved by combining these components

### char_mono_phi_w_injective — ELIMINATED (was proposed Axiom)

**Also FALSE.** Counterexample:
- w1 = [2;1;3;4], w2 = [3;1;2;4]
- Same phi_w = [D; C], same char_mono = [true; false; false]
- perm_eq w1 w2, but w1 ≠ w2

Replaced by the correct, weaker `char_mono_class_inj`: within the M-class
(apply_psis orbit) of a given sequence, char_mono is injective. This
follows from fact3 + uniq_expand_cde.

---

## 2. Previously resolved (prior sessions)

### Phase A — Standalone axioms (4 proved)

| Axiom | Strategy |
|-------|----------|
| `window_trichotomy` | Strong induction on size, 9-way case analysis |
| `endpoint_implies_next_has_left_child` | Induction on tree, 3 cases |
| `LR_pred_is_endpoint` | Induction + helper `window_size_last` |
| `strict_witness_exists` | Explicit witness construction |

### Phase B — Shape stability (5 proved)

| Axiom | Strategy |
|-------|----------|
| `window_size_psi` | Order-isomorphism argument |
| `has_left_child_psi` | Same via `has_left_child_order_iso` |
| `psi_comm_disjoint` | 5-region nth extensionality |
| `window_size_psi_ancestor` | Corollary of `window_size_psi` |
| `psi_comm_nested` | Shape stability + modular arithmetic |

### Phase C — Fact #3 (1 proved)

| Axiom | Strategy |
|-------|----------|
| `fact3` | Decidable predicate + reflection + structural decomposition |

### M4 descent-effect (4 proved, fully -vo verified)

| Lemma | Status |
|-------|--------|
| `descent_psi_R_add` | Proved (-vo verified, 7s) |
| `descent_psi_R_remove` | Proved (-vo verified, 7s) |
| `descent_psi_LR_swap1` | Proved (-vo verified, 7s) |
| `descent_psi_LR_swap2` | Proved (-vo verified, 7s) |

---

## 3. Final dependency graph

```
M2 psi_involutive ------------- DONE
M3 psi_comm ------------------- DONE
M4 descent axioms (10) -------- DONE (fully -vo verified)
M5 fact3 ---------------------- DONE
M6 phi_w_support_general ------ DONE (this session)
   strict_witness_exists ------- DONE
   omega_monotone_class_count -- DONE

perm_seq_bridge (NEW) --------- DONE (this session)
  omega_proper_beta_lt --------- DONE (this session)
  beta_swap_lt_caseA ----------- DONE (derived from omega_proper_beta_lt)

beta_swap_lt_caseB ------------ ELIMINATED (false axiom)
beta_alt_max ------------------- DONE (direct omega proof, this session)
```

---

## 4. File inventory (final)

| File | Role | Axioms | Admitted |
|------|------|--------|----------|
| `mmtree.v` | Min-max tree datatype | 0 | 0 |
| `psi_core.v` | Core psi definitions | 0 | 0 |
| `psi_comm.v` | Psi commutativity | 0 | 0 |
| `psi_descent_v2.v` | Core + tree_structure | 0 | 0 |
| `psi_descent_thms.v` | Descent-effect theorems | 0 | 0 |
| `psi_cdindex_defs.v` | cd-index definitions | 0 | 0 |
| `psi_cdindex_tree.v` | Tree-shape proofs (heavy, ~80GB -vo) | 0 | 0 |
| `psi_cdindex_core.v` | Remaining lemmas + re-exports | 0 | 0 |
| `psi_cdindex_witness.v` | S_w, omega, strict witness | 0 | 0 |
| `psi_cdindex_support.v` | phi_w_support + structural fact3 | 0 | 0 |
| `ordinal_reindex.v` | Ordinal helpers | 0 | 0 |
| `perm_compress.v` | Permutation compression | 0 | 0 |
| `descent.v` | Descent statistics | 0 | 0 |
| `eulerian.v` | Eulerian polynomials | 0 | 0 |
| `beta.v` | Beta polynomials | 0 | 0 |
| `beta_omega.v` | Omega-set infrastructure | 0 | 0 |
| `beta_bridge.v` | Set/seq bridge | 0 | 0 |
| `perm_seq_bridge.v` | Perm/seq bridge | 0 | 0 |
| `beta_swap.v` | beta_alt_max | 0 | 0 |
| **TOTAL** | **19 files** | **0** | **0** |

Note: the original `psi_cdindex.v` was split into 5 files
(defs/tree/core/witness/support) to manage -vo compilation memory.
The heaviest file (tree.v) uses extracted forall bodies +
abstract wrappers to reduce peak memory from 124GB to ~80GB.
The structural proof of fact3 (in support.v) avoids vm_compute
entirely, using phi_w_support_general + perm_eq reasoning.

---

## 5. Don't-repeat-these-mistakes log

1-13. (From prior sessions, still apply.)

14. **False axioms exist.** `beta_swap_lt_caseB` (per-step strict monotonicity
    of beta under toggle) was false — counterexample n=3, D={0,1}. Always
    test axioms computationally before investing in proofs.

15. **False "obvious" injectivity.** `char_mono_phi_w_injective` (tree structure
    + descent pattern determines sequence) was false — [2;1;3;4] vs [3;1;2;4].
    The correct statement restricts to within a single M-class.

16. **Direct proofs beat swap chains.** The original beta_alt_max proof went
    through 6 intermediate swap lemmas (one false). The direct omega-set proof
    is 30 lines: ω(alt) = setT, non-alt has ω ⊊ setT, apply Prop 1.6.4.

17. **`by rewrite ... /=` can OOM.** The `simpl` tactic on large terms produces
    enormous proof terms that crash -vo compilation. The check_fact3_true closing
    `by rewrite /check_fact3 /apply_psis /=` used >100GB. Fix: structural proof
    via perm_eq_from_subset (membership + injectivity + size equality). Also:
    split large files to serialize proof terms independently.

18. **Circular dependency from structural proofs.** The structural fact3 proof
    uses phi_w_support_general (downstream of fact3 in the original monolith).
    Fix: split into core (definitions) / witness / support (phi_w_support +
    fact3). fact3 lives in support, after phi_w_support_general.

19. **Inline forall bodies cause exponential proof term duplication.** When a
    large proof term is passed as a `forall` argument to a recursive lemma
    (e.g., has_left_child_order_iso), the IH duplicates the body at every
    recursive call, causing exponential blowup. In psi_cdindex_tree.v, a
    39-line forall body caused 124GB OOM. Fix: extract the body into a
    standalone opaque lemma (behead_rank_shift_order_iso), pass by reference.
    Combined with `abstract(...)` wrappers on all case branches.

20. **`abstract(...)` reduces serialization, not peak computation memory.**
    It wraps proof terms in opaque constants for .vo output, but the kernel
    still builds the full term during checking. For exponential blowup (lesson
    19), extraction is needed; `abstract` alone is insufficient.
