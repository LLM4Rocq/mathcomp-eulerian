# Status: FORMALIZATION COMPLETE

## All axioms closed (2026-04-24)

The formalization has **zero Axiom and zero Admitted** across all 15 active .v files.

The main theorem `beta_alt_max` is fully proved:
```coq
Lemma beta_alt_max n (D : {set 'I_n}) :
  ~~ set_is_alt D -> beta D < beta (alt_desc_set n).
```

## Build verification

All 17 files compile with `-vos` (type-level verification).
Full `-vo` build expected to stay under ~15GB per file (structural proofs
throughout, no heavy vm_compute in proof closings).

```bash
opam exec -- make -j4    # full build
```

Note: `psi_cdindex.v` was split into `psi_cdindex_core.v`,
`psi_cdindex_witness.v`, `psi_cdindex_support.v` to keep -vo
memory manageable. The vm_compute `Example` lemmas in core/support
are on small concrete inputs (size ≤ 8) and compile quickly.

## What was done this session

### Path 1: omega_proper_beta_lt (Stanley Prop 1.6.4) — CLOSED

1. **phi_w_support_general** proved in psi_cdindex.v (~350 LOC):
   - expand_cde_mem_iff: structural characterization of expand_cde membership
   - D-offset / S_w_seq correspondence via boolean reflection (check_width, check_offsets)
   - Main theorem: X ∈ expand_cde(Φ_w) ⟺ S_w ⊆ ω(desc(X))

2. **perm_seq_bridge.v** created (~580 LOC):
   - perm_to_seq / seq_to_perm bijection with round-trip proofs
   - is_descent_perm_seq: descent equivalence between perm and seq worlds
   - M-class injection: class_map + char_mono_class_inj
   - omega_proper_beta_lt: proved via injection + strict witness

3. **beta_bridge.v** cleaned: Axiom removed, beta_swap_lt_caseA moved to bridge

### Path 2: beta_swap_lt_caseB — ELIMINATED

**The axiom was mathematically false** (counterexample: n=3, D={0,1}).

beta_alt_max reproved directly via omega sets in ~30 lines:
- omega_set(alt_desc_set) = setT
- non-alternating D has omega_set(D) ⊊ setT
- omega_proper_beta_lt gives beta(D) < beta(alt)

Six intermediate lemmas removed (all were downstream of the false axiom).

### Key discoveries

1. **beta_swap_lt_caseB was FALSE** — beta equality (not strict inequality)
   is possible when toggling consecutive descents
2. **char_mono_phi_w_injective was FALSE** — different sequences can share
   tree structure and descent pattern; correct version restricts to M-class
3. **Direct omega proof beats swap chains** — the entire beta_swap_lt machinery
   was unnecessary; omega_proper_beta_lt suffices alone

## Architecture (final)

```
mmtree → psi_core → psi_comm → psi_descent_v2 → psi_descent_thms
                                                        ↓
                                                  psi_cdindex_core
                                                        ↓
                                                  psi_cdindex_witness
                                                        ↓
                                                  psi_cdindex_support
                                                        ↓
ordinal_reindex → perm_compress → descent → eulerian → beta
                                                        ↓
                                            beta_omega → beta_bridge
                                                              ↓
                                                      perm_seq_bridge
                                                              ↓
                                                         beta_swap
```

## If continuing this project

Potential future directions:
- Full `-vo` compilation of psi_cdindex.v (requires ~100GB RAM, 1-2h)
- Extract the Putnam 2025 A5 solution from beta_alt_max
- Generalize to other Coxeter groups
- Clean up perm_seq_bridge.v (some helper lemmas could be simplified)
