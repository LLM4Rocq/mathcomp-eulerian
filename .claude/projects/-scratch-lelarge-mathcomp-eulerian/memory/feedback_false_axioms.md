---
name: False axioms discovered
description: beta_swap_lt_caseB and char_mono_phi_w_injective were mathematically false; always test axioms computationally
type: feedback
originSessionId: 55f0839d-14c6-45f5-8ac3-a206e1d5f957
---
Two axioms turned out to be mathematically FALSE during this formalization:

1. `beta_swap_lt_caseB`: claimed beta(D) < beta(toggle_at D j) for consecutive descents with j+1 ∉ D. Counterexample: n=3, D={0,1}, beta = 3 = 3.

2. `char_mono_phi_w_injective`: claimed (phi_w, char_mono) determines a sequence uniquely among perm_eq sequences. Counterexample: [2;1;3;4] vs [3;1;2;4].

**Why:** Always test axioms computationally (vm_compute for small n) before investing significant effort in proofs.

**How to apply:** When formalizing, add `Example` checks for small cases before declaring `Axiom`. Use `vm_compute` to verify axiom instances for n ≤ 5. A false axiom downstream can invalidate an entire proof chain — the devil's advocate role caught both.
