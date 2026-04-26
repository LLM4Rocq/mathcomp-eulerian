---
name: Slurm memory allocation
description: psi_descent compilation resolved (15s, <1GB); no special Slurm allocation needed
type: feedback
originSessionId: e78b04d9-7991-4d3e-8dbd-5cb72f2c77bd
---
RESOLVED (2026-04-24): psi_descent.v compilation blocker is fixed.

**Previous state (2026-04-22):** psi_descent.v could not compile -vo
(50h+, 243GB+, never finished). Required -vos workflow.

**Current state (2026-04-24):** Replaced by psi_descent_v2.v + psi_descent_thms.v.
Both compile with full -vo in 15 seconds total, <1GB RAM.
No special Slurm --mem allocation needed.

**Root causes fixed:**
1. Fuel-based strong induction → structural induction on mmtree (O(n) vs O(3^n) proof terms)
2. `rewrite !index_uniq ?... //` exponential search → explicit applications

**How to apply:** Just use `make` or `rocq compile`. No -vos workaround needed.
