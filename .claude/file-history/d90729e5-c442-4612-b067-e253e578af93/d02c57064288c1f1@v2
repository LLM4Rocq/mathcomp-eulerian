---
name: Stanley EC1 PDF location
description: Location of Stanley Enumerative Combinatorics Vol 1 PDF and extracted sections relevant to β(S) theory and Foata/cd-index proofs
type: reference
originSessionId: d90729e5-c442-4612-b067-e253e578af93
---
Stanley, *Enumerative Combinatorics* Vol. 1 (2nd ed.) PDF is at `refs/enu_comb_stanley.pdf` (725 pages).

Key theorem for the Foata/descent β-axioms in `beta_swap.v`: **Proposition 1.6.4** — `ω(S) ⊂ ω(T) ⇒ βn(S) < βn(T)`, proved via cd-index nonneg. `ω(S)` = positions where exactly one of `i, i+1` is in S.

Pre-extracted plain text:
- `refs/stanley_1_4_descents.txt` — §1.4 Descents (pp.38–47): defines `α(S)`, `β(S)`, basic identities (1.31)–(1.35), Eulerian polynomials, w-compatible functions.
- `refs/stanley_1_6_cdindex.txt` — §1.6 Alternating permutations, Euler numbers, cd-index (pp.54–62): min-max tree M(w), ψi operators (Fact #2), Theorem 1.6.3 (cd-index with nonneg coefficients), Proposition 1.6.4, Corollary 1.6.5.

Poppler installed under `.local/poppler/` (needs `LD_LIBRARY_PATH=.local/poppler/lib`). To extract more pages:
`LD_LIBRARY_PATH=.local/poppler/lib .local/poppler/bin/pdftotext -f N -l M -layout refs/enu_comb_stanley.pdf out.txt`

**Why:** These extracts let future sessions (and subagents) cite the exact classical proof of the `beta_swap_monotone` / `beta_swap_lt` axioms without re-paging through the PDF, and without needing poppler on PATH in the harness.

**How to apply:** When working on `beta_swap.v` axiom elimination or related monotonicity results, point agents at these refs files. Edition note: §1.4 = Descents, §1.6 = Alternating perms + cd-index (differs from 1st-edition numbering cited in older sources).
