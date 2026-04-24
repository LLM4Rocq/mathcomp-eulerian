# psi_descent.v: Status and Next Steps

## RESOLVED (2026-04-24)

Option A (structural recursion on mmtree) was implemented successfully.
The original `psi_descent.v` is replaced by:
- `psi_descent_v2.v` — core + tree_structure (8s, 151KB .vo)
- `psi_descent_thms.v` — descent-effect theorems (7s, 82KB .vo)

Total: 15 seconds, 233KB, 0 Admitted. See `OPTION_A_PROGRESS.md`.

---

## Original State (2026-04-22, now historical)

### What works
- All files compile with `rocq compile -vos` (signature checking, no proof verification)
- All files EXCEPT `psi_descent.v` and `psi_cdindex.v` compile with full `-vo`
- The file `psi_descent.v` passes `-vos` (all types, statements, and imports are correct)
- `psi_cdindex.v` also passes `-vos` against `psi_descent.vos`

### What doesn't work
- `psi_descent.v` cannot compile with full `-vo` in any reasonable time
- Attempted compilation ran for 50 hours, consumed 243 GB RAM, and was still growing
- The `.vo` file was never produced

### Build command
```bash
# Full build (everything except psi_descent and psi_cdindex):
make   # or individually with rocq compile

# Then -vos for the two problematic files:
rocq compile -vos -q -w -deprecated-library-file -w -notation-overridden \
  -R . mathcomp_eulerian psi_descent.v
rocq compile -vos -q -w -deprecated-library-file -w -notation-overridden \
  -R . mathcomp_eulerian psi_cdindex.v
```

---

## The Problem

`psi_descent.v` proves Stanley's Fact #2: how the rank-shift operator `psi_i`
changes the descent set of a permutation. The file has 5 structural lemmas
that each use **strong induction on `size w`** with a **3-way case split** at
`mm_pos` (the min-max tree splitting point):

1. `post_window_extremum` -- element after window is ancestor extremum
2. `pre_window_lt_max_when_min_head` -- Case LR boundary when head=min
3. `pre_window_gt_min_when_max_head` -- Case LR boundary when head=max
4. `exactly_one_descent_LR` -- XOR property at positions i-1, i
5. `pre_window_extremum_R` -- Case R boundary

These proofs generate **massive proof terms** because:
- Strong induction on nat (`elim=> [|n IH]`) carries the full context at each level
- The 3-way case split (`case: (ltngtP i j)`) triples the term at each level
- The `has_left_child_cons`, `window_size_cons`, `window_at_cons` lemmas unfold
  recursive definitions, adding more term structure
- The kernel's Qed verification and `.vo` serialization scale super-linearly
  with proof term size

### What was tried and didn't help

| Approach | Effect | Why it failed |
|----------|--------|---------------|
| `abstract` on `has_left_child_cons` | Sped up Qed checks ~3x | Didn't reduce .vo serialization |
| `#[global] Opaque` on all major lemmas | No effect | Only prevents unfolding by other files |
| Proof decomposition (13 Local Lemmas) | ~15% memory reduction | Each branch still has large proof term |
| Unified `tree_structure` lemma (1 recursion instead of 5) | ~20% reduction | One large term ~ five medium ones |
| `Function` (well-founded recursion) for `has_left_child` | Prototype worked | Only addresses has_left_child, not the 5 proofs |

**Key insight:** All these approaches reorganize the same proof terms without
reducing their fundamental size. The proof strategy itself generates terms that
grow without bound during serialization.

---

## Recommended Next Steps

### Option A: Structural recursion on `mmtree` (recommended)

The current proofs work on `seq nat` and recurse by splitting at `mm_pos`.
Instead, prove properties directly on the `mmtree nat` datatype defined in
`mmtree.v`:

```coq
Inductive mmtree (A : Type) : Type :=
  | Leaf : A -> mmtree A
  | Node : A -> mmtree A -> mmtree A -> mmtree A.
```

**Why this should help:**
- Structural recursion on `mmtree` is directly supported by Coq's termination checker
- No need for strong induction with size bounds
- No fuel pattern, no `elim=> [|n IH]`
- The 3-way case split becomes structural pattern matching (`Leaf` vs `Node`)
- Proof terms should be dramatically smaller

**What's needed:**
- Define `window_size`, `has_left_child`, `is_descent` on `mmtree`
- Prove the 5 structural properties by structural induction
- Bridge back to `seq nat` via `mmtree_to_seq` / `mmtree_of_seq`

**Risk:** The bridge lemmas between tree and sequence representations may be
complex. The descent predicate is defined on sequences (positions), not trees
(nodes), so translating between them requires work.

### Option B: Reflection / `vm_compute`

Use computational reflection to verify the descent-set effect:
- Define a boolean decision procedure that checks Fact #2 for a given input
- Prove the procedure correct by a small kernel of lemmas
- Use `vm_compute` or `native_compute` for the heavy verification

**Why this should help:**
- `vm_compute` runs in the OCaml VM, not the kernel -- much faster
- Proof terms are small (just "the computation returned true")
- No induction, no case splits in the proof term

**Risk:** Requires designing the decision procedure carefully. May not
generalize well if the property needs to hold for all `n`.

### Option C: Accept `-vos` workflow

Use `-vos` for development and treat full verification as a separate concern:
- All type checking and statement verification works with `-vos`
- Proofs are present in the source but not kernel-verified
- This is standard practice for large Coq developments during active work

**When to revisit:** Once the formalization is complete and you want to produce
a fully verified artifact, apply Option A or B to the final version.

---

## File Inventory

### Core files (in dependency order)
| File | Lines | Compiles -vo? | Notes |
|------|-------|---------------|-------|
| `mmtree.v` | ~200 | Yes | Min-max tree datatype and operations |
| `ordinal_reindex.v` | ~100 | Yes | Ordinal reindexing helpers |
| `perm_compress.v` | ~150 | Yes | Permutation compression |
| `descent.v` | ~200 | Yes | Descent set on permutations |
| `eulerian.v` | ~300 | Yes | Eulerian polynomials |
| `beta.v` | ~200 | Yes | Beta polynomials |
| `beta_swap.v` | ~300 | Yes | Beta-swap axioms |
| `psi_core.v` | ~1950 | Yes | Core psi definitions and lemmas |
| `psi_comm.v` | ~1360 | Yes | Psi commutativity |
| `psi_descent.v` | ~1576 | **-vos only** | Descent-set effect of psi |
| `psi_cdindex.v` | ~1950 | **-vos only** | cd-index formalization |

### Auxiliary files
| File | Purpose |
|------|---------|
| `psi_base.v` | Combined M2+M3+M4 (alternative monolithic version) |
| `psi_descent_wf.v` | Prototype: `Function`-based `has_left_child_wf` |
| `M4_DESCENT_EFFECT_INFORMAL.md` | Informal proof of Fact #2 (detailed, ~1000 lines) |
| `refs/` | Reference materials (Stanley EC1 excerpts) |

### Current `psi_descent.v` structure (unified version)
The file uses a single `tree_structure` lemma that bundles all 5 structural
properties into one conjunction, proved by one strong induction. The 5 public
lemmas are trivial projections. The 4 descent-effect theorems
(`descent_psi_R_add`, `descent_psi_R_remove`, `descent_psi_LR_swap1`,
`descent_psi_LR_swap2`) are proved using helper lemmas that do not recurse.

---

## Key API Surface

### From `psi_descent.v`
```
is_descent_seq : seq nat -> nat -> bool
has_left_child : nat -> seq nat -> bool
has_left_child_0 : forall s, has_left_child 0 s = false
has_left_child_cons : (* unfolding lemma *)

post_window_extremum
pre_window_lt_max_when_min_head
pre_window_gt_min_when_max_head
exactly_one_descent_LR
pre_window_extremum_R

descent_psi_R_add      (* D(psi w) = D(w) u {i} *)
descent_psi_R_remove   (* D(psi w) = D(w) \ {i} *)
descent_psi_LR_swap1   (* D(psi w) = (D(w) u {i}) \ {i-1} *)
descent_psi_LR_swap2   (* D(psi w) = (D(w) u {i-1}) \ {i} *)
```

---

## Compilation Measurements (for reference)

All attempts on a 3 TB RAM node, single worker (`-j1`):

| Attempt | Duration | Peak RSS | Finished? |
|---------|----------|----------|-----------|
| Original (5 recursions) | 16h | 156 GB | No (killed) |
| + `abstract` | 10h | 210 GB | No (killed) |
| + `Opaque` | same | same | No (killed) |
| + decomposition | 22h | 219 GB | No (killed) |
| Unified `tree_structure` | 50h | 243 GB | No (killed) |
