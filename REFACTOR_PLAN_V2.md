# Refactor Plan V2 — Tree-Native Re-Architecture

Result of a fresh 3-agent investigation (mathematician / Rocq architect / devil's
advocate) after V1 (`REFACTOR_PLAN.md`) and 2.5 hours of compile-time confirmed
that surgical fixes cannot get the 3 holdout files to `.vo`.

This plan is **staged with explicit go/no-go gates**. Devil's advocate raised
substantive risks; the response is not to ignore them but to prove or disprove
each before committing further work.

## TL;DR

- The kernel-cost wall is caused by a representation choice, not the math.
- We encoded Stanley's *unlabelled min-max tree* as `seq nat` plus fuel-Fixpoints
  (`mm_pos`, `window_size_fuel`, `has_left_child_fuel`). Every heavy proof
  reconstructs tree-structure facts from seq-level inductions.
- Stanley himself **does not induct on `seq nat`** — he reasons structurally on
  the tree. The successful local refactor (`psi_cdindex_tree_shape.v`) already
  validated tree-structural induction at scale.
- **Proposed move:** introduce a tree-shape inductive (`cdstring`) and route the
  3 holdout files' proofs through it. Estimated reduction: ~2638 LoC → ~1150 LoC.
- **Risk:** the rewrite could fail to `.vo` for the same hardware reasons. Or
  re-introduce false lemmas the .vos catches accept.
- **Mitigation:** a two-day spike on the smallest first step (Phase 0 below)
  must `-vo`-pass before any further work commits. If the spike fails, **stop
  and accept `.vos`** as the project's terminal state.

## What we know after the V1 attempt (do not re-investigate)

1. The bottleneck is `D_vertex_descent_transition` (`psi_cdindex_support.v:1064`),
   specifically its `have Hint_L: is_internal i (take j s)` block that does
   `rewrite (window_size_cons ...) ... in Hws`.
2. Both V1 fixes failed at `-vo`:
   - Hoisting heavy `have`-blocks into Qed-opaque helpers: killed at 38 GB / 36 min.
   - Adding `Arguments window_size_fuel : simpl never.`: killed at 111 GB / 97 min
     (worse — `simpl never` is tactic-level, the kernel ignores it during Qed
     conversion checking).
3. `Opaque`/`Transparent` are also tactic-level and don't bind the kernel.
4. The only previously-successful pattern in this repo is `mmtree_shape` in
   `psi_cdindex_tree_shape.v`: a sealed structural shape feeds a single heavy
   `Qed` lemma; downstream consumers see the shape as a black box. That
   pattern cut a similar `>131 GB` blowup to `8 s, 0.6 GB`.

## Where the math drifted from Stanley (mathematician's finding)

| Object in our code | Stanley EC1 §1.6 | Status |
|--------------------|------------------|--------|
| `mmtree nat` (`mmtree.v`) | `M(w)`, the min-max tree | **Stanley's** — keep |
| `mm_pos`, `window_size_fuel`, `has_left_child_fuel` | reconstructions of split-point / right-subtree-size / has-left-child from `seq nat` | **Ours** — Stanley reads these directly off the tree |
| `phi_w : seq nat → seq cde` (`psi_cdindex_defs.v:48`) | `Φ_w` ∈ `Z⟨c,d⟩`, a tree-shape readout | **Ours** — Coq-friendly proxy, not Stanley's primary object |
| `expand_cde : seq cde → seq (seq bool)` | substitution `c↦a+b, d↦ab+ba` | Faithful but lives in wrong category (lists vs. polynomials) |
| `S_w_seq` (`psi_cdindex_witness.v:38`) | `S_w ⊂ [n−2]` | Faithful but indexed via fuel traversal |
| M-equivalence as orbit on `seq nat` | orbit of `G_w ≅ (Z/2Z)^{ι(w)}` on `M(w)` | **Ours** — moved to seq, losing tree structure |

`refs/stanley_1_6_cdindex.txt` confirms Stanley reads `Φ_w` off the *unlabelled*
tree shape (line 291), which depends only on `M(w)`. Our `phi_w` filters
`iota 0 (size w)` and reconstructs the same tree shape from seq positions —
that's the source of the heavy inductions.

## Where the implementation should converge (architect's finding)

The clean win is **not** a full migration to `{perm 'I_n}` (that would invalidate
~70% of the existing `.vo` tier — see devil's advocate #1, #6). It is a smaller,
targeted move: introduce a **structural cd-string inductive** to replace the
fuel-Fixpoint induction skeleton:

```coq
Inductive cdstring : Type :=
| cdEmpty   : cdstring
| cdC       : cdstring -> cdstring                  (* prepend a c-letter *)
| cdD       : cdstring -> cdstring                  (* prepend a d-letter *)
| cdSplit   : cdstring -> cdstring -> cdstring.     (* internal-vertex split *)
```

Then `phi_struct : forall (w : seq nat), uniq w -> cdstring`, sealed `Opaque`
with the `mmtree_shape` pattern, plus a single `phi_struct_to_phi_w` reconciliation
lemma. All downstream heavy proofs become structural inductions on `cdstring`,
each `Qed` constant-time.

This is **Stanley's tree-as-structural-object viewpoint** restricted to the cd-letter
readout — the minimum reformulation that closes the kernel-cost gap without
demolishing the working `.vo` tier.

## Build-isolation map

`.vo` files (18) form a closed forest rooted in 5 tier-A leaves
(`eulerian.v`, `descent.v`, `beta.v`, `beta_omega.v`, `beta_bridge.v`) and the
tier-B chain ending at `psi_cdindex_witness.v`. **None of the 18 `.vo` files
depend on any of the 3 holdouts.** The holdouts are pure leaves; they can be
deleted/replaced in isolation.

```
Tier-A (perm/finset, all .vo):
  ordinal_reindex < perm_compress < descent < eulerian < beta < beta_omega < beta_bridge

Tier-B (psi/cdindex, all .vo):
  mmtree < psi_core < psi_comm < psi_descent_v2 < psi_descent_thms <
  psi_cdindex_defs < psi_cdindex_tree_shape < psi_cdindex_tree_hlc <
  psi_cdindex_tree < psi_cdindex_core < psi_cdindex_witness

Holdouts (3, all leaves, .vos only):
  psi_cdindex_support  (1312 LoC; pulls Tier-B)
  perm_seq_bridge      (1025 LoC; pulls Tier-A + Tier-B + support)
  beta_swap            ( 301 LoC; pulls everything above)
```

The strongest theorem provable from `.vo` files alone is the omega-block
machinery in `beta_omega.v` and the eulerian row-sum in `eulerian.v`. **The
headline β-monotonicity theorem `beta_alt_max` (`beta_swap.v:273`) and
`omega_proper_beta_lt` (`perm_seq_bridge.v:543`) are not in any `.vo`.** That
is the actual gap this refactor closes.

## Devil's-advocate critique and how we respond

**1. Sunk cost / interface invalidation.** *Critique:* a "back to Stanley"
rewrite invalidates the seq-based interfaces in `psi_core.v`, `psi_comm.v`,
`psi_descent_v2.v`. *Response:* the proposed plan does **not** change those
files. They stay verbatim in Tier 1. The new `cdstring` inductive lives in
new files; existing seq-level lemmas are reused via the bridge `phi_struct_to_phi_w`.

**2. Bottleneck is mathematical, not stylistic.** *Critique:* `D_vertex_descent_transition`
case-splits on `i < mm_pos s` regardless of representation. *Response:* True for
that specific lemma — but the cost is in *kernel reduction of fuel-Fixpoints*,
not in case-splits. Structural induction on a *sealed inductive* (cdstring)
removes the fuel parameter from the proof term. We will **prove this on one
lemma in Phase 0** before scaling up.

**3. Stanley's proof is incomplete prose.** *Critique:* Stanley says "we just
sketch the basic facts." *Response:* Granted — we are not copying Stanley
verbatim. We are adopting his *structural object* (tree-shape) and re-proving
the omitted Facts on it. The new proofs are still our work; only the ambient
type changes.

**4. `.vos` is already publishable.** *Critique:* `coqchk` validates 0 axioms
at `.vos`; `.vo` adds no soundness gain here. *Response:* This is the most
important counter. The plan **explicitly preserves `.vos` as a tagged fallback**
(see Phase −1 below). If Phase 0 fails, we accept `.vos` as the terminal state.

**5. Hardware-bound.** *Critique:* 188 GB / 4 cores may be insufficient for
*any* representation. *Response:* The `psi_cdindex_tree_shape.v` evidence
disproves the strong form (8 s, 0.6 GB on a structurally-similar refactor). The
weak form is acknowledged; Phase 0 is the proof.

**6. `{perm 'I_n}` rewrite makes some proofs HARDER.** *Critique:* `is_descent_seq_take`
and friends become ordinal-coercion-heavy. *Response:* Agreed; **we are NOT doing
the {perm} rewrite.** The cdstring move keeps `seq nat` at the boundary and
just changes the *internal* induction object.

**7. False-lemma regression risk.** *Critique:* memory note records that
`beta_swap_lt_caseB` and `char_mono_phi_w_injective` were false and only caught
computationally. A rewrite could re-introduce similar bugs that `.vos` accepts.
*Response:* Phase 0 includes a `vm_compute` regression suite re-run on the new
`phi_struct` definition before any consumer migrates. Plus: every replaced
lemma keeps its original statement verbatim (only the proof body changes).

## Phase −1: Safety net (mandatory; do this before any other work)

```bash
# Tag the current .vos-clean state with 0 axioms / 0 Admitted.
git add -A && git commit -m "checkpoint: pre-refactor-v2, .vos-clean, 0 axioms"
git tag -a v1-vos-stable -m "Last commit before tree-native refactor (V2)"
git push origin v1-vos-stable
```

If this tag exists, the refactor is reversible; if any phase fails, `git reset
--hard v1-vos-stable` returns to a verified artifact.

## Phase 0: Smallest-first-step spike (1–2 days, GO/NO-GO gate)

Goal: prove the cdstring approach actually `-vo`-compiles ONE of the heavy
lemmas before touching the rest.

**Target lemma:** `cde_total_width_phi_w_all` (`psi_cdindex_support.v:711`,
80 LoC, was the second-heaviest `Qed` after `D_vertex_descent_transition`).

**Steps:**

1. Create `cdstring.v` requiring only `mathcomp.all_ssreflect`:
   - `Inductive cdstring` (4 constructors above).
   - `Fixpoint cdstring_width : cdstring -> nat` (structural recursion).
   - 5–10 lines of basic lemmas.
2. Create `cdstring_phi.v` requiring `cdstring`, `psi_cdindex_defs`, `mmtree`:
   - `Definition cde_to_cdstring : seq cde -> cdstring` (5 LoC, structural).
   - `Lemma cde_total_width_eq_cdstring_width : cde_total_width m =
     cdstring_width (cde_to_cdstring m)` (~10 LoC, kernel-cheap).
3. Create `cdstring_phi_w.v` requiring above + `psi_cdindex_witness`:
   - `Definition phi_struct : forall (w : seq nat), uniq w -> cdstring`
     using well-founded recursion on `size w` with `mmtree_shape` as the
     decreasing measure. **Seal it `Opaque` after a `*_cons` API lemma**, mirroring
     `psi_cdindex_tree_shape.v`'s `mmtree_shape_fuel`.
   - `Lemma cde_total_width_phi_w_all_v2 : forall w, uniq w ->
     cde_total_width (phi_w w) = (size w).-1.`
     Proof by structural induction on `phi_struct w Hu`, *not* by strong induction
     on `size w <= n`.

**Gate:** `coqc -vo cdstring_phi_w.v` succeeds in **under 30 minutes with peak
RSS under 32 GB**.

- **Success →** Phase 1.
- **Failure (OOM or timeout) →** STOP. Devil's advocate's critique #5 confirmed.
  Accept `.vos` as terminal. Document outcome in `BUILD_PLAN.md`.

The bar is deliberately tight: `psi_cdindex_tree_shape.v` ran 8 s / 0.6 GB. If
the cdstring spike costs more than 50× that, the pattern doesn't generalize.

## Phase 1: Migrate Stratum B lemmas (3–5 days)

Conditional on Phase 0 success.

Migrate the three `phi_w_*` lemmas all sharing the same induction skeleton:

| Old lemma | File:line | Replacement |
|-----------|-----------|-------------|
| `cde_total_width_phi_w_all` | `psi_cdindex_support.v:711` | done in Phase 0 |
| `D_offsets_phi_w_eq_S_w_seq` | `psi_cdindex_support.v:803` | new file `cdstring_offsets.v` |
| `D_vertex_descent_transition` | `psi_cdindex_support.v:1064` | new file `cdstring_descent.v` (uses `cdstring_offsets`) |

Each uses the same pattern: structural induction on `phi_struct w Hu`, with
the fuel parameter (`size w <= n`) gone. All three have the same case-split
shape so they share helpers in `cdstring.v`.

**Gate after Phase 1:** `psi_cdindex_support.v` rewritten as a thin wrapper
that re-states the old API in terms of the new lemmas. The whole file builds
to `.vo` in under 30 minutes / 32 GB.

## Phase 2: Trim `perm_seq_bridge.v` and `beta_swap.v` (2 days)

Conditional on Phase 1 success.

The architect predicts these "just work" once support is `.vo` (the model from
the tree-shape refactor: downstream files become kernel-elaborable once the
opaque-sealed bottleneck is in place). If they don't:

- `perm_seq_bridge.v`: factor out the `desc_bvec` bijection (V1 plan §perm_seq_bridge
  was right about this; the cdstring refactor doesn't change that part).
- `beta_swap.v`: 301 LoC, smallest. Build last.

**Gate after Phase 2:** all 21 files at `.vo`, 0 axioms, 0 Admitted.

## Phase 3: Cleanup (1 day)

- Delete `psi_cdindex_support.v` (replaced by cdstring chain).
- Delete `REFACTOR_PLAN.md` (superseded by this V2).
- Update `BUILD_PLAN.md` with final state.
- Tag `v2-vo-complete`.

## What does NOT change

- All 18 currently-`.vo` files stay verbatim, including `mmtree.v`, `psi_core.v`,
  `psi_comm.v`, `psi_descent_v2.v`, `psi_descent_thms.v`, `psi_cdindex_defs.v`,
  `psi_cdindex_tree*.v`, `psi_cdindex_core.v`, `psi_cdindex_witness.v`.
- The `seq nat` representation stays at the boundary (input to `phi_struct`).
- `mm_pos`, `window_size`, `has_left_child` stay as boundary predicates.
- All headline theorems keep their statements verbatim. Only proofs change.

## Stop conditions

1. **Phase 0 fails to `-vo` in 30 min / 32 GB.** Accept `.vos` and stop.
2. **Phase 1 introduces a false lemma** (caught computationally or by reviewer).
   Revert to `v1-vos-stable` and stop.
3. **Phase 2 reveals new dependencies** that pull in 50% more LoC than
   estimated. Re-evaluate before continuing.
4. **Total wall-clock exceeds 10 days.** Stop and accept `.vos`.

## What success looks like

- 21/21 `.vo`, 0 axioms, 0 Admitted.
- `coqchk -R . mathcomp_eulerian -silent -o mathcomp_eulerian.beta_swap` reports
  `Axioms: <none>`.
- `D_vertex_descent_transition`-style lemmas removed; replaced by structural
  inductions on `cdstring`.
- The `phi_struct` opacity boundary is the only place fuel-Fixpoints can hide.

## What "ok-to-fail" looks like

If we stop at the `.vos` state:

- `git tag v1-vos-stable` is the artifact.
- `BUILD_PLAN.md` already documents the rationale.
- 0 axioms / 0 Admitted at `.vos` is a publication-grade result.
- The `.vo` gap on 3 leaf files is documented as hardware-bound.
- This is **not a failure** — it is the upper bound of what 188 GB / 4 cores
  can validate at the kernel level for a formalization of this size.

## Appendices

### A. Files cited in this plan

- `BUILD_PLAN.md`, `REFACTOR_PLAN.md` (V1, superseded by this document)
- `psi_cdindex_tree_shape.v` (the proven shape pattern; Phase 0 model)
- `psi_cdindex_support.v` (the bottleneck; lines 711, 803, 1064)
- `psi_cdindex_defs.v:48` (`phi_w` definition; the conversion target)
- `mmtree.v` (the existing tree datatype)
- `refs/enu_comb_stanley.pdf` and `refs/stanley_1_6_cdindex.txt`
- `.claude/projects/-scratch-lelarge-mathcomp-eulerian/memory/feedback_false_axioms.md`

### B. Team-investigation summary

- **Mathematician** (read Stanley §1.4–§1.6 + the formalization): the drift is
  in the *ambient datatype*, not the math. Stanley uses the unlabelled tree as
  a structural object. Our `seq nat`-with-`mm_pos` reconstruction is the
  source of fuel-Fixpoint cost.
- **Architect** (read all 21 .v files + dep graph): proposes `cdstring`
  inductive + `phi_struct` opaque sealing. Smallest first migration:
  `cde_total_width_phi_w_all` (Phase 0). Two-tier file plan: keep 18 .vo
  files; replace 3 holdouts (~2638 LoC → ~1150 LoC).
- **Devil's advocate** (read the failure history + `.vos` rationale): 7
  falsifiable critiques. Most important: `.vos` is already publishable; the
  hardware constraint may be intrinsic; rewrite risks false-lemma regression.
  Recommendation: gated spike, hard stop conditions, preserve fallback tag.

The plan above incorporates each agent's findings explicitly.
