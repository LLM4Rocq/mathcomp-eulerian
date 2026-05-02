# Plan: `stirling_fiber.v` — `insert_after` construction and the §1.3.2 recurrence

> **Forward-looking design document.** Companion to
> [`INVERSIONS_PLAN.md`](INVERSIONS_PLAN.md).  Drafted after Session-2
> revealed that the `lift_perm`-based H2 was mathematically false:
> mathcomp's `perm.lift_perm i j s` is a *renaming* operation, not a
> cycle insertion.  This plan proposes the corrected path.

## 1. Why a new file

The Session-1 plan tried to use `perm.lift_perm ord_max j s` as the
"insert ord_max into s's cycle through j" operation.  Session-2
mechanically verified that this is wrong (concrete counterexample:
n=2, s=identity gives a 3-cycle σ instead of preserving the cycle
count).  The correct construction is an explicit "splice" perm we
call `insert_after` — semantically distinct from `lift_perm`.

Putting it in a separate file keeps `cycles_rec.v` (which has H1)
clean and lets the new file be added to `_CoqProject` only when the
full Stirling recurrence lands.

## 2. The construction

For `s : {perm 'I_n}` and `j0 : 'I_n`, define `insert_after j0 s :
{perm 'I_n.+1}` by:

- `insert_after j0 s ord_max = lift ord_max j0`
- `insert_after j0 s (lift ord_max p) = ord_max` where `p = s^{-1} j0`
  (i.e., the predecessor of `j0` under `s`)
- `insert_after j0 s (lift ord_max k) = lift ord_max (s k)` for all
  other `k : 'I_n`

**Cycle picture.** If the s-cycle through j0 reads
`p₁ → p₂ → ... → p_{r-1} → p_r = j0 → p₁`, then `insert_after j0 s`
modifies it to `p₁ → p₂ → ... → p_{r-1} → ord_max → j0 → p₁` (where
all the `pᵢ` get widened via `lift ord_max` and `j0` is now reached
from `ord_max` instead of from `p_{r-1}`).  All other s-cycles get
widened unchanged.  Cycle count is preserved.

**Concretely** (target signature):

```coq
Definition insert_after_fun (j0 : 'I_n) (s : {perm 'I_n}) (x : 'I_n.+1) :
  'I_n.+1 :=
  match unlift ord_max x with
  | None     => lift ord_max j0
  | Some k   => if k == s^-1 j0 then ord_max
                else lift ord_max (s k)
  end.

Lemma insert_after_fun_inj j0 s : injective (insert_after_fun j0 s).
Proof. (* ~30 LOC: case-split on unliftP and use s injective + lift_inj *) Qed.

Definition insert_after j0 s : {perm 'I_n.+1} := perm (insert_after_fun_inj j0 s).
```

## 3. Required lemmas

| Lemma | Statement | Estimated LOC |
|-------|-----------|---------------|
| `insert_after_fun_inj` | injectivity of the underlying function | ~30 |
| `insert_after_ord_max` | `insert_after j0 s ord_max = lift ord_max j0` | 5 |
| `insert_after_pred` | `insert_after j0 s (lift ord_max (s^-1 j0)) = ord_max` | 10 |
| `insert_after_other` | `k != s^-1 j0 → insert_after j0 s (lift ord_max k) = lift ord_max (s k)` | 10 |
| `cycle_count_insert_after` | `cycle_count (insert_after j0 s) = cycle_count s` | ~80–120 |
| `insert_after_ord_max_neq` | `insert_after j0 s ord_max != ord_max` (immediate) | 5 |

The headline `cycle_count_insert_after` is the analogue of H1 in
spirit, but the orbit decomposition is more delicate because one
s-cycle gets *modified* (extended by ord_max) rather than
*augmented as a singleton*.

## 4. Inverse and bijection

For the bijection, define `extract_perm` with hypothesis
`σ ord_max != ord_max`:

```coq
Definition extract_perm_fun (σ : {perm 'I_n.+1}) (k : 'I_n) : 'I_n :=
  if σ (lift ord_max k) == ord_max
  then odflt k (unlift ord_max (σ ord_max))
  else odflt k (unlift ord_max (σ (lift ord_max k))).

(* extract_perm_fun shorts out ord_max in σ's cycle: the predecessor
   of ord_max is sent directly to σ ord_max (= lift ord_max j0). *)

Definition extract_perm σ : {perm 'I_n} := perm (extract_perm_fun_inj σ).
```

| Lemma | Statement | Estimated LOC |
|-------|-----------|---------------|
| `extract_perm_fun_inj` | injectivity of extract | ~40 |
| `insert_after_extractK` | `σ ord_max != ord_max → insert_after (unlift_ord_max (σ ord_max)) (extract_perm σ) = σ` | ~30 |
| `extract_insert_afterK` | `extract_perm (insert_after j0 s) = s` | ~30 |
| `unlift_ord_max_insert_after` | `unlift ord_max ((insert_after j0 s) ord_max) = Some j0` | 10 |

These together establish the bijection
```
{σ : {perm 'I_n.+1} | σ ord_max != ord_max} ↔ 'I_n * {perm 'I_n}
```
where the first component is `unlift_ord_max (σ ord_max)` and the
second is `extract_perm σ`.

## 5. Per-fiber count

```coq
Lemma stirling_fiber_neq n k j (Hj : j != ord_max) :
  #|[set σ : {perm 'I_n.+1} | (σ ord_max == j) && (cycle_count σ == k.+1)]|
  = #|[set s : {perm 'I_n} | cycle_count s == k.+1]|.
```

Proof: bijection σ ↔ extract_perm σ; cycle counts coincide by
`cycle_count_insert_after`.

```coq
Lemma stirling_fiber_eq n k :
  #|[set σ : {perm 'I_n.+1} | (σ ord_max == ord_max) && (cycle_count σ == k.+1)]|
  = #|[set s : {perm 'I_n} | cycle_count s == k]|.
```

Proof: bijection σ ↔ "σ minus the ord_max fixed point" which is
exactly the H1 setup; cycle count drops by 1.  Already most of the
ingredients exist in `cycles_rec.v` H1.

## 6. Assembly

```coq
Lemma stirling_c_rec n k :
  stirling_c n.+1 k.+1 = n * stirling_c n k.+1 + stirling_c n k.
Proof.
rewrite /stirling_c -sum1_card.
rewrite (partition_big (fun σ : {perm 'I_n.+1} => σ ord_max) xpredT) //=.
rewrite (bigD1 ord_max) //= addnC.
(* main "tail" sum: n choices of j != ord_max, each gives stirling_c n k.+1 *)
rewrite (eq_bigr (fun _ => stirling_c n k.+1)); last by …
  rewrite … sum_nat_const card_… mulnC.
(* "head" term: σ ord_max = ord_max, gives stirling_c n k *)
rewrite stirling_fiber_eq.
ring.
Qed.
```

Estimated assembly: ~50 LOC.

## 7. Total scope

| Section | LOC | Difficulty |
|---------|-----|------------|
| `insert_after` def + injectivity | ~50 | low |
| `cycle_count_insert_after` | ~120 | **high** (orbit reasoning) |
| `extract_perm` def + injectivity | ~60 | medium |
| `insert_after_extractK` / `extract_insert_afterK` | ~60 | medium |
| `stirling_fiber_neq` / `stirling_fiber_eq` | ~80 | medium |
| `stirling_c_rec` assembly | ~50 | low |
| **Total** | **~420 LOC** | |

This is bigger than the original `cycles.v` (260 LOC).

## 8. Risks

- **Orbit count under modification (the new H2 analogue).**  The
  cycle through j0 in s gets extended by inserting ord_max as a new
  "vertex".  Show: `porbit (insert_after j0 s) ord_max = [set ord_max]
  ∪ (lift ord_max @: porbit s j0)` and then the porbits decomposition
  follows.  Same structural proof shape as H1 in `cycles_rec.v`, but
  with a non-trivial orbit instead of a singleton.
- **`s^-1 j0` everywhere is awkward.**  Consider working with the
  alternative formulation that uses `s j0` instead (option B in the
  drafting): `insert_after_fun = ... | Some k => if k == j0 then
  ord_max else lift ord_max (s k); | None => lift ord_max (s j0)`.
  Same combinatorics, no `s^-1`.  Mathematically equivalent; the
  bijection extraction is `j0 = unlift ord_max (σ^-1 ord_max)` instead
  of `unlift ord_max (σ ord_max)`.  Pick whichever is cleaner.
- **`vm_compute` sanity** of `stirling_c 3 _` etc.  Check early.

## 9. Recommended execution

1. Define `insert_after` (option A or B) and prove the three
   pointwise lemmas.
2. **Sanity-check** `cycle_count (insert_after ord0 1) = 2` for n=2
   via `vm_compute` *before* attempting the orbit decomposition.
   If this is wrong, the construction is wrong.
3. Prove `cycle_count_insert_after` via the porbits decomposition,
   reusing the `lift_perm_id_iter_lift` / `porbit_lift_perm_id_lift`
   structural lemmas from `cycles_rec.v` (genericize them where
   possible).
4. Define `extract_perm` and prove the cancellation lemmas.
5. Per-fiber bijections.
6. Assembly.

If step 2 fails (`vm_compute` doesn't match prediction), STOP and
fix the construction first.  This is the cheapest sanity check
available.

## 10. Once `stirling_c_rec` lands

- Add `stirling_fiber.v` (and `cycles_rec.v` along with it) to
  `_CoqProject`.
- Update the blueprint chapter `ch_inversions.tex` to remove the
  `\begin{remark}` deferral around the Stirling recurrence and
  replace with a proper `\begin{theorem} ... \rocq{...} \rocqok` block.
- Mark Phase 1 fully complete in `INVERSIONS_PLAN.md`.

The file does *not* need to address Foata or the q-factorial; those
are independent.
