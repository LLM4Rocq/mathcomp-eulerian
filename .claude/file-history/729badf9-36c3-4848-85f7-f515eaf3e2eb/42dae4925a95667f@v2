# M2 subtask decomposition — closing `psi_involutive`

**Current state of `psi.v` (588 LOC, compiles clean, no Admitted):**
- `mmtree_of_seq_mm`, `mmtree_of_seq_mmK` (alternating min/max tree + round-trip)
- `mm_pos`, `max_pos`, `mm_pos_lt`
- `window_size`, `window_at` (locate the right-subtree slice at position i)
- `window_size_fuel_bound`, `window_size_gt0`, `window_size_bound`, `window_size_oor`
- `window_size_fuel_monotone`, `window_size_cons`, `window_at_cons`
- `rank_shift_seq` (cyclic rank-shift on a window)
- `size_rank_shift_seq`, `rank_shift_perm_eq`, `sort_rank_shift_seq`, `uniq_rank_shift_seq`
- `rank_shift_seqE`, `nth_rank_shift_seq`, `head_rank_shift_seq`
- **`rank_shift_seq_involutive`** (double rank-shift = id, under head-is-extremum hypothesis)
- `psi`, `psi_perm_eq`, `psi_id_oor`, `psi_id_trivial`
- `Example psi_nontrivial`, `Example psi_involutive_ex`

**What is missing:** `psi_involutive : forall i w, uniq w -> psi i (psi i w) = w`.

---

## Proof strategy (from the informal note §4 and §6.6)

The argument:
1. `psi i w` replaces positions `[i, i + ws)` (where `ws = window_size i w`) with `rank_shift_seq (window_at i w)`.
2. Applying `psi i` again to `psi i w` reads the window at position `i` of the new word.
3. If the **window is stable** (same size, same slice = `rank_shift_seq` of old slice), then the second application applies `rank_shift_seq` again.
4. By `rank_shift_seq_involutive`, double rank-shift = id (needs head-is-extremum).
5. Therefore `psi i (psi i w) = w`.

The gap is steps 2–3: proving the window of `psi i w` at position `i` equals the rank-shifted window of `w`.

---

## Subtasks (ordered by dependency)

### T1. `size_psi` — size preservation (~5 LOC)

```coq
Lemma size_psi i w : size (psi i w) = size w.
```

Follows from `perm_size` + `psi_perm_eq`, or directly from `size_cat` + `size_rank_shift_seq`.

**Depends on:** nothing new. **Blocking:** T4, T5.

---

### T2. `uniq_psi` — uniqueness preservation (~3 LOC)

```coq
Lemma uniq_psi i w : uniq w -> uniq (psi i w).
```

Follows from `perm_uniq` + `psi_perm_eq`.

**Depends on:** nothing new. **Blocking:** T6.

---

### T3. `nth_psi_outside` — psi does not touch positions outside the window (~15 LOC)

```coq
Lemma nth_psi_outside i w k :
  k < i \/ i + window_size i w <= k ->
  nth 0 (psi i w) k = nth 0 w k.
```

Direct from `nth_cat` + `nth_take` + `nth_drop` on the `take i w ++ rank_shift_seq (...) ++ drop ...` definition.

**Depends on:** `size_rank_shift_seq`. **Blocking:** T5.

---

### T4. `mm_pos_stable` — mm_pos is preserved at every ancestor of position i (~40 LOC, HARD)

This is the crux. We need: at each recursive step of `mmtree_of_seq_mm` that leads to position `i`, the split point `mm_pos` of the current subarray is the same in `w` and `psi i w`.

**Strategy:** Induction on `size w`. At each level, let `j = mm_pos w`. Three cases:
- **`i < j`**: psi modifies positions `[i, i+ws)` which are all `< j`, so they lie inside `take j w`. The split point `j` depends on `min` and `max` of `w`. Since the modification is inside `take j w` (strictly before position `j`), positions `j .. size w - 1` are unchanged. Need: `mm_pos(psi i w) = j`. This requires that the min-or-max at position `j` is still the first extremum. Since the modification only permutes labels in `[i, i+ws) ⊆ [0, j)`, and the values at `j` and beyond are unchanged, we need that neither `min(w)` nor `max(w)` moved to a position `< j` under `psi`. Since `psi` is a `perm_eq`, `min(w)` and `max(w)` are still present; if they were at positions `≥ j` before, they stay there (psi only permutes within `[i, i+ws)` which is `⊆ [0, j)`... wait, we need `i + ws ≤ j`). This is guaranteed by the recursive structure: if `i < j`, the window at position `i` fits inside `take j w`.
- **`i = j`**: position `i` is the root of the current recursion level. The window is `drop j w` (everything from position `j` onward in the current subarray). psi modifies exactly this slice. Need: `mm_pos(psi i w) = j`. The value at position `j` changes (it becomes the opposite extremum of the window), but it is still an extremum of the whole array (because the window contains all positions `≥ j`, and positions `< j` have the same values). So `mm_pos` stays at `j`.
- **`i > j`**: symmetric to `i < j`, with recursion on `drop j.+1 w`.

Suggested decomposition: prove a helper
```coq
Lemma window_fits_left i w j :
  j = mm_pos w -> i < j -> i + window_size i w <= j.
```
(the window at position `i` in `take j w` does not cross boundary `j`).

Then the main lemma:
```coq
Lemma mm_pos_psi_eq i w :
  uniq w -> 1 < window_size i w -> i < size w ->
  mm_pos (psi i w) = mm_pos w.
```

**Depends on:** T1, T3. **Blocking:** T5.

---

### T5. `window_stable` — the window of `psi i w` at position i (~50 LOC, HARD)

```coq
Lemma window_size_psi i w :
  uniq w -> 1 < window_size i w -> i < size w ->
  window_size i (psi i w) = window_size i w.

Lemma window_at_psi i w :
  uniq w -> 1 < window_size i w -> i < size w ->
  window_at i (psi i w) = rank_shift_seq (window_at i w).
```

**Strategy:** Induct jointly on `size w`, using `window_size_cons` / `window_at_cons` and T4 (`mm_pos_psi_eq`) at each step. The three cases (`i < j`, `i = j`, `i > j`) parallel T4.

- **`i = j` case:** `window_at i w = drop j w` and `window_at i (psi i w) = drop j (psi i w) = rank_shift_seq (drop j w)`. This is nearly definitional from how `psi` splices.
- **`i < j` case:** recurse on `take j w` (which is unchanged by psi in positions `[j, ...)`, and psi's effect on `take j (psi i w)` is `psi i (take j w)` since the window fits inside `[0, j)` by `window_fits_left`). Then apply the IH.
- **`i > j` case:** symmetric, recurse on `drop j.+1 w`.

**Depends on:** T1, T3, T4. **Blocking:** T6.

---

### T6. `window_head_extremum` — provenance invariant (~30 LOC)

```coq
Lemma window_head_extremum w i :
  uniq w -> i < size w -> 1 < window_size i w ->
  let W := window_at i w in
  (head 0 W == nth 0 (sort leq W) 0) ||
  (head 0 W == nth 0 (sort leq W) (size W).-1).
```

The head of the window is the label at position `i`, which is the root of the subtree — by F2 it is either the min or max of that subtree's labels. The window labels are exactly the subtree labels.

**Strategy:** Induct on `size w`. Three cases via `window_at_cons`:
- `i < j`: recurse on `take j w`.
- `i = j`: `head(window) = nth 0 w j`, which is `min w` or `max w` by definition of `mm_pos`. The window = `drop j w` is a suffix of `w`, and `nth 0 w j` is also min-or-max of `drop j w` (because it is first-extremum of `w` and all earlier positions are in `take j w`, so among `drop j w` it is still extremal).
- `i > j`: recurse on `drop j.+1 w`.

**Depends on:** nothing new beyond existing infrastructure. **Blocking:** T7.

---

### T7. `psi_involutive` — assembly (~15 LOC)

```coq
Theorem psi_involutive i w : uniq w -> psi i (psi i w) = w.
```

**Proof:** Case split:
1. `size w <= i` → `psi_id_oor` twice.
2. `window_size i w <= 1` → `psi_id_trivial` twice (need `window_size i (psi i w) <= 1` too — follows from T5 or directly from `psi_id_trivial` making `psi i w = w`).
3. Otherwise (`1 < window_size i w` and `i < size w`):
   - By T5: `window_at i (psi i w) = rank_shift_seq (window_at i w)`.
   - By T5: `window_size i (psi i w) = window_size i w`.
   - Unfold `psi i (psi i w)` = `take i (psi i w) ++ rank_shift_seq (window_at i (psi i w)) ++ drop ...`.
   - By T3: `take i (psi i w) = take i w` (psi doesn't touch positions `< i`).
   - By T5: `rank_shift_seq (window_at i (psi i w)) = rank_shift_seq (rank_shift_seq (window_at i w))`.
   - By T6 + `rank_shift_seq_involutive`: this equals `window_at i w`.
   - Similarly `drop (i + ws) (psi i w) = drop (i + ws) w` by T3.
   - So the triple-cat equals `take i w ++ window_at i w ++ drop (i + ws) w = w`. QED.

**Depends on:** T2, T5, T6.

---

## Execution plan

| Phase | Subtasks | Est. LOC | Difficulty |
|-------|----------|----------|------------|
| 1 (easy) | T1, T2, T3 | ~23 | Low |
| 2 (hard) | T4 | ~40 | High — mm_pos stability is the mathematical crux |
| 3 (hard) | T5 | ~50 | High — window stability; builds on T4 |
| 4 (medium) | T6 | ~30 | Medium — head-extremum provenance |
| 5 (easy) | T7 | ~15 | Low — pure assembly |
| **Total** | | **~158** | |

Phases 1 and 4 are independent and can run in parallel. Phase 2 depends on Phase 1. Phase 3 depends on Phases 1+2. Phase 5 depends on Phases 3+4.

## Notes for the agent

- T4 is the mathematical crux. If it resists, the likely issue is the `i = j` case: showing `mm_pos` is stable when the root value changes from one extremum to the other. The key insight: `psi` replaces `drop j w` with `rank_shift_seq (drop j w)`, which is a `perm_eq`; the new value at position `j` is the opposite extremum of `drop j w`, which is also an extremum of all of `w` (because `j = mm_pos w` means the original value at `j` was one global extremum, and the other global extremum is also in `drop j w`). So the new value at `j` is still a global extremum, and since positions `< j` haven't changed, it's still the *first* global extremum.
- T5 and T4 could potentially be proved jointly by a single induction, since they share the same case structure. Consider this if separate proofs cause duplication.
- The `window_fits_left` helper for T4 is important: it says the window at position `i` in the full array, when `i < mm_pos w`, is entirely contained in `take (mm_pos w) w`. This follows from the recursive structure of `window_size`.
