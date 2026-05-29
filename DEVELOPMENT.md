# Development guide

Instructions and lessons learned from the sister project `sqg-lean-proofs`.
This file is the **primary reference** for anyone contributing Lean code
to this repo on a local workstation.

---

## ⚠️ CRITICAL — READ FIRST — Prevents kernel panic on Apple Silicon ⚠️

This project is developed primarily on an M2 Ultra Mac, which has a
known **SoC watchdog kernel-panic mode** when the APFS daemon (`apfsd`)
saturates. Every panic forces a full system restart and loses unsaved
work. The triggers are predictable and avoidable.

### NEVER run these locally

- ❌ `du -sh` / `du -h` on `.lake/`, `.lake/packages/mathlib/`, or any
  directory with tens of thousands of `.olean` files → **instant panic**.
- ❌ `find` with heavy predicates or `-exec` on big trees (`~`, `/Volumes/`).
- ❌ *Unthrottled* `lake build` — the **finalization phase** (flushing `.olean`,
  `.ilean`, `.c`, trace files across the dep graph) is many small writes in a
  narrow window and saturates apfsd. Confirmed crashes with an unthrottled
  `LEAN_NUM_THREADS=1 lake build` on a 3-file project. **The *throttled* form
  `taskpolicy -b nice -n 19 ... lake build` IS safe — see Always, below.**
- ❌ `lake exe cache get` — leantar decompresses ~8,000 small files in a
  burst. Every time.
- ❌ Multi-threaded `lake env lean FILE.lean` — parallel `.olean` writes
  same pattern as `lake build`.
- ❌ `sed -i` on multi-thousand-line files (use the Edit tool instead).
- ❌ `cp -r` or `mv` of large trees (`.lake` is ~7 GB).
- ❌ Back-to-back heavy file operations without pause.

### Always do these

- ✅ For single-file verification:
  `LEAN_NUM_THREADS=1 lake env lean NSBlwChain/YOUR_FILE.lean`
  (no-write elaboration; only type-checks in memory, doesn't write
  artifacts).
- ✅ For size info: `ls -ldh /path` (directory itself, no recursion)
  or `df -h /Volumes/4TB\ SD` (free space only).
- ✅ For finding files: use `Glob` / file browser, not `find`.
- ✅ **For full-graph build / CI-independent merge gate:**
  `taskpolicy -b nice -n 19 env LEAN_NUM_THREADS=1 lake build`. The
  `taskpolicy -b nice -n 19` throttle holds apfsd under the saturation
  threshold during the `.olean` finalization burst, so the full build is
  panic-safe. It elaborates every file fresh → catches the cross-file
  duplicate-`namespace.declName` conflicts that single-file `lake env lean`
  CANNOT (it reads pre-built `.olean`s). **This removes the need to depend on
  CI** — run it green before merge. (Pushing to CI to build the cache remotely
  still works, but is no longer required.)
- ✅ For big copies: `rsync --bwlimit=30M`.

### If you forget and the machine panics

Symptom in `/Library/Logs/DiagnosticReports/`:
- `panic-base-*.panic`: `"Unexpected SoC (system) watchdog reset occurred"`
- `apfsd_*.cpu_resource.diag`: `apfsd` at ~70-80% CPU for 100+ seconds

Restart the machine. Any unsaved Lean work is gone.

---

## Local-verify-primary workflow

**Policy (updated 2026-05-29, synced from `jacobian-lean-challenge`):** local
verification is primary; CI is an **optional** final-confidence check, **not**
the merge gate. The earlier "CI is the authoritative build" policy was set when
`lake build` was believed to always panic — only the *unthrottled* form does;
the throttled `taskpolicy -b nice -n 19 ... lake build` is panic-safe.

### The two local checks

1. **Per-file iteration (primary loop):**
   `LEAN_NUM_THREADS=1 lake env lean NSBlwChain/YOUR_FILE.lean` — no-write,
   type-checks against the existing `.olean` cache, ~3-30s warm. Read the inline
   error at the bottom of stdout, fix, repeat. Iterate as much as you want.
2. **Merge gate (full graph):**
   `taskpolicy -b nice -n 19 env LEAN_NUM_THREADS=1 lake build` — throttled,
   panic-safe (see CRITICAL section). This is the **only** local check that
   surfaces cross-file duplicate-`namespace.declName` conflicts (single-file
   `lake env lean` reads pre-built `.olean`s and cannot). Run it green before
   merging any chip that adds a new top-level `def`/`lemma`/`theorem`/
   `instance`. Skip it only for pure proof-body iteration on names already in
   `main`.

### The typical loop

1. Write code in modular blocks, **≤ 150 lines per commit** ideally.
2. After each change:
   `LEAN_NUM_THREADS=1 lake env lean NSBlwChain/YOUR_FILE.lean`. Fix inline
   errors; re-run.
3. Once the new file is green, single-file-check the manifest entry too.
4. Before merge (new top-level declaration): run the throttled full build
   (gate #2 above) and confirm "Build completed successfully".
5. Commit (no AI-attribution trailer) and merge. **CI is optional** — push and
   watch it only for a final external confirmation, after a mathlib-pin change,
   or when you touched a cross-cutting import.

### Optional: CI as final confirmation

If you do want a CI run, push the branch and poll:
```
gh run list --repo Brsanch/ns-lean-proofs --limit 3 \
  --json status,conclusion,headSha,workflowName
gh run view --job=<JOB_ID> --repo Brsanch/ns-lean-proofs   # leanprover/lean-action@v1 is the gating step
gh run view <RUN_ID> --repo Brsanch/ns-lean-proofs --log-failed   # on failure
```
The `leanprover/lean-action@v1` step is what determines build success;
`docgen` / `dedupe-caches` jobs are allowed to fail and do not gate correctness.

### Cache hygiene

The workflow includes a `dedupe-caches` job after build that keeps only
the newest cache per key. This prevents the 10 GB per-repo Actions
cache quota from filling up from duplicate `lean-action` cache saves.
No manual action needed.

### Expected cold-build time

First CI run on a new mathlib rev fetches ~8,000 files and decompresses
them — takes ~2-3 min for cache fetch alone, plus 1-2 min actual build.
Subsequent runs against the same mathlib rev hit the cache and complete
in ~2 min.

### Known benign failures

- **`Create Release` workflow fails on the very first push of a branch.**
  The action's `create-tags.sh` tries to diff between `0000...0000` (no
  parent) and the first commit, which is not a valid git range on an
  orphan branch. Subsequent pushes with a real parent work fine. The
  release workflow only re-fires on `lean-toolchain` changes anyway.
- **`docgen-action` hangs or times out.** It's `continue-on-error: true`
  with a 10-minute timeout. Safe to ignore for correctness; the
  `leanprover/lean-action@v1` step status is what determines build
  success.

---

## Diagnostic workflow for Lean timeouts and loops

**When you see `(deterministic) timeout at whnf, maximum number of
heartbeats (N) has been reached`:**

**DO NOT** iteratively bump `maxHeartbeats` from 200k → 400k → 800k.
Nine times out of ten it's a reducibility loop on a definitionally-
computable term applied to symbolic arguments, not a "just slow"
budget problem. Each bump wastes ~4 minutes of CI time and teaches
you nothing.

### Step 1: Run the built-in diagnostic

Add these three `set_option` lines directly above the failing `theorem`:

```lean
set_option maxHeartbeats 400000 in
set_option diagnostics true in
set_option diagnostics.threshold 100 in
theorem your_failing_theorem ... := ...
```

Push to CI. The CI log will contain output like:

```
info: File.lean:L:0: [diag] Diagnostics
  [reduction] unfolded declarations (max: N, num: K):
    [reduction] Int.rec ↦ 3573405
    [reduction] Multiset.ofList ↦ 80553
    [reduction] Add.add ↦ 1949293
    ...
```

**Read it literally.** Declarations unfolded 100k+ times ARE the loop.
Don't architect-guess; patch the specific declarations named.

### Step 2: Common root causes + fixes

| Pattern in diagnostic | Root cause | Fix |
|---|---|---|
| `Int.rec`, `Nat.rec`, `List.range` in millions | Finset/Multiset-valued definition with symbolic index | `attribute [local irreducible] yourDef` scoped to the slow section |
| `HAdd.hAdd`, `Add.add`, `NatCast.natCast` in millions | Arithmetic inside symbolic index computation | Same — find the def being unfolded |
| `Quot.lift`, `Multiset.ofList`, `Multiset.map` | Finset/Multiset normalization | Same |
| `dite`, `decidable_of_iff`, `Int.decEq`, `Multiset.decidableForallMultiset` | DecidableEq instance-synthesis loop | **See Step 3 below** |
| One specific instance showing 50k+ uses | Instance-search loop | Mark the class/def irreducible, or provide the instance explicitly |

### Step 3: `DecidableEq` instance-mismatch (structure-field gotcha)

**Telltale signature:**

```
h_bound has type   ... @trigPolyProduct inst✝ A B cf cg ...
but is expected to have type   ... @trigPolyProduct
  (fun a b ↦ Fintype.decidablePiFintype a b) A B cf cg ...
```

**Root cause.** The structure's field was elaborated at
structure-declaration time with the *default* `DecidableEq` instance
auto-synthesized by mathlib. But the consuming theorem has
`[DecidableEq ...]` as an *explicit class parameter*, which introduces
a fresh `inst✝`. The two instances are propositionally equal (it's a
Prop) but not definitionally equal, and structure-field unification
hits `isDefEq`.

**Fix (apply by default):**

1. **Remove `[DecidableEq ...]` from the theorem's signature.**
2. Add `classical` in the body if the proof genuinely needs it
   (e.g., calling a helper that takes `[DecidableEq]`).
3. Lean's default instance synthesis then picks the same instance at
   every use site, and field assignment matches.

**Pre-push checklist:**

1. Does this theorem call `.bound` or `.something` on a structure whose
   field type involves `DecidableEq`-parametrised terms?
2. If yes, is `[DecidableEq ...]` in MY signature?
3. If yes to both → remove it, use `classical` in the body.

### Step 4: `convert` instead of `exact` for instance mismatches

If a helper auto-synthesizes e.g. `Fintype.decidablePiFintype` but the
theorem's `[DecidableEq]` parameter is `inst✝`, they are subsingleton-
equal but not definitionally equal under irreducibility.

**Bridge with `convert`**, not `exact`:

```lean
-- failed: exact myHelper (params...)
convert myHelper (params...)
```

`convert` falls back to subsingleton reasoning for instance arguments
where `exact` requires strict definitional equality. Use `convert`
only at leaf instance-mismatch spots — never at an Lp-valued top-level
goal, which triggers `.default` transparency.

### Step 5: What NOT to do

- **Don't** iterate heartbeat bumps. Wastes CI time, diagnoses nothing.
- **Don't** restructure the proof ("split into smaller theorems",
  "unbundle structure projections") without diagnostic data. You're
  guessing. One v0.4.38-era session hit 10+ CI failures trying
  architectural fixes before the 1-minute diagnostic run pinpointed
  the actual loop. Cost comparison:

  | Approach | Cycles | Wall time |
  |---|---|---|
  | Architectural guesses without diagnostics | 9 | ~40 min |
  | Run `set_option diagnostics true` once | 1 | ~4 min |
  | Apply fix from diagnostic output | 1 | ~4 min |

  **Lesson: diagnostic first, architectural guesses never.**

---

## Lean 4 / mathlib gotchas (reference)

Collected from sister-project experience. Not exhaustive; add new ones
here as they come up.

### Imports must precede all other content

```lean
-- copyright comment (plain -- lines, OK above imports)
import Mathlib

/-!
# Module doc-comment goes HERE, after imports.
-/

namespace ...
```

Putting a `/-! ... -/` module doc-comment before `import Mathlib` gives
`invalid 'import' command, it must be used at the beginning of the file`.
**Common first-time mistake.** Always: copyright `--` comment, then
imports, then `/-! ... -/` doc, then `namespace`.

### `memℓp_gen_iff` (not the "obvious" name)

The correct mathlib4 name for `Memℓp f p ↔ Summable (fun i => ‖f i‖ ^ p.toReal)`
(for `0 < p.toReal`) is `memℓp_gen_iff`, not `memℓp_two_iff_summable_sq_norm`
or any other plausible-sounding alternative. It's an `Iff`, so use
`.mpr`, not `rw`. Using `rw [memℓp_gen_iff hp]` fails with "did not
find an occurrence of the pattern".

### `ENNReal` over `ℝ≥0∞`

Prefer the ASCII form `ENNReal` in type annotations. The Unicode
`ℝ≥0∞` has caused "expected token" + instance-synthesis cascade at
tokenization time in past work.

### `Lp.coeFn_sub f g`

Gives `(f - g) x = f x - g x` *almost everywhere*, not pointwise. Use
`filter_upwards` + `integral_congr_ae` when moving between
Lp-subtraction and pointwise subtraction in integrals.

### `mFourierCoeffLM` vs `mFourierCoeff`

The `LinearMap` form of `mFourierCoeff` is `mFourierCoeffLM`. Use
`map_sub` on it (not on `mFourierCoeff` directly) to get
`mFourierCoeff (f - g) m = mFourierCoeff f m - mFourierCoeff g m`.

### Useful diagnostic `set_option`s

- `set_option diagnostics true` + `set_option diagnostics.threshold 100`
  — primary tool, prints unfold/use counts at declaration close.
- `#defeq_abuse in theorem Foo ...` — identifies definitional abuse
  where implicit arguments force `.default` transparency.
- `count_heartbeats in <decl>` (from `Mathlib.Util.CountHeartbeats`) —
  auto-suggests a heartbeat budget or reveals loops.
- `set_option trace.Meta.isDefEq true` — verbose defeq trace, use on
  a minimal reproducer only (CI logs truncate).
- `set_option trace.Meta.synthInstance true` — trace instance
  resolution specifically.
- `set_option backward.isDefEq.respectTransparency false` — restore
  pre-4.29 transparency behavior if needed.

---

## Pre-commit checklist

Before every `git push`:

1. **Imports at top?** All `.lean` files must have `import` statements
   at the very top (above any `/-! ... -/` doc-comment).
2. **Tiny commit?** Ideally ≤ 150 lines changed per commit. Large
   commits amplify CI retry cost if something fails.
3. **Merge gate run?** For a chip adding a new top-level
   `def`/`lemma`/`theorem`/`instance`, ran
   `taskpolicy -b nice -n 19 env LEAN_NUM_THREADS=1 lake build` to "Build
   completed successfully" (the only local check that catches cross-file
   duplicate-name conflicts). Never run an *unthrottled* `lake build` or
   `lake exe cache get`.
4. **If consuming a structure field**: check for the `DecidableEq`
   class-parameter pattern (Step 3 above). If your theorem takes
   `[DecidableEq ...]` and calls `.bound` on a structure, remove the
   parameter and use `classical`.
5. **Commit message descriptive?** Reference the lemma name or section
   number that landed. Ex.: `"Add Lemma C2.5 Danskin envelope"`.

---

## Repository structure

See [`README.md`](./README.md) and [`OPEN.md`](./OPEN.md) for the
mathematical structure and roadmap.

In brief:

```
NSBlwChain/
  Basic.lean              -- entry point + module doc
  Setup/                  -- foundations (vector fields, NS hypothesis, axioms)
  Caveats/                -- elementary caveats (C1, C2.5, C4, angular integrals)
  BLW/                    -- BLW-gradient chain core (Thm 12.2, log-absorption)
  Torus/                  -- torus Biot–Savart machinery (C3)
  Analyticity/            -- real-analyticity refinement (C2.4, C2.6)
  Unconditional/          -- Theorems 1 and 2
  Capstone.lean           -- end-to-end Proposition 4
```

Each subdirectory is created on demand as content lands. New files
must be added to the top-level `NSBlwChain.lean` import list for them
to be included in the library build.
