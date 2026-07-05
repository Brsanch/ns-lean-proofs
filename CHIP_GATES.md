# Chip gates — ns-lean-proofs (load before ANY new Lean work in this repo)

Ported 2026-06-12 from `jacobian-lean-challenge/tools/chip-prompt-preamble.md`
(the 7 anti-paraphrase gates, added there 2026-05-23 after that repo ballooned
~130k → 183k+ LOC via paraphrase chips), adapted to this repo. The sibling
failure modes both ran through Lean repos in this program: jacobian grew via
paraphrase/parallel-route chips; sqg-lean-proofs hid a circular regularity
chain behind "zero sorry, zero axioms" (vacuous `True`-equivalent hypothesis
structures, `True`-valued core fields — found only by manual audit
2026-05-29). The analysis-side caution for THIS repo: the NS Seregin-closure
circularity (every σ/M route funnels through Lemma 2.2 → Seregin → C6 ≡
regularity; `docs/findings/ns_seregin_closure_circularity_2026_05_29.md` in
the NoetherSolve repo). Lean chips here must not re-encode that circle.

Before writing ANY new code, the chip must pass ALL gates below. If it fails
any, REJECT and report `✗ REJECTED` with the failing gate.

## Gate V — vacuity lint (mechanical)

Run, from the NoetherSolve repo:

```
python3 "/Volumes/4TB SD/ClaudeCode/noethersolve/scripts/lean_vacuity_lint.py" \
  "/Volumes/4TB SD/ClaudeCode/ns-lean-proofs" --no-color --max-findings 5
```

Rules: `True`-typed fields/binders; `Prop := True` defs; `True.intro` proof
terms; structures that cannot constrain their subject; structures none of
whose fields mention their parameters; theorems with underscore-unused named
hypotheses.

**Baseline = 5 findings (audited 2026-06-12 at 7; lowered 7 → 5 on
2026-07-04 by discharging the `EpsteinZeta` `True` placeholders).**
They are documented (the docstrings disclose each placeholder) but they mark
exactly where stated obligations are not yet obligations:

- ~~`Torus/EpsteinZeta.lean:102,117`~~ — **DISCHARGED 2026-07-04.**
  `LatticeSumBounded` is now the real per-finset inequality
  `∀ finite A ⊆ ℤ³\{0}, ∑ ‖a‖^{-s} ≤ C`, proved unconditionally (zero axioms)
  for every `s > 3` in `Torus/EpsteinZetaZ3.lean`
  (`latticeSum_le_latticeZetaConstZ3`, the ℤ³ mirror of the SQG project's
  §11.26.A–H); the `s = 4` witness is wired into `exampleBundleAt4`.
- `BLW/FromNSEvolution.lean:125,137` — `NSArgmaxInputs` cannot constrain
  `_xStar`, and its `ν_eq : True` "consistency" field asserts nothing.
- `BLW/ArgmaxIdentities.lean:87` — step (i) is a `True` placeholder, consumed
  only via step (ii).
- `BLW/EnvelopeFormFromNSEvolution.lean:49` (`_ax`) and
  `Setup/LipschitzToAE.lean:36` (`_`) — unused-hypothesis, unreviewed.

**Resolved 2026-06-12 (the 10 → 7 reduction):** the original baseline's two
flagged-for-review findings traced decoy: `blowup_rate_alpha`,
`blowup_rate_alpha_beta_two`, and `blowup_rate_alpha_full` took the ESS
Type-I hypothesis `_hNoType1` (and `_hα_pos`) without using them, and their
conclusions contained no Type-I content — "full Theorem 1" was the algebraic
bound with a narrower `α`-range and an inert hypothesis. All three wrappers
were removed; the honest theorems are `blowup_rate_alpha_of_bundle` /
`blowup_rate_alpha_of_leray` (algebraic, `α ≤ β`), and `NoTypeIBlowup` is
now explicitly a citation-carrier consumed by nothing (see the §"Type-I
exclusion" banner in `Unconditional/Theorem1.lean`).

**The count must never increase.** New code adds zero findings; deliberate
exceptions get an inline `-- vacuity-ok: <reason>` waiver named in the chip
report. Refining a `True` placeholder into the real statement is real work —
lower `--max-findings` here in the same commit.

What the linter CANNOT catch: circularity (hypothesis ≈ conclusion),
misformalization, encoding mismatches. "Lint-clean" ≠ "content is real".

## Gates 1–7 (anti-paraphrase, adapted)

1. **Paraphrase gate.** Shipping `T_new (h₁ ... hₖ)` from `T_old (h₁ ... hₙ)`,
   `k < n`, by naming the dropped hypotheses into a NEW structure/class/Prop
   is a paraphrase — each name is a deferred sorry with a different docstring.
   REJECT unless the chip also discharges a named hypothesis by classical
   proof on arbitrary data.

2. **Parallel-route gate.** A second route to an already-reachable conclusion
   is net negative. REJECT unless it closes something the existing route does
   not, documented precisely.

3. **Named-hypothesis gate.** A new `class`/`structure`/`def Prop` whose
   discharge is "left as future work" is a renamed sorry. REJECT unless the
   same session discharges it on arbitrary data. This repo's three classical
   axioms (`biot_savart_self_strain_bound`, `seregin_type_one_exclusion`,
   `NS_time_analyticity`) are the *named, load-bearing, cited* exceptions —
   do not add a fourth without the same standard of citation, and never
   silently.

4. **Per-instance gate.** Concrete scalar-bundle witnesses are smoke tests.
   At most ONE per session, only if a same-session theorem consumes it.

5. **Minimum substantive content.** The chip report's `proven:` field must be
   a substantive classical statement in plain math — NOT "wires hypothesis A
   into structure B" or "reduces N inputs to N−1". REJECT the latter.

6. **mathlib-first gate.** Grep `.lake/packages/mathlib/` before writing
   infrastructure; if a lemma is within ~50 LOC of glue, use it.

7. **Frontier gate (repo-specific).** A chip on the BLW chain must either
   (a) refine one of the baseline `True` placeholders into its real statement
   and discharge it, (b) discharge a named capstone-adjacent hypothesis on
   arbitrary data, or (c) prove a substantive classical lemma the chain
   actually consumes. Re-packagings of the gradient bound, and any chip whose
   conclusion needs C6-equivalent control (uniform enstrophy near `T*`) as an
   input, are REJECT — that is the documented Seregin circle, not closure.

## Discipline rules (panic-safe build; non-negotiable)

- Per-file iteration: `LEAN_NUM_THREADS=1 lake env lean NSBlwChain/.../FILE.lean`.
- Merge gate for any new top-level declaration: full
  `taskpolicy -b nice -n 19 env LEAN_NUM_THREADS=1 lake build`
  (single-file checks miss cross-file duplicate names).
- NEVER: unthrottled `lake build`, `lake exe cache get`, `du`/`find` on
  `.lake`.
- No `sorry`, no new `axiom` (see Gate 3 for the three existing ones), no `ω`
  as a binder name.
- "Zero sorry" is NOT the bar (sqg-lean-proofs had it while circular). The
  bar is Gate V + Gates 1–7 + OPEN.md staying truthful.
