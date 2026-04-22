# Changelog

All notable changes to this project will be documented in this file. Releases
will be archived on Zenodo once a publishable milestone is reached.

## v0.1.0 — 2026-04-22

**Initial scaffold.** Repository initialized, parallel to `sqg-lean-proofs`.

Highlights:

- Build infrastructure: `lakefile.toml`, `lean-toolchain` (`v4.29.0`),
  `.gitignore`, GitHub Actions workflows for CI (`lean_action_ci.yml`),
  dependency updates (`update.yml`), and tag releases (`create-release.yml`).
- Top-level Lean module: `NSBlwChain.lean` imports `NSBlwChain/Basic.lean`.
- `NSBlwChain/Basic.lean` — project entry point with a placeholder theorem
  to exercise the build, plus a doc-comment listing the formalization scope
  and the three named classical axioms.
- `OPEN.md` — live roadmap listing all outstanding items in order (§C1, §C2
  envelope, §C4 convex implicit bound, §D.3 angular integrals, Theorem 12.2,
  and downstream).
- `README.md` — public-facing description of the scope, axiomatic footprint,
  and build instructions.
- `CITATION.cff` — software-citation skeleton (to be populated on first release).

**Mathematical content:** none yet. Build status: expected to compile once
mathlib cache is fetched (CI will verify).
