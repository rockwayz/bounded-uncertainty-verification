# bounded-uncertainty-verification

[![CI](https://github.com/rockwayz/bounded-uncertainty-verification/actions/workflows/ci.yml/badge.svg)](https://github.com/rockwayz/bounded-uncertainty-verification/actions/workflows/ci.yml)

Lean 4 formalization of the four-state verification-output calculus from:

> Dolera, Simon. **Bounded-Uncertainty Verification for Artificial Intelligence Systems:
> An Honest Output Classification Grounded in Formal Impossibility Results.**
> Working paper, v1, July 2026. Zenodo.
> DOI: [10.5281/zenodo.21341445](https://doi.org/10.5281/zenodo.21341445)

**Software citation** — this repository, archived on Zenodo:
code DOI [10.5281/zenodo.21368547](https://doi.org/10.5281/zenodo.21368547)
(all versions; resolves to the latest release —
this release, v1.0.1: [10.5281/zenodo.21369153](https://doi.org/10.5281/zenodo.21369153))

## What this proves

The paper argues that a binary safe/unsafe verdict on an AI system is a lie of omission —
Rice's theorem (generalized to abstract semantics by Baldan–Ranzato–Zhang) makes every
non-trivial semantic property undecidable, so honest assurance must report the epistemic
status of a verdict alongside the verdict. This repository machine-checks the calculus
that claim rests on. A single module, [`VCalc/Basic.lean`](VCalc/Basic.lean), defines the
four output states (PROVEN, APPROXIMATION, ESCALATED, TERMINATED) with non-evaluation
(SKIPPED) structurally unrepresentable as assurance, certificates carrying scope and a
per-mechanism residual-risk ledger, and a composition operation with the
Dwork–Rothblum–Vadhan advanced-composition bound evaluated as a query-time accountant
over the whole ledger — the design that preserves the bound's √k growth, which a naively
iterated binary bound destroys. Four theorems are proved with no `sorry`: composition is
associative; the four states are exhaustive and mutually exclusive; accounted risk is
monotone (a budget, once exhausted, stays exhausted); and an exhausted budget can never
issue an APPROXIMATION — issuance degrades to ESCALATED or TERMINATED, never to a diluted
risk claim. On homogeneous ledgers the accountant's value equals the paper's DRV bound
exactly, with zero unformalized assumptions; on heterogeneous ledgers it evaluates at
worst-case ε, an over-approximation whose DP-soundness is cited, not formalized — the one
assumption boundary, labeled in the source where it lives.

## Checking

Lean 4 (`v4.32.0-rc1`); mathlib is pinned by commit in `lakefile.toml` and locked in
`lake-manifest.json`. Reproducible build (what CI runs on every push):

    lake exe cache get   # fetch mathlib's prebuilt oleans (~minutes, not hours)
    lake build

Success = the module type-checks with no `sorry`. `check.sh` is a fast local loop — it
type-checks the single module directly via `LEAN_PATH` against a prebuilt mathlib
checkout. Point `MATHLIB_DIR` at your mathlib4 checkout (default: `~/mathlib4`), built
with the toolchain in `lean-toolchain`, from which the `lean` binary is derived:

    MATHLIB_DIR=/path/to/mathlib4 ./check.sh VCalc/Basic.lean
