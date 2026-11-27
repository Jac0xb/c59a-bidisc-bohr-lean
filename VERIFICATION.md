# Verification Summary (`C_59a`: Bidisc Bohr Radius $K_2$)

## 1. Public Clean-Room Linux CI & Local Clean Rebuilds

- **GitHub Actions (`ubuntu-latest`, `x86_64`):** Run [`45910806091`](https://github.com/Jac0xb/c59a-bidisc-bohr-lean/actions/runs/45910806091) passed all verification steps in **1m 57s** (`SHA256SUMS`, `lake exe cache get`, `lake build` on Lean `v4.33.1` / Mathlib `v4.33.1`, forbidden-token audit, `#print axioms` + kernel inspection, and `certify_c59a_world_record.py`).
- **Local clean rebuild (`Darwin arm64`, Lean `v4.33.1`, Mathlib `v4.33.1` rev `0df444a360eaa60ab8c11dca51a86af692955474`):** From-scratch `lake build` after removing all `C59a*` build artifacts completed with exit code `0`, 0 errors, 0 warnings.

## 2. Lean 4 Kernel, Axiom & Definition-Fidelity Audit

- **Hard-fail axiom gate (`lake env lean ProofAudit.lean`):** Verifies that both headline theorems in `Optim.BohrRadius` exist as theorems (`ConstantInfo.thmInfo`), have `hasSorry = false` in their kernel proof terms, and depend strictly on `[propext, Classical.choice, Quot.sound]` (zero `native_decide`, zero `Lean.ofReduceBool`, zero `Lean.trustCompiler`):
  - `Optim.BohrRadius.bohrRadius_lt_3028252794909876_div_10pow16`
  - `Optim.BohrRadius.bohrRadius_lt_302825279490987594822_div_10pow21`
- **Core definition safety & verbatim `[P2026]` match:** All 6 definitions (`unitBidisc`, `IsSchur`, `HasBidiscCoefficients`, `finiteMajorant`, `IsBohrAdmissible`, `bohrRadius`) pass `DefinitionSafety.safe` and match `[P2026]` (`Shivamshaiv/bidisc-bohr-certificate/certificate/EndToEnd.lean`, commit `27464dce`) character-for-character (`diff -u` = 0 bytes).
- **Closed-vs-open Schur equivalence:** Separate Lean 4 checks (using only `[propext, Classical.choice, Quot.sound]`) confirmed `IsOpen unitBidisc`, `AnalyticOn ℂ f unitBidisc ↔ AnalyticOnNhd ℂ f unitBidisc`, `strictBohrRadius = bohrRadius` (resolving closed `‖f p‖ ≤ 1` vs open `‖f p‖ < 1`), and strict `‖fSchur L T S p‖ < 1` on `unitBidisc`.
- **Forbidden-token scan & `maxRecDepth` note:** Comment-stripped audit of `C59a.lean` confirms **0** outside-comment occurrences of `sorry`, `admit`, `axiom`, `native_decide`, `ofReduceBool`, `trustCompiler`, `implemented_by`, `@[extern`, `unsafe`, `partial`, `csimp`, `opaque`, `local instance`, `macro`, or `notation`. Lines `1846` and `1851` use narrowly scoped `set_option maxRecDepth 100000 in` solely to raise the kernel recursion depth budget for `decide` on `checkCert_44` and `checkCert_56`; this introduces no axioms and does not affect soundness.

## 3. Exact Proof Paths Verified

- **Lean 4 (`C59a.lean`):** Certifies the Herglotz ($t = 1/S \to 0^+$) total-degree antidiagonal sum $\sum_{1 \le j+k \le N} |h_{j,k}| r^{j+k} > 1$ inside Lean's kernel (`N = 56`, `scale = 10^26` and compact `N = 44`, `scale = 10^21`), then applies continuity at $t = 0$ (`bohrRadius_lt_of_uC_diag_sum_gt_one`) to exhibit $S > 0$ whose Schur function `fSchur L T S` has `finiteMajorant > 1`.
- **Independent stdlib Python verifier (`certify_c59a_world_record.py`, ~1 s, zero floats):** Verifies the symbolic positivity identity in $\mathbb{Z}[x_1, y_1, x_2, y_2, L, T]$, full-degree integer recurrence residuals, independent `fractions.Fraction` 2D power-series division cross-checks, and exact `math.isqrt` integer lower bounds strictly exceeding $1$ for **both** the Herglotz reduction and explicit finite Schur witnesses $f_S = (SQ - P)/(SQ + P)$ at $S = 10^{25}$ ($N = 56$) and $S = 10^{20}$ ($N = 44$), plus byte-for-byte agreement with `c59a_world_record_cert.json`.

## 4. Scope and Trusted Computing Base

- Proof soundness relies on the Lean `v4.33.1` kernel and Mathlib `v4.33.1`; no external kernel export checker (`lean4checker`, `nanoda`) has been run yet.
- Palomar registration requires Lean `≥ v4.35.0`, whereas this repository pins Lean `v4.33.1`.
