# Certified Upper Bound for the Bidisc Bohr Radius ($C_{59} = K_2$) in Lean 4

Standalone Lean 4 (`v4.33.1` + Mathlib) formalization and exact integer certificate verifier establishing a new upper bound on Terence Tao's optimization constant [`C_59`](https://teorth.github.io/optimizationproblems/constants/59a.html) (the Bohr radius $K_2$ of the unit bidisc $\mathbb{D}^2$):

$$
K_2 < \frac{302825279490987594822}{10^{21}} = 0.302825279490987594822.
$$

This strictly improves both the prior Lean-certified bound `[P2026]` ($0.302825279492$, by $1.012405178 \times 10^{-12}$) and the prior unformalized leaderboard record `[T2026]` ($0.302825279490988$, by $4.05178 \times 10^{-16}$), while:
1. matching `[P2026]`'s `Optim.BohrRadius` definitions **character-for-character verbatim**, and
2. eliminating all `native_decide` / `Lean.ofReduceBool` dependencies so both headline theorems depend strictly on **`[propext, Classical.choice, Quot.sound]`**.

---

## 1. Problem & Leaderboard Comparison

For analytic functions $f(z, w) = \sum_{j,k \ge 0} c_{j,k} z^j w^k$ mapping the open unit bidisc $\mathbb{D}^2 = \{(z, w) \in \mathbb{C}^2 : |z| < 1,\, |w| < 1\}$ into the unit disc, the bidisc Bohr radius $K_2$ is the supremum of $r > 0$ such that $\sum_{j,k \ge 0} |c_{j,k}| r^{j+k} \le 1$ for every such Schur function $f$.

| Reference | Certified Upper Bound | Improvement vs `[T2026]` | Certificate & Trust Footprint |
| --- | --- | --- | --- |
| `[BK1997]` | $1/3$ | — | Analytic ($K_d \le K_1 = 1/3$) |
| `[BPWW2026]` | $0.3177$ | — | Explicit construction |
| `[G2026]` | $0.3174541$ | — | Degree-$(250,250)$ Fejér certificate |
| `[P2026]` | $0.302825279492$ | — | Lean 4 (`native_decide` / `Lean.ofReduceBool`), $N=28$ |
| `[T2026]` | $0.302825279490988^*$ | baseline | Unformalized $3\times 3$ colligation (149-digit denom.), $N=40$ |
| **This repo (`N = 44`)** | **$0.3028252794909876$** | **$-4.00 \times 10^{-16}$** | **Lean 4 (3 standard axioms, zero `native_decide`), 10-digit $L, T$** |
| **This repo (`N = 56`)** | **$0.302825279490987594822$** | **$-4.05178 \times 10^{-16}$** | **Lean 4 (3 standard axioms, zero `native_decide`), 13-digit $L, T$** |

---

## 2. Construction & Positivity Identity

Using the canonical bidegree $(1,1)$ rational family from `[P2026]`, set $U(z, w) = (1+z)(1-w)$, $V(z, w) = 1 + zw$, $P = LU + iTV$, $Q = LV + iTU$, and $f_S = (SQ - P)/(SQ + P)$ for integers $L, T, S > 0$. The elementary algebraic identity

$$
4 \operatorname{Re}\bigl(\overline{Q(z, w)}\, P(z, w)\bigr) = 2(L^2 + T^2)\Bigl((1 - |z|^2)|1 - w|^2 + (1 - |w|^2)|1 + z|^2\Bigr) > 0 \qquad \forall (z, w) \in \mathbb{D}^2
$$

implies $Q \ne 0$, $\operatorname{Re}(P/Q) > 0$, and $|f_S(z, w)| < 1$ strictly on all of $\mathbb{D}^2$ ($f_S$ lies in the open-disc Schur class $S_2$).

Rescaling the Taylor coefficients of $h = P/Q$ and $f_S$ by $(L + iT)^{j+k}$ and $((S+1)(L+iT))^{j+k+1}$ respectively yields exact Gaussian-integer 3-term recurrences with zero rational division:
- **Compact witness (`N = 44`):** $L = 10^9$, $T = 1226959270$ (explicit Schur $S = 10^{20}$), proving $K_2 < 3028252794909876 / 10^{16}$.
- **Sharp 21-digit witness (`N = 56`):** $L = 10^{12}$, $T = 1226959270039$ (explicit Schur $S = 10^{25}$), proving $K_2 < 302825279490987594822 / 10^{21}$.
- The exact limiting radius of the bidegree-$(1,1)$ Herglotz family is $r^* \approx 0.3028252794909875948218341940639\ldots$ at $\alpha^* = T/L \approx 1.2269592700391990135\ldots$.

---

## 3. Lean 4 & Exact Integer Verification Evidence

### A. Lean 4 + Mathlib Formalization (`C59a.lean`)

Pinned to `leanprover/lean4:v4.33.1` and Mathlib `v4.33.1` (`0df444a360eaa60ab8c11dca51a86af692955474`), `C59a.lean` (1886 lines) proves:
- `Optim.BohrRadius.bohrRadius_lt_3028252794909876_div_10pow16 : bohrRadius < (3028252794909876 : ℝ) / 10 ^ 16`
- `Optim.BohrRadius.bohrRadius_lt_302825279490987594822_div_10pow21 : bohrRadius < (302825279490987594822 : ℝ) / 10 ^ 21`

Independent verification results (full raw logs in [`NOTES/verify_c59a.md`](NOTES/verify_c59a.md) and [`NOTES/adversary_records_report.md`](NOTES/adversary_records_report.md)):
- **Verbatim `[P2026]` compatibility:** All six definitions (`unitBidisc`, `IsSchur`, `HasBidiscCoefficients`, `finiteMajorant`, `IsBohrAdmissible`, `bohrRadius`) match `[P2026]` (`EndToEnd.lean`, commit `27464dce`) character-for-character (`diff -u` = 0 bytes).
- **Closed-vs-open Schur equivalence:** The adversary audit independently proved in Lean 4 (3 standard axioms) both `strictBohrRadius = bohrRadius` and strict `‖fSchur L T S p‖ < 1` on `unitBidisc`, plus `AnalyticOn ℂ f unitBidisc ↔ AnalyticOnNhd ℂ f unitBidisc`.
- **Clean from-scratch `lake build`:** exit code `0`, 0 errors, 0 warnings.
- **Axiom footprint:** BOTH headline theorems depend strictly on `[propext, Classical.choice, Quot.sound]` (`value.hasSorry = false`, zero `native_decide`, zero `Lean.ofReduceBool`, all 6 core definitions `DefinitionSafety.safe`).

### B. Independent Exact Integer Python Verifier (`certify_c59a_world_record.py`)

Zero-dependency standard-library Python verifier (no floating-point arithmetic in any check) verifying:
1. Symbolic polynomial identity $4\operatorname{Re}(\overline{Q}P) = 2(L^2+T^2)((1-|z|^2)|1-w|^2 + (1-|w|^2)|1+z|^2)$ in $\mathbb{Z}[x_1, y_1, x_2, y_2, L, T]$.
2. Exact full-degree residuals and independent `fractions.Fraction` 2D power-series division cross-checks.
3. Exact `math.isqrt` integer lower bounds strictly exceeding $1$ for both the Herglotz and explicit finite-Schur ($S = 10^{20}, 10^{25}$) paths, and byte-for-byte agreement with `c59a_world_record_cert.json`.

---

## 4. Assumed / Unverified

As documented in [`NOTES/verify_c59a.md`](NOTES/verify_c59a.md) and [`NOTES/adversary_records_report.md`](NOTES/adversary_records_report.md) (`AR-05`):
1. **Scoped `maxRecDepth`:** `C59a.lean` lines 1846 and 1851 use `set_option maxRecDepth 100000 in` scoped strictly to the two kernel `decide` certificates (`checkCert_44`, `checkCert_56`). This increases only kernel recursion depth and introduces zero axioms or soundness assumptions, though a strict literal `set_option` token ban flags these two lines (transparently logged in `NOTES/verify_c59a.md`).
2. **Trusted Computing Base (TCB):** Formal soundness relies on the Lean `v4.33.1` kernel and Mathlib `v4.33.1`; no external independent kernel export checker (`lean4checker`, `nanoda`, `con-ron`) has been run yet.
3. **Linux CI:** Local verification ran on macOS ARM64 (`Darwin 27.2.0 arm64`); GitHub Actions Linux `x86_64` verification (`.github/workflows/verify.yml`) executes once pushed.
4. **Palomar registry version:** This repo pins Lean `v4.33.1`, whereas Palomar registration requires Lean `≥ v4.35.0`; accordingly, the draft `teorth/optimizationproblems` patch (`teorth-59a-pr.patch`) conservatively retains `*` pending community replay or a future Palomar upgrade.

---

## 5. Reproduction

```bash
# 1. Verify file integrity
shasum -a 256 -c SHA256SUMS   # or: sha256sum -c SHA256SUMS

# 2. Build Lean 4 proof and check axioms
lake exe cache get
lake build
lake env lean --stdin <<'EOF'
import C59a
#print axioms Optim.BohrRadius.bohrRadius_lt_3028252794909876_div_10pow16
#print axioms Optim.BohrRadius.bohrRadius_lt_302825279490987594822_div_10pow21
EOF

# 3. Run independent exact integer Python verifier
python3 certify_c59a_world_record.py
```

---

## 6. AI Assistance Disclosure

The witness optimization, exact integer verifier, Lean 4 formalization, and verification scripts in this repository were developed with AI assistance and audited by independent clean-build verification and statement-fidelity checks (`NOTES/verify_c59a.md`, `NOTES/adversary_records_report.md`), with human review before submission. Every mathematical claim is mechanically checked by Lean 4's kernel (standard axioms only) and corroborated by the independent zero-float Python checker.
