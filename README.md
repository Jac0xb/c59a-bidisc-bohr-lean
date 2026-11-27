# Certified Upper Bound for the Bidisc Bohr Radius ($C_{59} = K_2$) in Lean 4

Standalone Lean 4 (`v4.33.1` + Mathlib) formalization and exact integer certificate verifier establishing an improved upper bound on Terence Tao's optimization constant [`C_59`](https://teorth.github.io/optimizationproblems/constants/59a.html) (the Bohr radius $K_2$ of the unit bidisc $\mathbb{D}^2$):

$$
K_2 < \frac{302825279490987594822}{10^{21}} = 0.302825279490987594822.
$$

This strictly improves both the prior Lean-certified bound `[P2026]` ($0.302825279492$, by $1.012405178 \times 10^{-12}$) and the prior unformalized bound `[T2026]` ($0.302825279490988$, by $4.05178 \times 10^{-16}$), while:
1. matching `[P2026]`'s `Optim.BohrRadius` definitions **character-for-character verbatim**, and
2. eliminating all `native_decide` / `Lean.ofReduceBool` dependencies so both main theorems depend strictly on **`[propext, Classical.choice, Quot.sound]`**.

---

## 1. Problem & Comparison with Prior Bounds

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

Using the bidegree $(1,1)$ rational family from `[P2026]`, set $U(z, w) = (1+z)(1-w)$, $V(z, w) = 1 + zw$, $P = LU + iTV$, $Q = LV + iTU$, and $f_S = (SQ - P)/(SQ + P)$ for integers $L, T, S > 0$. The algebraic identity

$$
4 \operatorname{Re}\bigl(\overline{Q(z, w)}\, P(z, w)\bigr) = 2(L^2 + T^2)\Bigl((1 - |z|^2)|1 - w|^2 + (1 - |w|^2)|1 + z|^2\Bigr) > 0 \qquad \forall (z, w) \in \mathbb{D}^2
$$

implies $Q \ne 0$, $\operatorname{Re}(P/Q) > 0$, and $|f_S(z, w)| < 1$ strictly on all of $\mathbb{D}^2$ ($f_S$ lies in the open-disc Schur class $S_2$).

Rescaling the Taylor coefficients of the Herglotz function $h = P/Q$ by $(L + iT)^{j+k}$ (and those of $f_S$ by $((S+1)(L+iT))^{j+k+1}$) yields exact Gaussian-integer 3-term recurrences with zero rational division:
- **Compact witness (`N = 44`):** $L = 10^9$, $T = 1226959270$ (explicit finite Schur $S = 10^{20}$ in Python checker), certifying $K_2 < 3028252794909876 / 10^{16}$.
- **Sharp 21-digit witness (`N = 56`):** $L = 10^{12}$, $T = 1226959270039$ (explicit finite Schur $S = 10^{25}$ in Python checker), certifying $K_2 < 302825279490987594822 / 10^{21}$.
- The limiting radius of this bidegree-$(1,1)$ Herglotz family is $r^* \approx 0.3028252794909875948218341940639\ldots$ at $\alpha^* = T/L \approx 1.2269592700391990135\ldots$ (equivalently $\theta^* = \arctan(L/T) \approx 0.683834403631$).

---

## 3. Lean 4 & Exact Integer Verification Evidence

Full verification details and CI links are documented in [`VERIFICATION.md`](VERIFICATION.md).

### A. Lean 4 + Mathlib Formalization (`C59a.lean`, `ProofAudit.lean`)

Pinned to `leanprover/lean4:v4.33.1` and Mathlib `v4.33.1` (`0df444a360eaa60ab8c11dca51a86af692955474`), `C59a.lean` (1886 lines) proves:
- `Optim.BohrRadius.bohrRadius_lt_3028252794909876_div_10pow16 : bohrRadius < (3028252794909876 : ℝ) / 10 ^ 16`
- `Optim.BohrRadius.bohrRadius_lt_302825279490987594822_div_10pow21 : bohrRadius < (302825279490987594822 : ℝ) / 10 ^ 21`

**Proof path in `C59a.lean`:** Lean's kernel certifies the Herglotz ($t = 1/S \to 0^+$) total-degree antidiagonal sum $\sum_{1 \le j+k \le N} |h_{j,k}| r^{j+k} > 1$ using exact integer witnesses (`N = 56`, `scale = 10^26` and `N = 44`, `scale = 10^21`), then uses continuity at $t = 0$ (`bohrRadius_lt_of_uC_diag_sum_gt_one`) to show $\exists S > 0$ such that `fSchur L T S` satisfies `finiteMajorant > 1`.

Verification status:
- **Public Linux CI (`ubuntu-latest`):** GitHub Actions run [`45910806091`](https://github.com/Jac0xb/c59a-bidisc-bohr-lean/actions/runs/45910806091) passed all checks in **1m 57s**.
- **Verbatim `[P2026]` compatibility:** All six definitions (`unitBidisc`, `IsSchur`, `HasBidiscCoefficients`, `finiteMajorant`, `IsBohrAdmissible`, `bohrRadius`) match `[P2026]` (`EndToEnd.lean`, commit `27464dce`) character-for-character (`diff -u` = 0 bytes).
- **Hard-fail axiom gate (`lake env lean ProofAudit.lean`):** Both theorems depend strictly on `[propext, Classical.choice, Quot.sound]` (`hasSorry = false`, zero `native_decide`, zero `Lean.ofReduceBool`), and all 6 core definitions pass `DefinitionSafety.safe`.

### B. Independent Exact Integer Python Verifier (`certify_c59a_world_record.py`)

Zero-dependency standard-library Python verifier (no floating-point arithmetic in any check) verifying:
1. Symbolic polynomial identity $4\operatorname{Re}(\overline{Q}P) = 2(L^2+T^2)((1-|z|^2)|1-w|^2 + (1-|w|^2)|1+z|^2)$ in $\mathbb{Z}[x_1, y_1, x_2, y_2, L, T]$.
2. Exact full-degree recurrence residuals and independent `fractions.Fraction` 2D power-series division cross-checks.
3. Exact `math.isqrt` integer lower bounds strictly exceeding $1$ for **both** the Herglotz reduction ($1 \le j+k \le N$) and explicit finite Schur witnesses $f_S = (SQ - P)/(SQ + P)$ at $S = 10^{20}$ ($N = 44$) and $S = 10^{25}$ ($N = 56$), plus byte-for-byte agreement with `c59a_world_record_cert.json`.

---

## 4. Assumed / Unverified

1. **Scoped `maxRecDepth`:** `C59a.lean` lines `1846` and `1851` use `set_option maxRecDepth 100000 in` scoped strictly to the two kernel `decide` proofs (`checkCert_44`, `checkCert_56`). This increases only kernel recursion depth and introduces zero axioms or soundness assumptions.
2. **Trusted Computing Base (TCB):** Formal soundness relies on the Lean `v4.33.1` kernel and Mathlib `v4.33.1`; no external independent kernel export checker (`lean4checker`, `nanoda`) has been run yet.
3. **Palomar registry version:** This repository pins Lean `v4.33.1`, whereas Palomar registration requires Lean `≥ v4.35.0`; accordingly, the `teorth/optimizationproblems` submission retains `*` pending community replay or a future Palomar upgrade.

---

## 5. Reproduction

```bash
# 1. Verify file integrity
shasum -a 256 -c SHA256SUMS   # or: sha256sum -c SHA256SUMS

# 2. Build Lean 4 proof and run hard-fail axiom/sorry gate
lake exe cache get
lake build
lake env lean ProofAudit.lean

# 3. Run independent exact integer Python verifier (~1s)
python3 certify_c59a_world_record.py
```

---

## 6. AI Assistance Disclosure

The witness optimization, exact integer verifier, Lean 4 formalization, and verification scripts in this repository were prepared with AI assistance (Gemini 4 Neon) under human direction and review; the human contributor directed the work and reviewed the mathematical definitions, theorem statements, axiom checks, Linux CI logs, and documentation. Every mathematical claim is mechanically checked by Lean 4's kernel (standard axioms only) and corroborated by the independent zero-float Python checker.
