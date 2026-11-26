# Isolated Statement-Fidelity Adversary Report: `C_89c` and `C_59a`

- **Auditor:** `adversary-c89c` (isolated; zero `read_board` calls, zero Lean edits)
- **Date:** 2026-11-26
- **Host / Toolchain:** `Darwin 27.2.0 arm64` (`Lean 4.33.1`, commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`, Mathlib `v4.33.1` rev `0df444a360eaa60ab8c11dca51a86af692955474`)
- **Primary Targets Audited:**
  1. `C_89c`: `/tmp/clout-swarm/lean-c89c/C89c/Defs.lean`, `/tmp/clout-swarm/lean-c89c/C89c.lean` (plus full repo scan across all 12 `.lean` modules)
  2. `C_59a`: `/tmp/clout-swarm/lean-c59a/C59a.lean`
- **External Specifications Compared Against:**
  - Raw live `teorth/optimizationproblems` `constants/89c.md` and `constants/59a.md` (`main`)
  - Raw `[P2026]` reference `Shivamshaiv/bidisc-bohr-certificate/certificate/EndToEnd.lean` (pinned commit `27464dce16c7fe41733befe32e672cff87139b6f`)
  - `/tmp/clout-swarm/NOTES/teorth_pr_spec.md`

---

## Verdicts

| Formalization | Target Constant | Verdict | Blocking Defects | Axiom Footprint |
|---|---|---|---|---|
| **`lean-c89c`** | `C_89c` ($K_6$ Ramsey multiplicity upper bound) | **PASS** | None (0) | `[propext, Classical.choice, Quot.sound]` |
| **`lean-c59a`** | `C_59a` (Bidisc Bohr radius $K_2$ upper bound) | **PASS** | None (0) | `[propext, Classical.choice, Quot.sound]` |

---

## Echoed Statements & Audited File Digests

### SHA-256 Checksums of Audited Sources (all corresponding `.olean` files verified FRESH)

```text
ab656a10047c001f31a734358a01fdbf48e08addefa7a7455125ad82af20ba75  /tmp/clout-swarm/lean-c89c/C89c.lean
8ea6c8d110a0b58139993dadf36bd468e7e05682f637cb85972ecf940464e4d2  /tmp/clout-swarm/lean-c89c/C89c/Bridge.lean
f1424297cebc14c364b50d274f78b2c6e428027e41e517ce8076f09e4fbe60e1  /tmp/clout-swarm/lean-c89c/C89c/Cert0.lean
f17b4cd19e9c310b95c4885d0496acf093f27d213bfc29df3a4a44c52e41d3cd  /tmp/clout-swarm/lean-c89c/C89c/Cert1.lean
19889702b057751fa9a7978222b2aeede858ce2c824df73353c60136b02161ad  /tmp/clout-swarm/lean-c89c/C89c/Cert2.lean
bed0861670ce1d6283492bfdfd9411b6a481af61ff725c6a3e4eef2fbdb3b9c2  /tmp/clout-swarm/lean-c89c/C89c/Cert3.lean
4d117497c2166fbeac26d2ad076ece66af5837a5074121ded13729a40a1443c7  /tmp/clout-swarm/lean-c89c/C89c/Defs.lean
8b44f65b54dc8caa2d2100b70a178911bcb6ecccd657e71d32020d40f67c485c  /tmp/clout-swarm/lean-c89c/C89c/Graphon.lean
166f6bcc4dc5f978897bf8a9dd5da5d3001d67c322e462af57e1903b779ab54e  /tmp/clout-swarm/lean-c89c/C89c/LinearF2.lean
d3c1644960fa4b0aa53aa1478eb09eb6368a469b5e2a890aa17f85aa1517d84d  /tmp/clout-swarm/lean-c89c/C89c/Orbits.lean
fd64898c92747fbe9b9ef55ca23d6d5cc6d7f2e2cd8d186447d03f7a4742ddaa  /tmp/clout-swarm/lean-c89c/C89c/OrbitsData.lean
13b9d1886272a20c663c813452069c21b87aff7f3fc03c52ab4f1cf21bc4c696  /tmp/clout-swarm/lean-c89c/C89c/OrbitsLib.lean
1eec9f2a811ccc1c6dc8ae261a5c99cfb572f93f3f7f2c4fb3708c4fea80d08a  /tmp/clout-swarm/lean-c59a/C59a.lean
```

### 1. `C_89c` Echoed Core Definitions (`Optim.RamseyMultiplicity6`)

```lean
noncomputable def monoK6Count {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ := by
  classical
  exact ((Finset.univ.powersetCard 6).filter (fun S : Finset (Fin n) =>
    G.IsClique (S : Set (Fin n)) ∨ Gᶜ.IsClique (S : Set (Fin n)))).card

noncomputable def minMonoK6 (n : ℕ) : ℕ :=
  sInf {k : ℕ | ∃ G : SimpleGraph (Fin n), monoK6Count G = k}

noncomputable def minMonoK6Density (n : ℕ) : ℝ :=
  (minMonoK6 n : ℝ) / (Nat.choose n 6 : ℝ)

noncomputable def C89c : ℝ :=
  Filter.liminf minMonoK6Density Filter.atTop
```

**Echoed Headline Theorems (`C89c.lean`):**
- `exists_graph_monoK6Density_le_exact (n : ℕ) (hn : 6 ≤ n) : ∃ G : SimpleGraph (Fin n), (monoK6Count G : ℝ) / (Nat.choose n 6 : ℝ) ≤ (4757458776713226325231370030032091 : ℝ) / 105233402846062332139835966609296457728`
- `exists_graph_monoK6Density_le_5_7 (n : ℕ) (hn : 6 ≤ n) : ∃ G : SimpleGraph (Fin n), (monoK6Count G : ℝ) / (Nat.choose n 6 : ℝ) ≤ (489716756549 : ℝ) / 10832338896289792`
- `c89c_le_exact : C89c ≤ (4757458776713226325231370030032091 : ℝ) / 105233402846062332139835966609296457728`
- `c89c_le_exact_1105_1541` (alias of `c89c_le_exact`)
- `c89c_le_7406983191 : C89c ≤ (7406983191 : ℝ) / (10 ^ 10 * 2 ^ 14)`
- `c89c_le_07406983191_mul_2pow_neg14 : C89c ≤ (7406983191 : ℝ) / 10 ^ 10 * (2 : ℝ) ^ (-14 : ℤ)`
- `c89c_le_exact_5_7 : C89c ≤ (489716756549 : ℝ) / 10832338896289792`
- `limsup_minMonoK6Density_le_exact : Filter.limsup minMonoK6Density Filter.atTop ≤ (4757458776713226325231370030032091 : ℝ) / 105233402846062332139835966609296457728`

### 2. `C_59a` Echoed Core Definitions (`Optim.BohrRadius`)

```lean
def unitBidisc : Set (ℂ × ℂ) :=
  {p | ‖p.1‖ < 1 ∧ ‖p.2‖ < 1}

def IsSchur (f : ℂ × ℂ → ℂ) : Prop :=
  AnalyticOn ℂ f unitBidisc ∧
    ∀ p ∈ unitBidisc, ‖f p‖ ≤ 1

def HasBidiscCoefficients (f : ℂ × ℂ → ℂ)
    (coeff : ℕ → ℕ → ℂ) : Prop :=
  ∃ radius : ℝ, 0 < radius ∧ radius ≤ 1 ∧
    ∀ z w : ℂ, ‖z‖ < radius → ‖w‖ < radius →
      HasSum (fun i : ℕ × ℕ =>
        coeff i.1 i.2 * z ^ i.1 * w ^ i.2) (f (z, w))

noncomputable def finiteMajorant
    (coeff : ℕ → ℕ → ℂ) (radius : ℝ) (N : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (N + 1),
    ∑ k ∈ Finset.range (N + 1),
      ‖coeff j k‖ * radius ^ (j + k)

def IsBohrAdmissible (radius : ℝ) : Prop :=
  ∀ (f : ℂ × ℂ → ℂ) (coeff : ℕ → ℕ → ℂ),
    IsSchur f → HasBidiscCoefficients f coeff →
      ∀ N : ℕ, finiteMajorant coeff radius N ≤ 1

noncomputable def bohrRadius : ℝ :=
  sSup (insert 0 {radius : ℝ | 0 < radius ∧ IsBohrAdmissible radius})
```

**Echoed Headline Theorems (`C59a.lean`):**
- `bohrRadius_lt_3028252794909876_div_10pow16 : bohrRadius < (3028252794909876 : ℝ) / 10 ^ 16`
- `bohrRadius_lt_302825279490987594822_div_10pow21 : bohrRadius < (302825279490987594822 : ℝ) / 10 ^ 21`

---

## Attack Results (`AR-01` .. `AR-05`)

### `AR-01`: `C_89c` Definition-Fidelity Attack — **PASS**

Compared line-by-line against Terence Tao's `teorth/optimizationproblems` `constants/89c.md`:
> *"For a 2-colouring of the edges of $K_n$, let $k_6$ be the number of $6$-element vertex sets whose fifteen edges all have the same colour. The Ramsey multiplicity constant of $K_6$ is $C_{89c} := \lim_{n\to\infty} \frac{\min k_6}{\binom{n}{6}}$, the minimum over all 2-colourings of $K_n$."*

1. **Unordered 6-subset counting & zero double-counting (`monoK6Count`):**
   - `SimpleGraph (Fin n)` encodes symmetric irreflexive binary relations on `Fin n`, in exact bijection with 2-colorings of the edges of $K_n$ (red = `G.Adj`, blue = `Gᶜ.Adj`).
   - `Finset.univ.powersetCard 6` enumerates all unordered 6-element subsets $S \subseteq \mathrm{Fin}\,n$ (cardinality $\binom{n}{6}$).
   - `SimpleGraph.IsClique` unfolds to `Set.Pairwise S G.Adj` (all $\binom{6}{2}=15$ unordered pairs adjacent in `G`), and `SimpleGraph.instCompl` defines `Gᶜ.Adj u v ↔ u ≠ v ∧ ¬ G.Adj u v`.
   - `Finset.filter` tests `G.IsClique (S : Set (Fin n)) ∨ Gᶜ.IsClique (S : Set (Fin n))` per 6-subset $S$, so each monochromatic 6-subset is counted **at most once** (and for $|S|=6 \ge 2$ the two disjuncts are mutually exclusive anyway).
2. **True minimum & zero junk values (`minMonoK6`, `minMonoK6Density`):**
   - For every $n \in \mathbb{N}$, `{k : ℕ | ∃ G : SimpleGraph (Fin n), monoK6Count G = k}` is non-empty (e.g., witnessed by `⊥ : SimpleGraph (Fin n)`), so `Nat.sInf` is the true minimum over all simple graphs on `Fin n`.
   - For all $n \ge 6$, `Nat.choose n 6 ≥ 1 > 0`, so `(minMonoK6 n : ℝ) / (Nat.choose n 6 : ℝ)` has zero division-by-zero junk values on the tail $n \ge 6$. (The `0 / 0 = 0` values at $n < 6$ cannot affect `Filter.atTop` or any theorem gated by `6 ≤ n`.)
3. **Finite-$n$, `limsup`, and `liminf` strength:**
   - `exists_graph_monoK6Density_le_exact` holds uniformly for **every** $n \ge 6$ (via Lovász $W$-random graph averaging $G(n, W)$ in `Bridge.lean`, giving exact expectation $t_{\mathrm{mono}}(K_6, W)$ with zero $O(1/n)$ error).
   - `limsup_minMonoK6Density_le_exact` proves `Filter.limsup minMonoK6Density Filter.atTop ≤ exact`.
   - Non-blocking note: `C89c` is defined via `Filter.liminf` rather than formally proving convergence (`Tendsto minMonoK6Density atTop (nhds L)` via standard averaging monotonicity for $n \ge 6$). However, because `0 ≤ minMonoK6Density n ≤ exact` holds for **every** $n \ge 6$ and `limsup ≤ exact` is proved, any limit $L$ satisfies $L = \liminf = \limsup \le \text{exact}$ — zero loophole.
4. **Exact arithmetic & world-record comparison (independently verified in Python `fractions.Fraction`):**
   - Degree-9 polynomial at $p = 1105/1541$ matches `4757458776713226325231370030032091 / 105233402846062332139835966609296457728` **identically** ($= 0.7406983190659612\ldots \cdot 2^{-14}$).
   - Decimal bound `7406983191 / (10^10 * 2^14)` ($= 0.7406983191 \cdot 2^{-14}$) rounds **UP** conservatively (margin $+3.404 \times 10^{-11} \cdot 2^{-14}$) and **strictly beats** `[SCIEL2026]` (both exact fraction $0.7422042115280503\ldots \cdot 2^{-14}$ and quoted $0.7422042116 \cdot 2^{-14}$) by $0.00150589\ldots \cdot 2^{-14}$.
   - Clean 1-digit variant ($p = 5/7$): `489716756549 / 10832338896289792` ($= 0.7407005464024919\ldots \cdot 2^{-14}$) also strictly beats `[SCIEL2026]`.
   - Independent Python check of `vo10Graphon` confirmed $|V_{10}| = 1024$, $|F| = 32$, $|Q^{-1}(1)| = 528$, $F \subseteq Q^{-1}(1)$.
5. **`pp.all true` signature check:**
   - Inspected full `pp.all true` output for `monoK6Count`, `minMonoK6`, `minMonoK6Density`, `C89c`, `c89c_le_exact`, `c89c_le_7406983191`, `c89c_le_07406983191_mul_2pow_neg14`, `exists_graph_monoK6Density_le_exact`, and `limsup_minMonoK6Density_le_exact`.
   - Every operator resolves to standard Mathlib instances (`Real.instLE`, `Real.instDivInvMonoid`, `Real.instNatCast`, `Real.instMul`, `Real.instMonoid`, `Int.instNegInt`, `Filter.liminf`, `Filter.limsup`, `SimpleGraph.instCompl`). No integer-division or coercion traps.

---

### `AR-02`: `C_59a` Definition-Fidelity Attack — **PASS**

Compared line-by-line against `teorth/optimizationproblems` `constants/59a.md` (`[Kne2025]`, `[BK1997]`) and `[P2026]` (`Shivamshaiv/bidisc-bohr-certificate/certificate/EndToEnd.lean`, commit `27464dce16c7fe41733befe32e672cff87139b6f`):

1. **Verbatim compatibility with `[P2026]`:**
   - `diff -u` between `[P2026]` lines 25–59 and `C59a.lean` lines 25–57 showed **zero differences** across all six definitions (`unitBidisc`, `IsSchur`, `HasBidiscCoefficients`, `finiteMajorant`, `IsBohrAdmissible`, `bohrRadius`).
2. **`unitBidisc`:** `{p : ℂ × ℂ | ‖p.1‖ < 1 ∧ ‖p.2‖ < 1}` uses `Complex.instNorm` on each coordinate (`|z| < 1 ∧ |w| < 1`), matching $\mathbb{D}^2$ exactly. Proved open in Lean (`test_unitBidisc_isOpen`).
3. **`IsSchur` (`‖f p‖ ≤ 1` vs `< 1`, and `AnalyticOn` vs `AnalyticOnNhd`):**
   - `constants/59a.md` defines $S_2$ as analytic functions $f : \mathbb{D}^2 \to \mathbb{D}$ (strict `‖f p‖ < 1`), whereas `[P2026]` and `C59a.lean` use closed `‖f p‖ ≤ 1`.
   - **Closed-vs-open attack formally refuted in Lean:** We independently proved in Lean 4.33.1 (using only `[propext, Classical.choice, Quot.sound]`) BOTH:
     - `test_strict_eq_closed : strictBohrRadius = bohrRadius` (scaling any closed-Schur witness by $c = (1 + 1/M)/2 \in (0, 1)$ gives a strict-Schur witness violating the same radius), AND
     - `test_fSchur_strict_lt_one`: the actual witness family `fSchur L T S` (for $L, T, S > 0$) itself satisfies strict `‖fSchur L T S p‖ < 1` everywhere on `unitBidisc`.
   - **`AnalyticOn` vs `AnalyticOnNhd` attack formally refuted in Lean:** Using `Mathlib.Analysis.Analytic.Within` (`IsOpen.analyticOn_iff_analyticOnNhd`), we independently proved `AnalyticOn ℂ f unitBidisc ↔ AnalyticOnNhd ℂ f unitBidisc` — matching standard complex holomorphicity on $\mathbb{D}^2$.
4. **`HasBidiscCoefficients`:**
   - `pp.all true` confirms `HasSum` uses `SummationFilter.unconditional (ℕ × ℕ)` in the standard norm topology on `ℂ`. Because `ℂ` is finite-dimensional, unconditional summability equals absolute summability, which uniquely determines `coeff j k` as the exact Taylor coefficients at $(0, 0)$ on any open bidisc $D(0, \text{radius})^2$ ($\text{radius} > 0$). Conversely, every holomorphic function on $\mathbb{D}^2$ has a Taylor series converging absolutely on $\mathbb{D}^2$ (hence on some $0 < \text{radius} \le 1$). Thus `HasBidiscCoefficients` is neither vacuous nor overly permissive.
5. **`finiteMajorant`, `IsBohrAdmissible`, `bohrRadius`:**
   - `finiteMajorant coeff r N` computes $\sum_{j=0}^{N} \sum_{k=0}^{N} |c_{j,k}| r^{j+k}$ using `Complex.instNorm` and `r^(j+k)`. Since all terms are non-negative for $r > 0$, `∀ N, finiteMajorant coeff r N ≤ 1` is equivalent to $\|f_r\|_1 = \sum_{j,k \ge 0} |c_{j,k}| r^{j+k} \le 1$.
   - `bohrRadius := sSup (insert 0 {radius : ℝ | 0 < radius ∧ IsBohrAdmissible radius})`. Inserting `0` guarantees non-emptiness for `csSup_le`; we independently proved `0 ≤ bohrRadius` in Lean (`test_bohrRadius_nonneg`, upper-bounded via $f(z,w)=z$), and no vacuity bug exists.
6. **Exact numerical & strict inequality checks:**
   - `bohrRadius_lt_302825279490987594822_div_10pow21` ($N=56$): $K_2 < 0.302825279490987594822$, strictly beating `[T2026]` ($0.302825279490988$) by $4.05178 \times 10^{-16}$ and `[P2026]` ($0.302825279492$) by $1.012405178 \times 10^{-12}$.
   - `bohrRadius_lt_3028252794909876_div_10pow16` ($N=44$): $K_2 < 0.3028252794909876$, strictly beating `[T2026]` by $4 \times 10^{-16}$.
   - `pp.all true` verified standard `Real.instLT`, `Real.instDivInvMonoid`, `Real.instNatCast`, `Real.instMonoid` on both headline theorems.

---

### `AR-03`: Direct Small-Case Sanity Tests on `C89c/Defs.lean` — **PASS**

All tests were executed directly via `lake env lean --stdin` inside `/tmp/clout-swarm/lean-c89c` (exit code 0, zero `sorryAx`, axioms strictly `[propext, Classical.choice, Quot.sound]`):

| Test | Lean Statement Verified | Result |
|---|---|---|
| Complete $K_6$ on `Fin 6` | `monoK6Count (⊤ : SimpleGraph (Fin 6)) = 1` | PASS (no double count) |
| Empty $\overline{K_6}$ on `Fin 6` | `monoK6Count (⊥ : SimpleGraph (Fin 6)) = 1` | PASS (no double count) |
| Complete $K_7$ on `Fin 7` | `monoK6Count (⊤ : SimpleGraph (Fin 7)) = 7` | PASS ($\binom{7}{6}=7$) |
| Empty $\overline{K_7}$ on `Fin 7` | `monoK6Count (⊥ : SimpleGraph (Fin 7)) = 7` | PASS ($\binom{7}{6}=7$) |
| Single edge on `Fin 6` | `monoK6Count oneEdge6 = 0` | PASS |
| $K_5 \sqcup K_1$ on `Fin 6` | `monoK6Count k5PlusK1 = 0` | PASS |
| $K_6 \sqcup K_1$ on `Fin 7` | `monoK6Count k6PlusK1 = 1` | PASS (only $\{0..5\}$) |
| Minimum at $n=6$ | `minMonoK6 6 = 0` | PASS |
| Non-degeneracy of `C89c` | `0 ≤ C89c` | PASS |
| Erdős random graphon $W \equiv 1/2$ | `tMonoK6 (V := Unit) (fun _ _ => (1 / 2 : ℝ)) = 2 ^ (-14 : ℤ)` | PASS |

---

### `AR-04`: Independent Axiom & Sneaky-Hack Audit — **PASS**

1. **Independent `#print axioms` verification:**
   - **`C89c`** (`C89c`, `exists_graph_monoK6Density_le_exact`, `exists_graph_monoK6Density_le_5_7`, `c89c_le_exact`, `c89c_le_exact_1105_1541`, `c89c_le_7406983191`, `c89c_le_07406983191_mul_2pow_neg14`, `c89c_le_exact_5_7`, `limsup_minMonoK6Density_le_exact`, `tMonoK6_vo10Graphon`, `tMonoK6_vo10Graphon_1105_1541`):
     **ALL depend ONLY on `[propext, Classical.choice, Quot.sound]`.**
   - **`C59a`** (`bohrRadius`, `bohrRadius_lt_3028252794909876_div_10pow16`, `bohrRadius_lt_302825279490987594822_div_10pow21`, `bohrRadius_lt_of_finiteMajorant_gt_one`, `bohrRadius_lt_of_uC_diag_sum_gt_one`, `bohrRadius_lt_of_checkCert`):
     **ALL depend ONLY on `[propext, Classical.choice, Quot.sound]`.**
   - Notable trust upgrade over `[P2026]`: `[P2026]`'s `EndToEnd.lean` contained **7 `native_decide` calls** (pulling in `Lean.ofReduceBool`); both `C89c` and `C59a` use **zero `native_decide`** and **zero `Lean.ofReduceBool`**.
2. **Whole-repository static scan (`grep`) across all 13 `.lean` files (12 in `lean-c89c`, 1 in `lean-c59a`):**
   - **0 occurrences** of `axiom`, `sorry`, `admit`, `native_decide`, `unsafe`, `implemented_by`, `extern`, `notation`, `infix*`, `prefix`, `postfix`, `macro`, `syntax`, `opaque`, `partial`, `local`, `scoped`, `attribute`, or `@[...]`.
   - **Custom `instance` declarations:**
     - `lean-c89c`: only 2 benign local instances — `C89c/Graphon.lean:46` (`instance : Fintype Vec4`) and `C89c.lean:213` (`instance : Nonempty V10`), neither shadowing any Mathlib type.
     - `lean-c59a`: **0 `instance` declarations**.
   - **`set_option` directives:**
     - `lean-c89c`: **0 `set_option` directives**.
     - `lean-c59a`: **2 narrowly-scoped `set_option maxRecDepth 100000 in`** (lines 1846, 1851) strictly around `private theorem checkCert_44` and `private theorem checkCert_56` (purely a kernel reduction depth budget for `decide`, zero soundness impact).
   - **`.olean` freshness:** All 12 `.olean` files in `lean-c89c/.lake/build/lib/lean/` and `C59a.olean` in `lean-c59a/.lake/build/lib/lean/` are **FRESH** (`mtime(olean) ≥ mtime(lean)`), confirming our `#print axioms` and `#check` runs audited the exact current source files.

---

### `AR-05`: Assumed / Unverified Gaps

1. **Single-host macOS ARM64 execution:** All Lean verification so far ran on one host (`Darwin 27.2.0 arm64`); no clean-room Linux `x86_64` CI rebuild from scratch has been executed yet.
2. **Lean 4.33.1 + Mathlib `v4.33.1` TCB & no multi-kernel export replay:** Proof soundness relies on the Lean 4.33.1 kernel (`commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6`) and Mathlib `v4.33.1` (`rev 0df444a360eaa60ab8c11dca51a86af692955474`). No external independent kernel checker (`lean4checker`, `nanoda`, `con-ron`) has yet re-checked the exported environments.
3. **Palomar registry version requirement (`≥ v4.35.0`):** Both `lean-c89c` and `lean-c59a` pin `leanprover/lean4:v4.33.1` (`lake-manifest.json` Mathlib `v4.33.1`), while Palomar registration requires Lean `≥ v4.35.0`. Upgrading both toolchains/manifests to `≥ v4.35.0` and re-verifying is required if targeting Palomar registration (e.g., to omit `*` on `teorth/optimizationproblems`).
4. **External hosting & pinning not yet created:** Neither `/tmp/clout-swarm/lean-c89c` nor `/tmp/clout-swarm/lean-c59a` is currently a Git repository (no pinned commit SHA, GitHub release tag, Zenodo DOI, or `SHA256SUMS` file yet — mandatory for `teorth/optimizationproblems` PRs).
5. **Scoped `maxRecDepth` in `C59a.lean`:** Lines 1846 and 1851 set `maxRecDepth 100000` for kernel `decide` on `rows44` and `rows56`; sound, but CI/external checkers must allow this depth budget.
6. **Unformalized auxiliary properties (non-blocking for upper bounds):**
   - `C89c` does not formalize existence of `lim_{n→∞} minMonoK6Density n` (monotonicity for $n \ge 6$), though `exists_graph_monoK6Density_le_exact` and `limsup_minMonoK6Density_le_exact` already bound any limit.
   - `C59a` does not formalize a positive lower bound on `bohrRadius` (e.g., $1/(3\sqrt{2}) \le K_2$) or Taylor-coefficient uniqueness from `HasBidiscCoefficients` (both standard mathematical facts; definitions match `[P2026]` verbatim).
   - This isolated adversary audit did not independently re-implement the `C89c` 49-orbit sum or `C59a` $N=44/56$ DP outside Lean (relying on Lean's kernel for proof validity while independently auditing statement fidelity, definitions, small cases, axioms, and headline rational arithmetic).

---

## Findings Summary

- **Blocking defects found:** **0** in `C_89c`, **0** in `C_59a`.
- **Non-blocking observations:**
  1. `C89c` defines `C89c` as `Filter.liminf` without explicitly proving limit existence (`Tendsto`); completely mitigated because `exists_graph_monoK6Density_le_exact` (all $n \ge 6$) and `limsup_minMonoK6Density_le_exact` are both proved in `C89c.lean`.
  2. `C59a` defines `IsSchur` with closed `‖f p‖ ≤ 1` (verbatim `[P2026]`) whereas `constants/59a.md` writes open `‖f p‖ < 1`; completely mitigated because we proved in Lean both `strictBohrRadius = bohrRadius` and strict `‖fSchur L T S p‖ < 1` on `unitBidisc`.
  3. Both repos currently pin Lean `v4.33.1` (below Palomar's `≥ v4.35.0` threshold) and are not yet published/pinned in external Git repositories.
