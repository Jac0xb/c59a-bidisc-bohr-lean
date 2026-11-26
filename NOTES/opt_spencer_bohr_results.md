# World-Record Optimizer Lane 2 (`opt-spencer-bohr`) — Results & Exact Certificates

- **Date:** 2026-11-26
- **Workspace:** `/tmp/clout-swarm/opt_spencer_bohr/`
- **Targets Audited & Attacked (all exact specs fetched directly from `teorth/optimizationproblems`):**
  1. `C_59a` — Bidisc Bohr Radius $K_2$ Upper Bound (**NEW EXACT-CERTIFIED WORLD RECORD!**)
  2. `C_10c` — Spencer Discrepancy Constant Lower Bound (deep structural + computational audit)
  3. `C_51a` — Erdős #513 Maximum-Term Constant Lower Bound (deep structural + computational audit)

---

## 1. NEW WORLD RECORD CERTIFIED: `C_59a` — Bidisc Bohr Radius $K_2$ Upper Bound

### Live Records vs. Our New World Record
| Source | Certified Bound | Improvement vs `[T2026]` | Certificate Complexity |
|---|---|---|---|
| `[P2026]` (Lean 4) | $K_2 < 302825279492 / 10^{12} = 0.302825279492$ | — | $L, T$ (10-digit), $S = 10^{15}$, $N=28$ |
| `[T2026]` (live leaderboard `*`, unformalized) | $K_2 < 3028252794909880 / 10^{16} = 0.302825279490988$ | baseline | $3\times 3$ unitary colligation with **149-digit** denominator, $N=40$ |
| **OURS (Compact Lean Witness)** | **$K_2 < 3028252794909876 / 10^{16} = 0.3028252794909876$** | **$-4.00 \times 10^{-16}$** | **10-digit** $L=10^9, T=1226959270$ (+ $S=10^{20}$ explicit Schur), $N=44$ |
| **OURS (Sharp 21-Digit Witness)** | **$K_2 < 302825279490987594822 / 10^{21} = 0.302825279490987594822$** | **$-4.05178 \times 10^{-16}$** | **13-digit** $L=10^{12}, T=1226959270039$ (+ $S=10^{25}$ explicit Schur), $N=56$ |

- **Exact Verifier (stdlib Python, ZERO floats):** `/tmp/clout-swarm/opt_spencer_bohr/certify_c59a_world_record.py`
- **Exact Witness JSON:** `/tmp/clout-swarm/opt_spencer_bohr/c59a_world_record_cert.json`

### Why It Works & Why Lean 4 Formalization Is Ultra-Clean
1. **Agler–Herglotz Discovery:** By reducing bidisc Schur functions $f_S = (S - h)/(S + h) \in S_2$ to the Herglotz limit $h(z, w) = 1 + 2\sum_{k\ge 1} v^*(U\Delta)^k v$ ($\operatorname{Re} h > 0$ on $\mathbb{D}^2$), we eliminated the $10^{-15}$–$10^{-26}$ cancellation that forced `[T2026]` into 149-digit denominators.
2. **Global Search Over Higher Colligations ($m = 2, 3, 4, 5, 6, 8$):**
   - Multi-start Riemannian Adam + line search (`opt_c59a.c`), $r$-annealing from $r = 0.50 \to 0.302825$ (`opt_c59a_anneal.c`), exact tangent Hessian checks at $m=3$ and $m=4$ (all cross-coupling Hessian eigenvalues $\le 0$), clean fixed-$|A|$ general Schur colligation scans ($a \in [0, 0.999]$), and unconstrained 2D-FFT Herglotz polynomial optimization ($D = 8, 12, 16$) ALL confirmed the canonical bidegree-$(1,1)$ Herglotz extremizer $U = \operatorname{diag}(1, i)\begin{pmatrix} c & s \\ s & -c \end{pmatrix}$, $v = (1/\sqrt{2}, 1/\sqrt{2})$ with optimal $\alpha^* = T/L = 1.2269592700391990135475...$, achieving the exact limit
     $$r^* = 0.3028252794909875948218341940639...$$
   - `[T2026]`'s unformalized bound stopped at `0.3028252794909880`, leaving `4.0518 × 10^{-16}` on the table while needing 149-digit integers.
3. **3-Line Algebraic Positivity Identity (Lean-4 Ready):**
   For $U = (1+z)(1-w)$, $V = 1+zw$, $P = L U + i T V$, $Q = L V + i T U$ ($L, T > 0$):
   $$4 \operatorname{Re}(\overline{Q(z,w)} P(z,w)) = 2(L^2 + T^2)\Big((1 - |z|^2)|1 - w|^2 + (1 - |w|^2)|1 + z|^2\Big) > 0 \quad \forall (z, w) \in \mathbb{D}^2.$$
   Hence $Q \ne 0$, $\operatorname{Re}(P/Q) > 0$, and for every $S > 0$, $f_S = (SQ - P)/(SQ + P)$ satisfies $|f_S| < 1$ on $\mathbb{D}^2$ ($f_S \in S_2$).
4. **Pure Integer Recurrence (ZERO Rational Division):**
   - Herglotz path: $g_{j,k} = h_{j,k} (L + i T)^{j+k} \in \mathbb{Z}[i]$ satisfies a 3-term integer recurrence with coefficients $\pm iT$ and $-(L^2+T^2)$.
   - Explicit finite Schur path (no $S \to \infty$ limit needed!): $G_{j,k} = (f_S)_{j,k} ((S+1)(L+iT))^{j+k+1} \in \mathbb{Z}[i]$ satisfies a 3-term integer recurrence, and exact `math.isqrt` floor sums prove strictly $B_{r,N}(f_S) > 1$, hence $K_2 < r$.

---

## 2. Deep Structural & Computational Audit: `C_10c` (Spencer Discrepancy LB)

- **Exact Spec:** $C_{10c} = \sup_{n\ge 1, A \in [-1,1]^{n\times n}} \frac{1}{\sqrt{n}} \min_{x \in \{\pm 1\}^n} \|Ax\|_\infty$. Live record: `[H2026]` $5/\sqrt{8} \approx 1.767766953$ (reproduced exactly).
- **Two Structural Theorems Proved:**
  1. **Kleitman Integer Ceiling for Real $A \in [-1, 1]^{n\times n}$:** For any $A \in [-1, 1]^{n\times n}$ with $\mathrm{disc}(A) \ge t$, each row's positive/negative cap has Hamming diameter $\le \lfloor n - t \rfloor$, giving an exact integer ceiling $\mathrm{disc}(A) \le n - D_{\min}(n)$ for EVERY $n$ (eliminating $n \le 9$ and $n = 12$ completely).
  2. **Linear Code Multiplicity Collapse:** For any binary linear $[n, k]$ code containing $\mathbf{1}$ (so $2^{k-1}$ complementary pairs of rows), any column multiplicity $m_u \ge 2$ is strictly dominated by $m_u \bmod 2 \in \{0, 1\}$, explaining why `[L2026]` ($n=17$) and any beating code must be nonlinear or non-binary.
- **Exhaustive & Metaheuristic Search Results (all verified in `clang -O3`, 12 threads):**
  - Sanity checks reproduced to **0 uncovered** in `<1 s`: `[G2026]` ($n=6, R=1$), `[H2026]` ($n=8, z=1, R=1$), `[L2026]` ($n=17, P=16, R=5$), and `(15, 32, 4)` ($n=16, m=15, P=16, R=4 \implies 7/4 = 1.75$).
  - `$n=15, P=15, R=4$` (`7/√15 = 1.8074`, slack `1.777`): FWHT-BLS, hybrid FWHT+SA, and 36M-move high-T random SA ALL hit an exact floor of **233 / 16,384 uncovered** (1.42%) — strong evidence $K_{sc}(15, 4) > 30$. Warm-started continuous $A \in [-1,1]^{15\times 15}$ ascent reached `5.265 / √15 = 1.359`.
  - `$n=18, P=18, R=5$` (`8/√18 = 1.8856`, slack `1.733`): best `3,846 / 131,072` (2.93%).
  - `$n=20, P=20, R=6$` (`8/√20 = 1.7889`, slack `2.306`): unconstrained `4,688 / 524,288` (0.89%); `a=3` all-ones padded (`m=17`) `1,274 / 262,144` (0.486%).
  - `$n=24, m=23, z=1, \text{all1}=1, R=7$` (`9/√24 = 1.8371`, slack `2.235`): **EXHAUSTIVE** over all 182,362 canonical $\mathbb{Z}_{23}$ circulant seeds gave `704 / 165,376` orbit reps (`16,192 / 4,194,304` = **0.386% uncovered**), achieved uniquely by the $24\times 24$ Paley Hadamard seed `0x0299af`!
  - `$n=25, m=25, R=8$` (`9/5 = 1.8000`, slack `2.694`): $\mathbb{Z}_{25}$ circulant reached `2,943 / 671,092` (**0.4385% uncovered**, seed `0x07b0bb7`); $\mathbb{Z}_5 \times \mathbb{Z}_5$ reached `3,839 / 671,104` (0.572%).

---

## 3. Deep Structural & Computational Audit: `C_51a` (Erdős #513 Maximum-Term LB)

- **Exact Spec:** $C_{51} = \sup_{f \text{ trans. entire}} \liminf_{r\to\infty} \mu(r, f)/M(r, f)$. Live record: `[R2026b]` `0.5850788196744` (`[Can2026d]` replay `0.5850788196745135`, reproduced to all 16 digits).
- **Exact Period-$p$ Generalization Tested:** Every bilateral Laurent series satisfying a general scaling identity $k(\lambda z) = C z^p k(z)$ has the exact form $a_n = u_{n \bmod p} (K^{-1} e^{i\alpha})^{n^2/2}$, and by the Maximum Modulus Principle on annuli, $\beta(f) = \min_{j} \mu(r_j, k) / M(r_j, k)$ over the $\le p$ transition corners $r_j$ per period.
- **Finding:** Multi-start 12-thread Nelder–Mead optimization (`opt_c51a.c`) over $p = 2, 3, 4, 5$ (including complex phases, unequal amplitudes, and skipped max-term regimes $|u_r| < K^{-1/2}$), plus symmetric $p=2$ phase scans and local $p=3, 4$ axis/palindromic probes around `[R2026b]`, ALL collapsed back to the $p=1$ `[R2026b]` optimum `0.5850788196745135`:
  - Even for symmetric pure-phase $p = 2$ ($|u_0|=|u_1|=1, u_1 = e^{i\phi}$, where both transition corners have IDENTICAL max modulus), breaking $\theta \leftrightarrow -\theta$ symmetry splits the two equal interior peaks $\theta^* \approx \pm 0.64554$ linearly in $|\phi|$, creating a sharp V-cusp maximum at $\phi = 0$.
