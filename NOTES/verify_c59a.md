# Independent Verification Report: `C_59a` (Bidisc Bohr Radius $K_2$)

## Overall Verdict: **FAIL (strict Step 2 literal `set_option` token ban) — Kernel & Mathematical Soundness: PASS**

- **Steps 1, 3, 4, 5:** **PASS** (clean CoW clone, exact character-for-character `[P2026]` definition match & plain-English fidelity against `constants/59a.md`, clean from-scratch `lake build` with exit code `0` / 0 errors / 0 warnings, and strictly 3 standard axioms `[propext, Classical.choice, Quot.sound]` with `value.hasSorry = false` and zero `native_decide` / `ofReduceBool`).
- **Step 2 (Literal Forbidden-Construct Audit):** **FAIL on literal `set_option` token ban** — outside comments, `C59a.lean` contains **2 matches** of `set_option`:
  - `L1846`: `set_option maxRecDepth 100000 in` (scoped to `private theorem checkCert_44`)
  - `L1851`: `set_option maxRecDepth 100000 in` (scoped to `private theorem checkCert_56`)
  - **0 matches** outside comments for all soundness-affecting tokens (`sorry`, `admit`, `axiom`, `native_decide`, `ofReduceBool`, `trustCompiler`, `implemented_by`, `@[extern`, `unsafe`, `partial`, `csimp`, `opaque`, `local instance`).
  - Note: `maxRecDepth` only raises the recursion depth limit for kernel `decide` reduction and does **not** weaken soundness or introduce axioms. Per verifier discipline, this report does **not** self-waive the explicit `set_option` token check in Step 2; `@coordinator` may either waive scoped `maxRecDepth` or request a refactor eliminating it.

---

## Step 1: Fresh Clean Copy & SHA-256 — **PASS**

### Commands
```bash
rm -rf /tmp/clout-swarm/verify-c59a
cp -c -R /tmp/clout-swarm/lean-c59a /tmp/clout-swarm/verify-c59a
cat /tmp/clout-swarm/lean-c59a/lean-toolchain
cat /tmp/clout-swarm/lean-c59a/lakefile.toml
shasum -a 256 /tmp/clout-swarm/lean-c59a/C59a.lean /tmp/clout-swarm/verify-c59a/C59a.lean
wc -l /tmp/clout-swarm/verify-c59a/C59a.lean
```

### Exit Code
`0`

### Raw Output
```text
=== lean-toolchain ===
leanprover/lean4:v4.33.1
=== lakefile ===
name = "c59a"
version = "0.1.0"
defaultTargets = ["C59a"]

[leanOptions]
pp.unicode.fun = true
autoImplicit = false
relaxedAutoImplicit = false

[[require]]
name = "mathlib"
scope = "leanprover-community"
rev = "v4.33.1"

[[lean_lib]]
name = "C59a"
=== shasum -a 256 ===
1eec9f2a811ccc1c6dc8ae261a5c99cfb572f93f3f7f2c4fb3708c4fea80d08a  /tmp/clout-swarm/lean-c59a/C59a.lean
1eec9f2a811ccc1c6dc8ae261a5c99cfb572f93f3f7f2c4fb3708c4fea80d08a  /tmp/clout-swarm/verify-c59a/C59a.lean
=== line count and all .lean files ===
/tmp/clout-swarm/verify-c59a/C59a.lean
    1886 /tmp/clout-swarm/verify-c59a/C59a.lean
```
(`lake-manifest.json` pins `mathlib` at `v4.33.1`, rev `0df444a360eaa60ab8c11dca51a86af692955474`.)

---

## Step 2: Forbidden-Construct Audit — **FAIL (2 scoped `set_option maxRecDepth` hits; 0 soundness-affecting tokens)**

### Audit Method
Comment-stripping Python parser (handles nested `/- ... -/`, line `-- ...`, and string literals) + raw file scan over `/tmp/clout-swarm/verify-c59a/C59a.lean` matching regex:
`\b(sorry|admit|axiom|native_decide|ofReduceBool|trustCompiler|implemented_by|unsafe|partial|csimp|opaque|set_option)\b|@\[extern|\blocal\s+instance\b`

### Exit Code
`0` (scanner exited cleanly; reported 2 matches outside comments)

### Raw Output
```text
--- Matches OUTSIDE comments (comment-stripped) ---
  L1846 [set_option]: set_option maxRecDepth 100000 in
  L1851 [set_option]: set_option maxRecDepth 100000 in
Total outside-comment matches: 2
--- Matches in RAW file (including comments) ---
  L42 [partial]: /-- Finite rectangular partial sums of the absolute Bohr series. -/
  L1736 [native_decide]: Both certificates are verified purely inside Lean 4's kernel (`decide`, ZERO `native_decide`,
  L1737 [sorry]: ZERO `sorry`, ZERO extra axioms beyond `{propext, Classical.choice, Quot.sound}`).
  L1846 [set_option]: set_option maxRecDepth 100000 in
  L1851 [set_option]: set_option maxRecDepth 100000 in
Total raw matches: 5
```

### Audit Breakdown
- `sorry`: **0** outside comments
- `admit`: **0** outside comments
- `axiom`: **0** outside comments
- `native_decide`: **0** outside comments
- `ofReduceBool`: **0** outside comments
- `trustCompiler`: **0** outside comments
- `implemented_by`: **0** outside comments
- `@[extern`: **0** outside comments
- `unsafe`: **0** outside comments
- `partial`: **0** outside comments
- `csimp`: **0** outside comments
- `opaque`: **0** outside comments
- `local instance`: **0** outside comments
- `set_option`: **2** outside comments (`L1846` & `L1851`, both `set_option maxRecDepth 100000 in`, scoped to kernel `decide` proofs `checkCert_44` and `checkCert_56`).

---

## Step 3: Definition-Fidelity Audit (`[P2026]` §3A & `constants/59a.md`) — **PASS**

### 3a. Verbatim Comparison vs `/tmp/clout-swarm/NOTES/teorth_pr_spec.md` §3A

Compared `C59a.lean` L25–56 (`unitBidisc`, `IsSchur`, `HasBidiscCoefficients`, `finiteMajorant`, `IsBohrAdmissible`, `bohrRadius` in `namespace Optim.BohrRadius`) against `teorth_pr_spec.md` L66–97:

```text
=== Verbatim comparison of Optim.BohrRadius definitions (spec §3A vs C59a.lean) ===
EXACT CHARACTER-FOR-CHARACTER MATCH (32 lines, 1368 bytes)
r21 < r16 < T2026 < P2026: True
T2026 - r21 = 202589/500000000000000000000 = 4.051780000000e-16
P2026 - r21 = 506202589/500000000000000000000 = 1.012405178000e-12
```

### 3b. Plain-English Fidelity Audit vs `teorth/optimizationproblems` `constants/59a.md`
- **`unitBidisc` (`{p | ‖p.1‖ < 1 ∧ ‖p.2‖ < 1}`):** Exact match with $\mathbb{D}^2 = \{(z_1, z_2) \in \mathbb{C}^2 : |z_1|, |z_2| < 1\}$.
- **`IsSchur` (`AnalyticOn ℂ f unitBidisc ∧ ∀ p ∈ unitBidisc, ‖f p‖ ≤ 1`):** Verbatim match with `[P2026]`. Note: `constants/59a.md` states $f : \mathbb{D}^2 \to \mathbb{D}$ (strict open unit disc $|f| < 1$). Mathematically, $K_2$ is identical under $|f| < 1$ vs $|f| \le 1$ (by the Maximum Modulus Principle, every non-constant holomorphic map $\mathbb{D}^2 \to \overline{\mathbb{D}}$ maps into $\mathbb{D}$, while constant unimodular maps $|c| = 1$ trivially satisfy $\|f_r\|_1 = 1 \le 1$ for all $r > 0$). Moreover, the concrete witness `fSchur L T S` in `C59a.lean` satisfies the **strict** inequality `‖fSchur L T S p‖ < 1` everywhere on `unitBidisc` (because `4 * S * (conj Q * P).re > 0` strictly on `unitBidisc` in `isSchur_fSchur`, L585–623), so the witness itself lies inside the strict open-disc Schur class $S_2$.
- **`HasBidiscCoefficients`:** Requires a genuine locally convergent Taylor expansion `HasSum (fun i : ℕ × ℕ => coeff i.1 i.2 * z ^ i.1 * w ^ i.2) (f (z, w))` on some positive polydisc `0 < radius ≤ 1` (non-vacuous; explicitly proven for `fSchur L T (1/t)` in `hasBidiscCoefficients_fSchur`, L718–740).
- **`finiteMajorant` & `IsBohrAdmissible`:** Rectangular partial sums $\sum_{j=0}^N \sum_{k=0}^N |c_{jk}| r^{j+k} \le 1$ for all $N \in \mathbb{N}$ is equivalent to $\|f_r\|_1 \le 1$ since all summands are nonnegative.
- **`bohrRadius` (`sSup (insert 0 {radius : ℝ | 0 < radius ∧ IsBohrAdmissible radius})`):** Non-vacuous (`0 ∈ insert 0 ...`) and bounded above (proved genuinely via `csSup_le` in `bohrRadius_lt_of_finiteMajorant_gt_one`, L94–106; not exploiting Mathlib's `sSup = 0` junk value for unbounded sets).
- **Exact `ℝ` inequalities proven:**
  - `bohrRadius < (3028252794909876 : ℝ) / 10 ^ 16` (`= 0.3028252794909876 < 0.302825279490988`)
  - `bohrRadius < (302825279490987594822 : ℝ) / 10 ^ 21` (`= 0.302825279490987594822 < 0.302825279490988`, improving `[T2026]` by `4.05178e-16` and `[P2026]` by `1.012405178e-12`).

---

## Step 4: Fresh Compilation from Scratch — **PASS**

### 4a. Removal of Prebuilt `C59a.*` Artifacts
Commands:
```bash
find /tmp/clout-swarm/verify-c59a/.lake/build -name 'C59a*' -print
find /tmp/clout-swarm/verify-c59a/.lake/build -name 'C59a*' -delete
find /tmp/clout-swarm/verify-c59a/.lake/build -name 'C59a*' -print
```
Exit Code: `0`

Raw Output (8 deleted files, 0 remaining):
```text
/tmp/clout-swarm/verify-c59a/.lake/build/ir/C59a.setup.json
/tmp/clout-swarm/verify-c59a/.lake/build/ir/C59a.c
/tmp/clout-swarm/verify-c59a/.lake/build/ir/C59a.c.hash
/tmp/clout-swarm/verify-c59a/.lake/build/lib/lean/C59a.olean.hash
/tmp/clout-swarm/verify-c59a/.lake/build/lib/lean/C59a.ilean.hash
/tmp/clout-swarm/verify-c59a/.lake/build/lib/lean/C59a.olean
/tmp/clout-swarm/verify-c59a/.lake/build/lib/lean/C59a.ilean
/tmp/clout-swarm/verify-c59a/.lake/build/lib/lean/C59a.trace
=== verify 0 C59a* artifacts remain ===
```

### 4b. `lake build`
Command:
```bash
cd /tmp/clout-swarm/verify-c59a && lake build
```
Exit Code: `0`

Raw Output (progress spinner frames stripped):
```text
Build completed successfully (2035 jobs).
```
(0 errors, 0 warnings.)

Rebuilt artifact SHA-256:
```text
ed4a421bfb10212f850e9bc3f1363541f10df60b44b479d05b47d64768ad0a68  /tmp/clout-swarm/verify-c59a/.lake/build/lib/lean/C59a.olean
```

---

## Step 5: Independent Axiom & `pp.all` Type Check — **PASS**

### Command
```bash
cd /tmp/clout-swarm/verify-c59a && lake env lean --stdin <<'EOF'
import C59a
import Lean
set_option pp.all true in #check @Optim.BohrRadius.bohrRadius_lt_3028252794909876_div_10pow16
set_option pp.all true in #check @Optim.BohrRadius.bohrRadius_lt_302825279490987594822_div_10pow21
#print axioms Optim.BohrRadius.bohrRadius_lt_3028252794909876_div_10pow16
#print axioms Optim.BohrRadius.bohrRadius_lt_302825279490987594822_div_10pow21
-- plus typecheck examples + Lean.collectAxioms / thmInfo / value.hasSorry / DefinitionSafety.safe #eval
EOF
```

### Exit Code
`0`

### Raw Output
```text
Optim.BohrRadius.bohrRadius_lt_3028252794909876_div_10pow16 : @LT.lt.{0} Real Real.instLT Optim.BohrRadius.bohrRadius
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@OfNat.ofNat.{0} Real (nat_lit 3028252794909876)
      (@instOfNatAtLeastTwo.{0} Real (nat_lit 3028252794909876) Real.instNatCast
        (@Nat.instAtLeastTwoHAddOfNat
          (@OfNat.ofNat.{0} Nat (nat_lit 3028252794909875) (instOfNatNat (nat_lit 3028252794909875)))
          (@Nat.instNeZeroSucc
            (@OfNat.ofNat.{0} Nat (nat_lit 3028252794909874) (instOfNatNat (nat_lit 3028252794909874)))))))
    (@HPow.hPow.{0, 0, 0} Real Nat Real
      (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
      (@OfNat.ofNat.{0} Real (nat_lit 10)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 10) Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))))))
      (@OfNat.ofNat.{0} Nat (nat_lit 16) (instOfNatNat (nat_lit 16)))))
Optim.BohrRadius.bohrRadius_lt_302825279490987594822_div_10pow21 : @LT.lt.{0} Real Real.instLT
  Optim.BohrRadius.bohrRadius
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@OfNat.ofNat.{0} Real (nat_lit 302825279490987594822)
      (@instOfNatAtLeastTwo.{0} Real (nat_lit 302825279490987594822) Real.instNatCast
        (@Nat.instAtLeastTwoHAddOfNat
          (@OfNat.ofNat.{0} Nat (nat_lit 302825279490987594821) (instOfNatNat (nat_lit 302825279490987594821)))
          (@Nat.instNeZeroSucc
            (@OfNat.ofNat.{0} Nat (nat_lit 302825279490987594820) (instOfNatNat (nat_lit 302825279490987594820)))))))
    (@HPow.hPow.{0, 0, 0} Real Nat Real
      (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
      (@OfNat.ofNat.{0} Real (nat_lit 10)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 10) Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))))))
      (@OfNat.ofNat.{0} Nat (nat_lit 21) (instOfNatNat (nat_lit 21)))))
'Optim.BohrRadius.bohrRadius_lt_3028252794909876_div_10pow16' depends on axioms: [propext, Classical.choice, Quot.sound]
'Optim.BohrRadius.bohrRadius_lt_302825279490987594822_div_10pow21' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
=== Kernel Check: Optim.BohrRadius.bohrRadius_lt_3028252794909876_div_10pow16 ===
  is thmInfo          : true
  levelParams         : []
  collectAxioms       : [propext, Classical.choice, Quot.sound]
  subset of allowed   : true
  contains sorryAx    : false
  contains ofReduceBool: false
  contains trustComp  : false
  value.hasSorry      : false
=== Kernel Check: Optim.BohrRadius.bohrRadius_lt_302825279490987594822_div_10pow21 ===
  is thmInfo          : true
  levelParams         : []
  collectAxioms       : [propext, Classical.choice, Quot.sound]
  subset of allowed   : true
  contains sorryAx    : false
  contains ofReduceBool: false
  contains trustComp  : false
  value.hasSorry      : false
  def Optim.BohrRadius.unitBidisc: safety=Lean.DefinitionSafety.safe, levelParams=[]
  def Optim.BohrRadius.IsSchur: safety=Lean.DefinitionSafety.safe, levelParams=[]
  def Optim.BohrRadius.HasBidiscCoefficients: safety=Lean.DefinitionSafety.safe, levelParams=[]
  def Optim.BohrRadius.finiteMajorant: safety=Lean.DefinitionSafety.safe, levelParams=[]
  def Optim.BohrRadius.IsBohrAdmissible: safety=Lean.DefinitionSafety.safe, levelParams=[]
  def Optim.BohrRadius.bohrRadius: safety=Lean.DefinitionSafety.safe, levelParams=[]
KERNEL_CHECK_PASS
```
