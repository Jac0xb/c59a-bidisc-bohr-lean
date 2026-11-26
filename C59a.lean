import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.Linear
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.IntervalCases

namespace Optim.BohrRadius

/-!
## 1. Definitions (verbatim match with `[P2026]` `Optim.BohrRadius`)
-/

/-- The open unit bidisc. -/
def unitBidisc : Set (ℂ × ℂ) :=
  {p | ‖p.1‖ < 1 ∧ ‖p.2‖ < 1}

/-- Analytic functions from the unit bidisc to the closed unit disc. -/
def IsSchur (f : ℂ × ℂ → ℂ) : Prop :=
  AnalyticOn ℂ f unitBidisc ∧
    ∀ p ∈ unitBidisc, ‖f p‖ ≤ 1

/-- A family is the actual locally convergent Taylor germ of `f` at zero. -/
def HasBidiscCoefficients (f : ℂ × ℂ → ℂ)
    (coeff : ℕ → ℕ → ℂ) : Prop :=
  ∃ radius : ℝ, 0 < radius ∧ radius ≤ 1 ∧
    ∀ z w : ℂ, ‖z‖ < radius → ‖w‖ < radius →
      HasSum (fun i : ℕ × ℕ =>
        coeff i.1 i.2 * z ^ i.1 * w ^ i.2) (f (z, w))

/-- Finite rectangular partial sums of the absolute Bohr series. -/
noncomputable def finiteMajorant
    (coeff : ℕ → ℕ → ℂ) (radius : ℝ) (N : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (N + 1),
    ∑ k ∈ Finset.range (N + 1),
      ‖coeff j k‖ * radius ^ (j + k)

def IsBohrAdmissible (radius : ℝ) : Prop :=
  ∀ (f : ℂ × ℂ → ℂ) (coeff : ℕ → ℕ → ℂ),
    IsSchur f → HasBidiscCoefficients f coeff →
      ∀ N : ℕ, finiteMajorant coeff radius N ≤ 1

/-- The bidisc Bohr radius, as the supremum of universally admissible radii. -/
noncomputable def bohrRadius : ℝ :=
  sSup (insert 0 {radius : ℝ | 0 < radius ∧ IsBohrAdmissible radius})

/-!
## 2. General Upper-Bound Reduction via Continuity of `finiteMajorant`
-/

lemma finiteMajorant_mono {coeff : ℕ → ℕ → ℂ} {r₁ r₂ : ℝ} {N : ℕ}
    (hr₁ : 0 ≤ r₁) (h : r₁ ≤ r₂) :
    finiteMajorant coeff r₁ N ≤ finiteMajorant coeff r₂ N := by
  unfold finiteMajorant
  refine Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => ?_
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr₁ h (j + k)) (norm_nonneg _)

lemma continuous_finiteMajorant (coeff : ℕ → ℕ → ℂ) (N : ℕ) :
    Continuous (fun r : ℝ => finiteMajorant coeff r N) := by
  unfold finiteMajorant
  refine continuous_finsetSum _ fun j _ => continuous_finsetSum _ fun k _ => ?_
  exact continuous_const.mul (continuous_pow (j + k))

theorem bohrRadius_lt_of_finiteMajorant_gt_one
    (f : ℂ × ℂ → ℂ) (coeff : ℕ → ℕ → ℂ) (R : ℝ) (N : ℕ)
    (hR : 0 < R) (hf : IsSchur f) (hcoeff : HasBidiscCoefficients f coeff)
    (hgt : 1 < finiteMajorant coeff R N) :
    bohrRadius < R := by
  have hcont : ContinuousAt (fun r : ℝ => finiteMajorant coeff r N) R :=
    (continuous_finiteMajorant coeff N).continuousAt
  have hev : ∀ᶠ r in nhds R, 1 < finiteMajorant coeff r N :=
    hcont.eventually (isOpen_Ioi.mem_nhds hgt)
  rw [Metric.eventually_nhds_iff] at hev
  rcases hev with ⟨δ, hδpos, hδ⟩
  let r' : ℝ := max (R / 2) (R - δ / 2)
  have hr'_pos : 0 < r' := lt_of_lt_of_le (by linarith) (le_max_left _ _)
  have hr'_lt : r' < R := max_lt (by linarith) (by linarith)
  have hr'_dist : dist r' R < δ := by
    rw [Real.dist_eq, abs_of_neg (sub_neg.mpr hr'_lt)]
    have h1 : R - δ / 2 ≤ r' := le_max_right _ _
    linarith
  have hr'_gt : 1 < finiteMajorant coeff r' N := hδ hr'_dist
  have hle : bohrRadius ≤ r' := by
    unfold bohrRadius
    refine csSup_le (Set.insert_nonempty 0 _) ?_
    intro x hx
    rcases hx with rfl | ⟨hxpos, hxadm⟩
    · exact hr'_pos.le
    · by_contra hnot
      push Not at hnot
      have h1 : finiteMajorant coeff r' N ≤ finiteMajorant coeff x N :=
        finiteMajorant_mono hr'_pos.le hnot.le
      have h2 : finiteMajorant coeff x N ≤ 1 := hxadm f coeff hf hcoeff N
      linarith
  exact lt_of_le_of_lt hle hr'_lt

/-!
## 3. General Bidegree-(1,1) Rational Function Power Series
-/

def ratNum (n00 n10 n01 n11 : ℂ) (z w : ℂ) : ℂ :=
  n00 + n10 * z + n01 * w + n11 * z * w

def ratDen (a10 a01 a11 : ℂ) (z w : ℂ) : ℂ :=
  1 + a10 * z + a01 * w + a11 * z * w

def ratCoeff (n00 n10 n01 n11 a10 a01 a11 : ℂ) : ℕ → ℕ → ℂ
  | 0, 0 => n00
  | j + 1, 0 =>
      (if j = 0 then n10 else 0) - a10 * ratCoeff n00 n10 n01 n11 a10 a01 a11 j 0
  | 0, k + 1 =>
      (if k = 0 then n01 else 0) - a01 * ratCoeff n00 n10 n01 n11 a10 a01 a11 0 k
  | j + 1, k + 1 =>
      (if j = 0 ∧ k = 0 then n11 else 0)
      - a10 * ratCoeff n00 n10 n01 n11 a10 a01 a11 j (k + 1)
      - a01 * ratCoeff n00 n10 n01 n11 a10 a01 a11 (j + 1) k
      - a11 * ratCoeff n00 n10 n01 n11 a10 a01 a11 j k
termination_by j k => j + k

lemma ratCoeff_norm_le (n00 n10 n01 n11 a10 a01 a11 : ℂ) :
    ∀ j k : ℕ,
      ‖ratCoeff n00 n10 n01 n11 a10 a01 a11 j k‖ ≤
        (‖n00‖ + ‖n10‖ + ‖n01‖ + ‖n11‖) * (2 + ‖a10‖ + ‖a01‖ + ‖a11‖) ^ (j + k) := by
  let C : ℝ := ‖n00‖ + ‖n10‖ + ‖n01‖ + ‖n11‖
  let B : ℝ := 2 + ‖a10‖ + ‖a01‖ + ‖a11‖
  have hC : 0 ≤ C := by positivity
  have hB1 : 1 ≤ B := by
    have : 0 ≤ ‖a10‖ + ‖a01‖ + ‖a11‖ := by positivity
    linarith
  suffices h : ∀ d j k : ℕ, j + k = d →
      ‖ratCoeff n00 n10 n01 n11 a10 a01 a11 j k‖ ≤ C * B ^ d by
    intro j k
    exact h (j + k) j k rfl
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro j k hjk
    cases j with
    | zero =>
      cases k with
      | zero =>
        subst hjk
        simp only [ratCoeff, Nat.add_zero, pow_zero, mul_one]
        dsimp [C]
        have : 0 ≤ ‖n10‖ + ‖n01‖ + ‖n11‖ := by positivity
        linarith
      | succ k =>
        have hk : 0 + k < d := by omega
        have hih := ih (0 + k) hk 0 k rfl
        have hd : d = (0 + k) + 1 := by omega
        rw [hd, pow_succ, ratCoeff]
        have hterm : ‖if k = 0 then n01 else 0‖ ≤ C := by
          split_ifs
          · have : 0 ≤ ‖n00‖ + ‖n10‖ + ‖n11‖ := by positivity
            linarith
          · simpa using hC
        have h1 : ‖if k = 0 then n01 else 0‖ ≤ C * B ^ (0 + k) :=
          hterm.trans (le_mul_of_one_le_right hC (one_le_pow₀ hB1))
        calc ‖(if k = 0 then n01 else 0) - a01 * ratCoeff n00 n10 n01 n11 a10 a01 a11 0 k‖
            ≤ ‖if k = 0 then n01 else 0‖ + ‖a01 * ratCoeff n00 n10 n01 n11 a10 a01 a11 0 k‖ :=
              norm_sub_le _ _
          _ = ‖if k = 0 then n01 else 0‖ + ‖a01‖ * ‖ratCoeff n00 n10 n01 n11 a10 a01 a11 0 k‖ := by
              rw [norm_mul]
          _ ≤ C * B ^ (0 + k) + ‖a01‖ * (C * B ^ (0 + k)) := by
              gcongr
          _ = C * B ^ (0 + k) * (1 + ‖a01‖) := by ring
          _ ≤ C * B ^ (0 + k) * B := by
              gcongr
              have : 0 ≤ ‖a10‖ + ‖a11‖ := by positivity
              linarith
          _ = C * (B ^ (0 + k) * B) := by ring
    | succ j =>
      cases k with
      | zero =>
        have hj : j + 0 < d := by omega
        have hih := ih (j + 0) hj j 0 rfl
        have hd : d = (j + 0) + 1 := by omega
        rw [hd, pow_succ, ratCoeff]
        have hterm : ‖if j = 0 then n10 else 0‖ ≤ C := by
          split_ifs
          · have : 0 ≤ ‖n00‖ + ‖n01‖ + ‖n11‖ := by positivity
            linarith
          · simpa using hC
        have h1 : ‖if j = 0 then n10 else 0‖ ≤ C * B ^ (j + 0) :=
          hterm.trans (le_mul_of_one_le_right hC (one_le_pow₀ hB1))
        calc ‖(if j = 0 then n10 else 0) - a10 * ratCoeff n00 n10 n01 n11 a10 a01 a11 j 0‖
            ≤ ‖if j = 0 then n10 else 0‖ + ‖a10 * ratCoeff n00 n10 n01 n11 a10 a01 a11 j 0‖ :=
              norm_sub_le _ _
          _ = ‖if j = 0 then n10 else 0‖ + ‖a10‖ * ‖ratCoeff n00 n10 n01 n11 a10 a01 a11 j 0‖ := by
              rw [norm_mul]
          _ ≤ C * B ^ (j + 0) + ‖a10‖ * (C * B ^ (j + 0)) := by
              gcongr
          _ = C * B ^ (j + 0) * (1 + ‖a10‖) := by ring
          _ ≤ C * B ^ (j + 0) * B := by
              gcongr
              have : 0 ≤ ‖a01‖ + ‖a11‖ := by positivity
              linarith
          _ = C * (B ^ (j + 0) * B) := by ring
      | succ k =>
        have h1lt : j + (k + 1) < d := by omega
        have h2lt : (j + 1) + k < d := by omega
        have h3lt : j + k < d := by omega
        have hih1 := ih (j + (k + 1)) h1lt j (k + 1) rfl
        have hih2 := ih ((j + 1) + k) h2lt (j + 1) k rfl
        have hih3 := ih (j + k) h3lt j k rfl
        have heq1 : (j + 1) + k = j + k + 1 := by omega
        have heq2 : j + (k + 1) = j + k + 1 := by omega
        have hd : d = (j + k + 1) + 1 := by omega
        rw [heq2] at hih1
        rw [heq1] at hih2
        have hBpow : B ^ (j + k) ≤ B ^ (j + k + 1) := by
          rw [pow_succ]
          exact le_mul_of_one_le_right (by positivity) hB1
        have hih3' : ‖ratCoeff n00 n10 n01 n11 a10 a01 a11 j k‖ ≤ C * B ^ (j + k + 1) :=
          hih3.trans (mul_le_mul_of_nonneg_left hBpow hC)
        have hterm : ‖if j = 0 ∧ k = 0 then n11 else 0‖ ≤ C := by
          split_ifs
          · have : 0 ≤ ‖n00‖ + ‖n10‖ + ‖n01‖ := by positivity
            linarith
          · simpa using hC
        have h0 : ‖if j = 0 ∧ k = 0 then n11 else 0‖ ≤ C * B ^ (j + k + 1) :=
          hterm.trans (le_mul_of_one_le_right hC (one_le_pow₀ hB1))
        rw [hd, pow_succ, ratCoeff]
        have htri :
            ‖(if j = 0 ∧ k = 0 then n11 else 0)
              - a10 * ratCoeff n00 n10 n01 n11 a10 a01 a11 j (k + 1)
              - a01 * ratCoeff n00 n10 n01 n11 a10 a01 a11 (j + 1) k
              - a11 * ratCoeff n00 n10 n01 n11 a10 a01 a11 j k‖
            ≤ ‖if j = 0 ∧ k = 0 then n11 else 0‖
              + ‖a10‖ * ‖ratCoeff n00 n10 n01 n11 a10 a01 a11 j (k + 1)‖
              + ‖a01‖ * ‖ratCoeff n00 n10 n01 n11 a10 a01 a11 (j + 1) k‖
              + ‖a11‖ * ‖ratCoeff n00 n10 n01 n11 a10 a01 a11 j k‖ := by
          have t1 := norm_sub_le
            ((if j = 0 ∧ k = 0 then n11 else 0)
              - a10 * ratCoeff n00 n10 n01 n11 a10 a01 a11 j (k + 1)
              - a01 * ratCoeff n00 n10 n01 n11 a10 a01 a11 (j + 1) k)
            (a11 * ratCoeff n00 n10 n01 n11 a10 a01 a11 j k)
          have t2 := norm_sub_le
            ((if j = 0 ∧ k = 0 then n11 else 0)
              - a10 * ratCoeff n00 n10 n01 n11 a10 a01 a11 j (k + 1))
            (a01 * ratCoeff n00 n10 n01 n11 a10 a01 a11 (j + 1) k)
          have t3 := norm_sub_le
            (if j = 0 ∧ k = 0 then n11 else 0)
            (a10 * ratCoeff n00 n10 n01 n11 a10 a01 a11 j (k + 1))
          simp only [norm_mul] at t1 t2 t3
          linarith
        calc ‖(if j = 0 ∧ k = 0 then n11 else 0)
                - a10 * ratCoeff n00 n10 n01 n11 a10 a01 a11 j (k + 1)
                - a01 * ratCoeff n00 n10 n01 n11 a10 a01 a11 (j + 1) k
                - a11 * ratCoeff n00 n10 n01 n11 a10 a01 a11 j k‖
            ≤ C * B ^ (j + k + 1)
              + ‖a10‖ * (C * B ^ (j + k + 1))
              + ‖a01‖ * (C * B ^ (j + k + 1))
              + ‖a11‖ * (C * B ^ (j + k + 1)) := by
              have ha1 := mul_le_mul_of_nonneg_left hih1 (norm_nonneg a10)
              have ha2 := mul_le_mul_of_nonneg_left hih2 (norm_nonneg a01)
              have ha3 := mul_le_mul_of_nonneg_left hih3' (norm_nonneg a11)
              linarith
          _ = C * B ^ (j + k + 1) * (1 + ‖a10‖ + ‖a01‖ + ‖a11‖) := by ring
          _ ≤ C * B ^ (j + k + 1) * B := by
              gcongr
              linarith
          _ = C * (B ^ (j + k + 1) * B) := by ring

lemma hasBidiscCoefficients_rat (n00 n10 n01 n11 a10 a01 a11 : ℂ) :
    HasBidiscCoefficients
      (fun p => ratNum n00 n10 n01 n11 p.1 p.2 / ratDen a10 a01 a11 p.1 p.2)
      (ratCoeff n00 n10 n01 n11 a10 a01 a11) := by
  let C : ℝ := ‖n00‖ + ‖n10‖ + ‖n01‖ + ‖n11‖
  let B : ℝ := 2 + ‖a10‖ + ‖a01‖ + ‖a11‖
  have hC : 0 ≤ C := by positivity
  have hB2 : 2 ≤ B := by
    have : 0 ≤ ‖a10‖ + ‖a01‖ + ‖a11‖ := by positivity
    linarith
  have hBpos : 0 < B := by linarith
  let ρ : ℝ := 1 / (2 * B)
  have hρpos : 0 < ρ := by positivity
  have hρle1 : ρ ≤ 1 := by
    dsimp [ρ]
    rw [div_le_one (by positivity)]
    linarith
  refine ⟨ρ, hρpos, hρle1, fun z w hz hw => ?_⟩
  let c := ratCoeff n00 n10 n01 n11 a10 a01 a11
  let term : ℕ × ℕ → ℂ := fun p => c p.1 p.2 * z ^ p.1 * w ^ p.2
  have hBρ : B * ρ = 1 / 2 := by
    dsimp [ρ]
    field_simp
  have hsumm : Summable term := by
    have hgeom : Summable (fun n : ℕ => ((1 / 2 : ℝ) ^ n)) :=
      summable_geometric_of_lt_one (by norm_num) (by norm_num)
    have hprod : Summable (fun p : ℕ × ℕ => (C * (1 / 2 : ℝ) ^ p.1) * ((1 / 2 : ℝ) ^ p.2)) :=
      (hgeom.mul_left C).mul_of_nonneg hgeom
        (fun n => by positivity) (fun n => by positivity)
    refine Summable.of_norm_bounded hprod fun p => ?_
    have hnorm : ‖term p‖ = ‖c p.1 p.2‖ * ‖z‖ ^ p.1 * ‖w‖ ^ p.2 := by
      simp [term, norm_pow]
    rw [hnorm]
    have hc := ratCoeff_norm_le n00 n10 n01 n11 a10 a01 a11 p.1 p.2
    calc ‖c p.1 p.2‖ * ‖z‖ ^ p.1 * ‖w‖ ^ p.2
        ≤ (C * B ^ (p.1 + p.2)) * ρ ^ p.1 * ρ ^ p.2 := by
          gcongr
      _ = C * (B * ρ) ^ p.1 * (B * ρ) ^ p.2 := by
          rw [pow_add, mul_pow, mul_pow]; ring
      _ = (C * (1 / 2 : ℝ) ^ p.1) * (1 / 2 : ℝ) ^ p.2 := by
          rw [hBρ]
  let s : ℂ := ∑' p : ℕ × ℕ, term p
  have hs : HasSum term s := hsumm.hasSum
  have hden_ne : ratDen a10 a01 a11 z w ≠ 0 := by
    have hz1 : ‖z‖ < 1 := hz.trans_le hρle1
    have hw1 : ‖w‖ < 1 := hw.trans_le hρle1
    have hlt : ‖a10 * z + a01 * w + a11 * z * w‖ < 1 := by
      calc ‖a10 * z + a01 * w + a11 * z * w‖
          ≤ ‖a10 * z + a01 * w‖ + ‖a11 * z * w‖ := norm_add_le _ _
        _ ≤ ‖a10 * z‖ + ‖a01 * w‖ + ‖a11 * z * w‖ := by
            gcongr; exact norm_add_le _ _
        _ = ‖a10‖ * ‖z‖ + ‖a01‖ * ‖w‖ + ‖a11‖ * ‖z‖ * ‖w‖ := by
            simp only [norm_mul]
        _ ≤ ‖a10‖ * ρ + ‖a01‖ * ρ + ‖a11‖ * ρ * 1 := by
            have h1 : ‖a10‖ * ‖z‖ ≤ ‖a10‖ * ρ := by gcongr
            have h2 : ‖a01‖ * ‖w‖ ≤ ‖a01‖ * ρ := by gcongr
            have h3 : ‖a11‖ * ‖z‖ * ‖w‖ ≤ ‖a11‖ * ρ * 1 := by
              have h3a : ‖a11‖ * ‖z‖ ≤ ‖a11‖ * ρ := by gcongr
              exact mul_le_mul h3a hw1.le (norm_nonneg _) (by positivity)
            linarith
        _ = (‖a10‖ + ‖a01‖ + ‖a11‖) * ρ := by ring
        _ ≤ B * ρ := by
            gcongr
            linarith
        _ = 1 / 2 := hBρ
        _ < 1 := by norm_num
    intro hzero
    have heq : a10 * z + a01 * w + a11 * z * w = -1 := by
      unfold ratDen at hzero
      linear_combination hzero
    rw [heq, norm_neg, norm_one] at hlt
    exact lt_irrefl 1 hlt
  let g1 : ℕ × ℕ → ℂ := fun p =>
    if p.1 = 0 then 0 else a10 * z * term (p.1 - 1, p.2)
  let g2 : ℕ × ℕ → ℂ := fun p =>
    if p.2 = 0 then 0 else a01 * w * term (p.1, p.2 - 1)
  let g11 : ℕ × ℕ → ℂ := fun p =>
    if p.1 = 0 ∨ p.2 = 0 then 0 else a11 * z * w * term (p.1 - 1, p.2 - 1)
  have hg1 : HasSum g1 (a10 * z * s) := by
    have hinj : Function.Injective (fun p : ℕ × ℕ => (p.1 + 1, p.2)) := by
      intro p q h
      simp only [Prod.mk.injEq, Nat.add_right_cancel_iff] at h
      exact Prod.ext h.1 h.2
    rw [← hinj.hasSum_iff]
    · have hcomp : (g1 ∘ fun p : ℕ × ℕ => (p.1 + 1, p.2)) = fun p => a10 * z * term p := by
        ext p
        simp [g1]
      rw [hcomp]
      exact hs.mul_left (a10 * z)
    · intro p hp
      cases h1 : p.1 with
      | zero => simp [g1, h1]
      | succ j =>
        exfalso
        exact hp ⟨(j, p.2), Prod.ext h1.symm rfl⟩
  have hg2 : HasSum g2 (a01 * w * s) := by
    have hinj : Function.Injective (fun p : ℕ × ℕ => (p.1, p.2 + 1)) := by
      intro p q h
      simp only [Prod.mk.injEq, Nat.add_right_cancel_iff] at h
      exact Prod.ext h.1 h.2
    rw [← hinj.hasSum_iff]
    · have hcomp : (g2 ∘ fun p : ℕ × ℕ => (p.1, p.2 + 1)) = fun p => a01 * w * term p := by
        ext p
        simp [g2]
      rw [hcomp]
      exact hs.mul_left (a01 * w)
    · intro p hp
      cases h2 : p.2 with
      | zero => simp [g2, h2]
      | succ k =>
        exfalso
        exact hp ⟨(p.1, k), Prod.ext rfl h2.symm⟩
  have hg11 : HasSum g11 (a11 * z * w * s) := by
    have hinj : Function.Injective (fun p : ℕ × ℕ => (p.1 + 1, p.2 + 1)) := by
      intro p q h
      simp only [Prod.mk.injEq, Nat.add_right_cancel_iff] at h
      exact Prod.ext h.1 h.2
    rw [← hinj.hasSum_iff]
    · have hcomp : (g11 ∘ fun p : ℕ × ℕ => (p.1 + 1, p.2 + 1)) = fun p => a11 * z * w * term p := by
        ext p
        simp [g11]
      rw [hcomp]
      exact hs.mul_left (a11 * z * w)
    · intro p hp
      cases h1 : p.1 with
      | zero => simp [g11, h1]
      | succ j =>
        cases h2 : p.2 with
        | zero => simp [g11, h2]
        | succ k =>
          exfalso
          exact hp ⟨(j, k), Prod.ext h1.symm h2.symm⟩
  have hsum_lhs :
      HasSum (fun p => term p + g1 p + g2 p + g11 p) (ratDen a10 a01 a11 z w * s) := by
    have h := ((hs.add hg1).add hg2).add hg11
    convert h using 1
    unfold ratDen
    ring
  have hsum_rhs :
      HasSum
        (fun p : ℕ × ℕ =>
          (if p = (0, 0) then n00 else 0)
          + (if p = (1, 0) then n10 * z else 0)
          + (if p = (0, 1) then n01 * w else 0)
          + (if p = (1, 1) then n11 * z * w else 0))
        (ratNum n00 n10 n01 n11 z w) := by
    unfold ratNum
    exact (((hasSum_ite_eq (0, 0) n00).add (hasSum_ite_eq (1, 0) (n10 * z))).add
      (hasSum_ite_eq (0, 1) (n01 * w))).add (hasSum_ite_eq (1, 1) (n11 * z * w))
  have hfun_eq :
      (fun p => term p + g1 p + g2 p + g11 p) =
      (fun p : ℕ × ℕ =>
        (if p = (0, 0) then n00 else 0)
        + (if p = (1, 0) then n10 * z else 0)
        + (if p = (0, 1) then n01 * w else 0)
        + (if p = (1, 1) then n11 * z * w else 0)) := by
    ext ⟨j, k⟩
    cases j with
    | zero =>
      cases k with
      | zero =>
        simp [term, g1, g2, g11, c, ratCoeff]
      | succ k =>
        cases k with
        | zero =>
          simp [term, g1, g2, g11, c, ratCoeff]
          ring
        | succ k =>
          simp [term, g1, g2, g11, c, ratCoeff, pow_succ]
          ring
    | succ j =>
      cases k with
      | zero =>
        cases j with
        | zero =>
          simp [term, g1, g2, g11, c, ratCoeff]
          ring
        | succ j =>
          simp [term, g1, g2, g11, c, ratCoeff, pow_succ]
          ring
      | succ k =>
        cases j with
        | zero =>
          cases k with
          | zero =>
            simp [term, g1, g2, g11, c, ratCoeff]
            ring
          | succ k =>
            simp [term, g1, g2, g11, c, ratCoeff, pow_succ]
            ring
        | succ j =>
          simp [term, g1, g2, g11, c, ratCoeff, pow_succ]
          ring
  rw [hfun_eq] at hsum_lhs
  have heq : ratDen a10 a01 a11 z w * s = ratNum n00 n10 n01 n11 z w :=
    hsum_lhs.unique hsum_rhs
  have hs_eq : s = ratNum n00 n10 n01 n11 z w / ratDen a10 a01 a11 z w := by
    rw [eq_div_iff hden_ne]
    simpa [mul_comm] using heq
  simpa [hs_eq] using hs

lemma continuousAt_ratCoeff
    {n00 n10 n01 n11 a10 a01 a11 : ℝ → ℂ} {t₀ : ℝ}
    (hn00 : ContinuousAt n00 t₀) (hn10 : ContinuousAt n10 t₀)
    (hn01 : ContinuousAt n01 t₀) (hn11 : ContinuousAt n11 t₀)
    (ha10 : ContinuousAt a10 t₀) (ha01 : ContinuousAt a01 t₀)
    (ha11 : ContinuousAt a11 t₀) :
    ∀ j k : ℕ, ContinuousAt (fun t => ratCoeff (n00 t) (n10 t) (n01 t) (n11 t)
      (a10 t) (a01 t) (a11 t) j k) t₀ := by
  suffices h : ∀ d j k : ℕ, j + k = d →
      ContinuousAt (fun t => ratCoeff (n00 t) (n10 t) (n01 t) (n11 t)
        (a10 t) (a01 t) (a11 t) j k) t₀ by
    intro j k
    exact h (j + k) j k rfl
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro j k hjk
    cases j with
    | zero =>
      cases k with
      | zero => simpa [ratCoeff] using hn00
      | succ k =>
        simp only [ratCoeff]
        have hih := ih (0 + k) (by omega) 0 k rfl
        have h1 : ContinuousAt (fun t => if k = 0 then n01 t else 0) t₀ := by
          split_ifs
          · exact hn01
          · exact continuousAt_const
        exact h1.sub (ha01.mul hih)
    | succ j =>
      cases k with
      | zero =>
        simp only [ratCoeff]
        have hih := ih (j + 0) (by omega) j 0 rfl
        have h1 : ContinuousAt (fun t => if j = 0 then n10 t else 0) t₀ := by
          split_ifs
          · exact hn10
          · exact continuousAt_const
        exact h1.sub (ha10.mul hih)
      | succ k =>
        simp only [ratCoeff]
        have hih1 := ih (j + (k + 1)) (by omega) j (k + 1) rfl
        have hih2 := ih ((j + 1) + k) (by omega) (j + 1) k rfl
        have hih3 := ih (j + k) (by omega) j k rfl
        have h1 : ContinuousAt (fun t => if j = 0 ∧ k = 0 then n11 t else 0) t₀ := by
          split_ifs
          · exact hn11
          · exact continuousAt_const
        exact ((h1.sub (ha10.mul hih1)).sub (ha01.mul hih2)).sub (ha11.mul hih3)

/-!
## 4. The Agler–Herglotz Bidegree-(1,1) Family and Herglotz Limit Reduction
-/

def polyU (z w : ℂ) : ℂ := (1 + z) * (1 - w)
def polyV (z w : ℂ) : ℂ := 1 + z * w

def polyP (L T : ℝ) (z w : ℂ) : ℂ :=
  (L : ℂ) * polyU z w + Complex.I * (T : ℂ) * polyV z w

def polyQ (L T : ℝ) (z w : ℂ) : ℂ :=
  (L : ℂ) * polyV z w + Complex.I * (T : ℂ) * polyU z w

noncomputable def fSchur (L T S : ℝ) (p : ℂ × ℂ) : ℂ :=
  ((S : ℂ) * polyQ L T p.1 p.2 - polyP L T p.1 p.2) /
    ((S : ℂ) * polyQ L T p.1 p.2 + polyP L T p.1 p.2)

lemma four_mul_re_conj_Q_mul_P (L T : ℝ) (z w : ℂ) :
    4 * (starRingEnd ℂ (polyQ L T z w) * polyP L T z w).re =
      2 * (L ^ 2 + T ^ 2) *
        ((1 - ‖z‖ ^ 2) * ‖1 - w‖ ^ 2 + (1 - ‖w‖ ^ 2) * ‖1 + z‖ ^ 2) := by
  simp only [polyQ, polyP, polyU, polyV, Complex.sq_norm, Complex.normSq_apply,
    Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    Complex.one_re, Complex.one_im]
  ring

lemma norm_sq_add_sub_norm_sq_sub (S : ℝ) (a b : ℂ) :
    ‖(S : ℂ) * a + b‖ ^ 2 - ‖(S : ℂ) * a - b‖ ^ 2 =
      4 * S * (starRingEnd ℂ a * b).re := by
  simp only [Complex.sq_norm, Complex.normSq_apply,
    Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

lemma re_conj_Q_mul_P_pos {L T : ℝ} (hL : 0 < L) (hT : 0 < T)
    {p : ℂ × ℂ} (hp : p ∈ unitBidisc) :
    0 < (starRingEnd ℂ (polyQ L T p.1 p.2) * polyP L T p.1 p.2).re := by
  rcases hp with ⟨hz, hw⟩
  have h1z : 0 < 1 - ‖p.1‖ ^ 2 := by nlinarith [norm_nonneg p.1]
  have h1w : 0 < 1 - ‖p.2‖ ^ 2 := by nlinarith [norm_nonneg p.2]
  have h1mw : 0 < ‖(1 : ℂ) - p.2‖ := by
    have htri : 1 - ‖p.2‖ ≤ ‖(1 : ℂ) - p.2‖ := by
      simpa using norm_sub_norm_le (1 : ℂ) p.2
    linarith
  have h1pz : 0 < ‖(1 : ℂ) + p.1‖ := by
    have htri : 1 - ‖p.1‖ ≤ ‖(1 : ℂ) + p.1‖ := by
      simpa [sub_neg_eq_add, norm_neg] using norm_sub_norm_le (1 : ℂ) (-p.1)
    linarith
  have hLT : 0 < L ^ 2 + T ^ 2 := by positivity
  have hpos :
      0 < 2 * (L ^ 2 + T ^ 2) *
        ((1 - ‖p.1‖ ^ 2) * ‖(1 : ℂ) - p.2‖ ^ 2 + (1 - ‖p.2‖ ^ 2) * ‖(1 : ℂ) + p.1‖ ^ 2) := by
    positivity
  linarith [four_mul_re_conj_Q_mul_P L T p.1 p.2]

lemma isSchur_fSchur {L T S : ℝ} (hL : 0 < L) (hT : 0 < T) (hS : 0 < S) :
    IsSchur (fSchur L T S) := by
  have hden_ne : ∀ p ∈ unitBidisc, (S : ℂ) * polyQ L T p.1 p.2 + polyP L T p.1 p.2 ≠ 0 := by
    intro p hp
    have hre := re_conj_Q_mul_P_pos hL hT hp
    have hdiff := norm_sq_add_sub_norm_sq_sub S (polyQ L T p.1 p.2) (polyP L T p.1 p.2)
    have hpos : 0 < ‖(S : ℂ) * polyQ L T p.1 p.2 + polyP L T p.1 p.2‖ ^ 2 := by
      nlinarith [sq_nonneg ‖(S : ℂ) * polyQ L T p.1 p.2 - polyP L T p.1 p.2‖]
    intro hzero
    rw [hzero, norm_zero, zero_pow two_ne_zero] at hpos
    exact lt_irrefl 0 hpos
  constructor
  · have hU : AnalyticOn ℂ (fun p : ℂ × ℂ => polyU p.1 p.2) unitBidisc :=
      (analyticOn_const.add analyticOn_fst).mul (analyticOn_const.sub analyticOn_snd)
    have hV : AnalyticOn ℂ (fun p : ℂ × ℂ => polyV p.1 p.2) unitBidisc :=
      analyticOn_const.add (analyticOn_fst.mul analyticOn_snd)
    have hP : AnalyticOn ℂ (fun p : ℂ × ℂ => polyP L T p.1 p.2) unitBidisc :=
      (analyticOn_const.mul hU).add (analyticOn_const.mul hV)
    have hQ : AnalyticOn ℂ (fun p : ℂ × ℂ => polyQ L T p.1 p.2) unitBidisc :=
      (analyticOn_const.mul hV).add (analyticOn_const.mul hU)
    have hnum : AnalyticOn ℂ (fun p : ℂ × ℂ => (S : ℂ) * polyQ L T p.1 p.2 - polyP L T p.1 p.2) unitBidisc :=
      (analyticOn_const.mul hQ).sub hP
    have hden : AnalyticOn ℂ (fun p : ℂ × ℂ => (S : ℂ) * polyQ L T p.1 p.2 + polyP L T p.1 p.2) unitBidisc :=
      (analyticOn_const.mul hQ).add hP
    exact hnum.div hden hden_ne
  · intro p hp
    have hre := re_conj_Q_mul_P_pos hL hT hp
    have hdiff := norm_sq_add_sub_norm_sq_sub S (polyQ L T p.1 p.2) (polyP L T p.1 p.2)
    have hden_pos : 0 < ‖(S : ℂ) * polyQ L T p.1 p.2 + polyP L T p.1 p.2‖ :=
      norm_pos_iff.mpr (hden_ne p hp)
    have hsq : ‖(S : ℂ) * polyQ L T p.1 p.2 - polyP L T p.1 p.2‖ ^ 2 ≤
        ‖(S : ℂ) * polyQ L T p.1 p.2 + polyP L T p.1 p.2‖ ^ 2 := by
      nlinarith
    have hle : ‖(S : ℂ) * polyQ L T p.1 p.2 - polyP L T p.1 p.2‖ ≤
        ‖(S : ℂ) * polyQ L T p.1 p.2 + polyP L T p.1 p.2‖ := by
      nlinarith [norm_nonneg ((S : ℂ) * polyQ L T p.1 p.2 - polyP L T p.1 p.2)]
    unfold fSchur
    rw [norm_div, div_le_one hden_pos]
    exact hle

noncomputable def gN10 (L T t : ℝ) : ℂ :=
  -((L : ℂ) - Complex.I * (T : ℂ)) / (((1 + t : ℝ) : ℂ) * ((L : ℂ) + Complex.I * (T : ℂ)))

noncomputable def gN01 (L T t : ℝ) : ℂ :=
  ((L : ℂ) - Complex.I * (T : ℂ)) / (((1 + t : ℝ) : ℂ) * ((L : ℂ) + Complex.I * (T : ℂ)))

noncomputable def gN11 (L T t : ℝ) : ℂ :=
  2 * ((L : ℂ) - Complex.I * (T : ℂ)) / (((1 + t : ℝ) : ℂ) * ((L : ℂ) + Complex.I * (T : ℂ)))

noncomputable def gA10 (L T t : ℝ) : ℂ :=
  ((t : ℂ) * (L : ℂ) + Complex.I * (T : ℂ)) / (((1 + t : ℝ) : ℂ) * ((L : ℂ) + Complex.I * (T : ℂ)))

noncomputable def gA01 (L T t : ℝ) : ℂ :=
  -((t : ℂ) * (L : ℂ) + Complex.I * (T : ℂ)) / (((1 + t : ℝ) : ℂ) * ((L : ℂ) + Complex.I * (T : ℂ)))

noncomputable def gA11 (L T t : ℝ) : ℂ :=
  (((1 - t : ℝ) : ℂ) * ((L : ℂ) - Complex.I * (T : ℂ))) /
    (((1 + t : ℝ) : ℂ) * ((L : ℂ) + Complex.I * (T : ℂ)))

noncomputable def gCoeff (L T t : ℝ) : ℕ → ℕ → ℂ :=
  ratCoeff 0 (gN10 L T t) (gN01 L T t) (gN11 L T t) (gA10 L T t) (gA01 L T t) (gA11 L T t)

noncomputable def fCoeff (L T t : ℝ) (j k : ℕ) : ℂ :=
  if j = 0 ∧ k = 0 then (((1 - t) / (1 + t) : ℝ) : ℂ)
  else (((2 * t) / (1 + t) : ℝ) : ℂ) * gCoeff L T t j k

lemma denom_D_ne_zero {L T : ℝ} (hL : 0 < L) :
    (L : ℂ) + Complex.I * (T : ℂ) ≠ 0 := by
  intro h
  have hre := congr_arg Complex.re h
  simp at hre
  linarith

lemma fSchur_inv_eq {L T t : ℝ} (hL : 0 < L) (hT : 0 < T) (ht : 0 < t)
    {z w : ℂ} (hp : (z, w) ∈ unitBidisc) :
    fSchur L T (1 / t) (z, w) =
      (((1 - t) / (1 + t) : ℝ) : ℂ) +
        (((2 * t) / (1 + t) : ℝ) : ℂ) *
          (ratNum 0 (gN10 L T t) (gN01 L T t) (gN11 L T t) z w /
            ratDen (gA10 L T t) (gA01 L T t) (gA11 L T t) z w) := by
  have hD : (L : ℂ) + Complex.I * (T : ℂ) ≠ 0 := denom_D_ne_zero hL
  have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have ht1 : ((1 + t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
  have h1t : (1 : ℂ) + (t : ℂ) ≠ 0 := by
    simpa [Complex.ofReal_add, Complex.ofReal_one] using ht1
  have hdenS : ((1 / t : ℝ) : ℂ) * polyQ L T z w + polyP L T z w ≠ 0 := by
    have hre := re_conj_Q_mul_P_pos hL hT hp
    have hdiff := norm_sq_add_sub_norm_sq_sub (1 / t) (polyQ L T z w) (polyP L T z w)
    have hS : 0 < 1 / t := by positivity
    have hpos : 0 < ‖((1 / t : ℝ) : ℂ) * polyQ L T z w + polyP L T z w‖ ^ 2 := by
      nlinarith [sq_nonneg ‖((1 / t : ℝ) : ℂ) * polyQ L T z w - polyP L T z w‖]
    intro hzero
    rw [hzero, norm_zero, zero_pow two_ne_zero] at hpos
    exact lt_irrefl 0 hpos
  have hQ_tP : polyQ L T z w + (t : ℂ) * polyP L T z w ≠ 0 := by
    intro hzero
    apply hdenS
    have : ((1 / t : ℝ) : ℂ) * polyQ L T z w + polyP L T z w =
        (polyQ L T z w + (t : ℂ) * polyP L T z w) / (t : ℂ) := by
      push_cast
      field_simp
    rw [this, hzero, zero_div]
  have hratDen_eq :
      (((1 + t : ℝ) : ℂ) * ((L : ℂ) + Complex.I * (T : ℂ))) *
        ratDen (gA10 L T t) (gA01 L T t) (gA11 L T t) z w =
      polyQ L T z w + (t : ℂ) * polyP L T z w := by
    unfold ratDen gA10 gA01 gA11 polyQ polyP polyU polyV
    push_cast
    field_simp
    ring
  have hratDen_ne : ratDen (gA10 L T t) (gA01 L T t) (gA11 L T t) z w ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hratDen_eq
    exact hQ_tP hratDen_eq.symm
  have hratNum_eq :
      (((1 + t : ℝ) : ℂ) * ((L : ℂ) + Complex.I * (T : ℂ))) *
        ratNum 0 (gN10 L T t) (gN01 L T t) (gN11 L T t) z w =
      polyQ L T z w - polyP L T z w := by
    unfold ratNum gN10 gN01 gN11 polyQ polyP polyU polyV
    push_cast
    field_simp
    ring
  have hdiv :
      ratNum 0 (gN10 L T t) (gN01 L T t) (gN11 L T t) z w /
        ratDen (gA10 L T t) (gA01 L T t) (gA11 L T t) z w =
      (polyQ L T z w - polyP L T z w) / (polyQ L T z w + (t : ℂ) * polyP L T z w) := by
    rw [← hratNum_eq, ← hratDen_eq, mul_div_mul_left _ _ (mul_ne_zero ht1 hD)]
  rw [hdiv]
  unfold fSchur
  push_cast
  field_simp
  ring

lemma hasBidiscCoefficients_fSchur {L T t : ℝ} (hL : 0 < L) (hT : 0 < T) (ht : 0 < t) :
    HasBidiscCoefficients (fSchur L T (1 / t)) (fCoeff L T t) := by
  rcases hasBidiscCoefficients_rat 0 (gN10 L T t) (gN01 L T t) (gN11 L T t)
      (gA10 L T t) (gA01 L T t) (gA11 L T t) with ⟨ρ, hρpos, hρle1, hsum⟩
  refine ⟨ρ, hρpos, hρle1, fun z w hz hw => ?_⟩
  have hp : (z, w) ∈ unitBidisc := ⟨hz.trans_le hρle1, hw.trans_le hρle1⟩
  rw [fSchur_inv_eq hL hT ht hp]
  let c1 : ℂ := (((1 - t) / (1 + t) : ℝ) : ℂ)
  let c2 : ℂ := (((2 * t) / (1 + t) : ℝ) : ℂ)
  have hg : HasSum (fun i : ℕ × ℕ => gCoeff L T t i.1 i.2 * z ^ i.1 * w ^ i.2)
      (ratNum 0 (gN10 L T t) (gN01 L T t) (gN11 L T t) z w /
        ratDen (gA10 L T t) (gA01 L T t) (gA11 L T t) z w) := hsum z w hz hw
  have hadd := (hasSum_ite_eq (0, 0) c1).add (hg.mul_left c2)
  refine hadd.congr_fun fun i => ?_
  rcases i with ⟨j, k⟩
  by_cases hjk : j = 0 ∧ k = 0
  · rcases hjk with ⟨rfl, rfl⟩
    simp [fCoeff, gCoeff, ratCoeff, c1, c2]
  · have hne : (j, k) ≠ (0, 0) := by
      intro h
      exact hjk (Prod.mk.inj h)
    simp only [fCoeff, hjk, hne, ↓reduceIte, zero_add, c2]
    ring

lemma finiteMajorant_fCoeff {L T t r : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (N : ℕ) :
    finiteMajorant (fCoeff L T t) r N =
      (1 - t) / (1 + t) +
        (2 * t) / (1 + t) *
          ∑ j ∈ Finset.range (N + 1),
            ∑ k ∈ Finset.range (N + 1),
              ‖gCoeff L T t j k‖ * r ^ (j + k) := by
  have h1 : 0 ≤ (1 - t) / (1 + t) := by positivity
  have h2 : 0 ≤ (2 * t) / (1 + t) := by positivity
  unfold finiteMajorant
  rw [Finset.mul_sum]
  have hsplit :
      (1 - t) / (1 + t) +
        ∑ j ∈ Finset.range (N + 1),
          (2 * t) / (1 + t) *
            ∑ k ∈ Finset.range (N + 1), ‖gCoeff L T t j k‖ * r ^ (j + k) =
      ∑ j ∈ Finset.range (N + 1),
        ((if j = 0 then (1 - t) / (1 + t) else 0) +
          (2 * t) / (1 + t) *
            ∑ k ∈ Finset.range (N + 1), ‖gCoeff L T t j k‖ * r ^ (j + k)) := by
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq']
    simp
  rw [hsplit]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  have hsplit2 :
      (if j = 0 then (1 - t) / (1 + t) else 0) +
        ∑ k ∈ Finset.range (N + 1),
          (2 * t) / (1 + t) * (‖gCoeff L T t j k‖ * r ^ (j + k)) =
      ∑ k ∈ Finset.range (N + 1),
        ((if k = 0 then (if j = 0 then (1 - t) / (1 + t) else 0) else 0) +
          (2 * t) / (1 + t) * (‖gCoeff L T t j k‖ * r ^ (j + k))) := by
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq']
    simp
  rw [hsplit2]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases hjk : j = 0 ∧ k = 0
  · rcases hjk with ⟨rfl, rfl⟩
    simp only [fCoeff, gCoeff, ratCoeff, and_self, ↓reduceIte, Complex.norm_real,
      Real.norm_of_nonneg h1, norm_zero, mul_zero, add_zero, pow_zero, mul_one]
  · have hnot : ¬ (k = 0 ∧ j = 0) := fun ⟨hk, hj⟩ => hjk ⟨hj, hk⟩
    have hite : (if k = 0 then (if j = 0 then (1 - t) / (1 + t) else 0) else 0) = 0 := by
      split_ifs <;> simp_all
    rw [hite, zero_add]
    simp only [fCoeff, hjk, ↓reduceIte, norm_mul, Complex.norm_real, Real.norm_of_nonneg h2]
    ring

/-- The scaled Gaussian-integer-valued sequence `uC L T j k` satisfying
`gCoeff L T 0 j k = (L - iT) / (L + iT)^(j+k) * uC L T j k` for `j + k ≥ 1`. -/
def uC (L T : ℝ) : ℕ → ℕ → ℂ
  | 0, 0 => 0
  | j + 1, 0 => if j = 0 then -1 else -(Complex.I * (T : ℂ)) * uC L T j 0
  | 0, k + 1 => if k = 0 then 1 else (Complex.I * (T : ℂ)) * uC L T 0 k
  | j + 1, k + 1 =>
      if j = 0 ∧ k = 0 then 2 * (L : ℂ)
      else -(Complex.I * (T : ℂ)) * uC L T j (k + 1)
         + (Complex.I * (T : ℂ)) * uC L T (j + 1) k
         - ((L ^ 2 + T ^ 2 : ℝ) : ℂ) * uC L T j k
termination_by j k => j + k

lemma gCoeff_zero_eq_uC {L T : ℝ} (hL : 0 < L) :
    ∀ j k : ℕ, 1 ≤ j + k →
      gCoeff L T 0 j k =
        ((L : ℂ) - Complex.I * (T : ℂ)) / ((L : ℂ) + Complex.I * (T : ℂ)) ^ (j + k) *
          uC L T j k := by
  have hD : (L : ℂ) + Complex.I * (T : ℂ) ≠ 0 := denom_D_ne_zero hL
  have hDDc : ((L : ℂ) + Complex.I * (T : ℂ)) * ((L : ℂ) - Complex.I * (T : ℂ)) =
      ((L ^ 2 + T ^ 2 : ℝ) : ℂ) := by
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  suffices h : ∀ d j k : ℕ, j + k = d → 1 ≤ d →
      gCoeff L T 0 j k =
        ((L : ℂ) - Complex.I * (T : ℂ)) / ((L : ℂ) + Complex.I * (T : ℂ)) ^ d *
          uC L T j k by
    intro j k hjk
    exact h (j + k) j k rfl hjk
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro j k hjk hd1
    cases j with
    | zero =>
      cases k with
      | zero => omega
      | succ k =>
        cases k with
        | zero =>
          have hd : d = 1 := by omega
          subst hd
          simp [gCoeff, ratCoeff, gN01, gA01, uC]
        | succ k =>
          have hih := ih (0 + (k + 1)) (by omega) 0 (k + 1) rfl (by omega)
          have hd : d = (0 + (k + 1)) + 1 := by omega
          rw [hd, pow_succ]
          conv_lhs => unfold gCoeff; rw [ratCoeff]
          conv_rhs => rw [uC]
          simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, zero_sub]
          change -(gA01 L T 0 * gCoeff L T 0 0 (k + 1)) = _
          rw [hih]
          simp only [gA01, Complex.ofReal_zero, zero_mul, zero_add, add_zero, Complex.ofReal_one,
            one_mul]
          field_simp
    | succ j =>
      cases k with
      | zero =>
        cases j with
        | zero =>
          have hd : d = 1 := by omega
          subst hd
          simp [gCoeff, ratCoeff, gN10, gA10, uC]
          ring
        | succ j =>
          have hih := ih ((j + 1) + 0) (by omega) (j + 1) 0 rfl (by omega)
          have hd : d = ((j + 1) + 0) + 1 := by omega
          rw [hd, pow_succ]
          conv_lhs => unfold gCoeff; rw [ratCoeff]
          conv_rhs => rw [uC]
          simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, zero_sub]
          change -(gA10 L T 0 * gCoeff L T 0 (j + 1) 0) = _
          rw [hih]
          simp only [gA10, Complex.ofReal_zero, zero_mul, zero_add, add_zero, Complex.ofReal_one,
            one_mul]
          field_simp
      | succ k =>
        by_cases h00 : j = 0 ∧ k = 0
        · rcases h00 with ⟨rfl, rfl⟩
          have hd : d = 2 := by omega
          subst hd
          simp only [gCoeff, ratCoeff, uC, and_self, ↓reduceIte, gN11, gN10, gN01, gA10, gA01, gA11,
            Complex.ofReal_zero, zero_mul, zero_add, add_zero, sub_zero, Complex.ofReal_one,
            one_mul, mul_zero]
          field_simp
          ring
        · have hih1 := ih (j + (k + 1)) (by omega) j (k + 1) rfl (by omega)
          have hih2 := ih ((j + 1) + k) (by omega) (j + 1) k rfl (by omega)
          have hih3 := ih (j + k) (by omega) j k rfl (by omega)
          have hd1' : j + (k + 1) = j + k + 1 := by omega
          have hd2' : (j + 1) + k = j + k + 1 := by omega
          have hd : d = j + k + 2 := by omega
          rw [hd1'] at hih1
          rw [hd2'] at hih2
          rw [hd]
          conv_lhs => unfold gCoeff; rw [ratCoeff]
          conv_rhs => rw [uC]
          simp only [h00, ↓reduceIte, zero_sub]
          change -(gA10 L T 0 * gCoeff L T 0 j (k + 1))
              - gA01 L T 0 * gCoeff L T 0 (j + 1) k
              - gA11 L T 0 * gCoeff L T 0 j k = _
          rw [hih1, hih2, hih3]
          simp only [gA10, gA01, gA11, Complex.ofReal_zero, zero_mul, zero_add, add_zero, sub_zero,
            Complex.ofReal_one, one_mul]
          rw [← hDDc, show j + k + 2 = (j + k) + 2 from rfl,
            show j + k + 1 = (j + k) + 1 from rfl, pow_add, pow_add, pow_one]
          field_simp
          ring

lemma norm_gCoeff_zero {L T : ℝ} (hL : 0 < L) (j k : ℕ) (hjk : 1 ≤ j + k) :
    ‖gCoeff L T 0 j k‖ =
      ‖uC L T j k‖ / (Real.sqrt (L ^ 2 + T ^ 2)) ^ (j + k - 1) := by
  rw [gCoeff_zero_eq_uC hL j k hjk, norm_mul, norm_div, norm_pow]
  have hnorm_D : ‖(L : ℂ) + Complex.I * (T : ℂ)‖ = Real.sqrt (L ^ 2 + T ^ 2) := by
    have hsq : ‖(L : ℂ) + Complex.I * (T : ℂ)‖ ^ 2 = L ^ 2 + T ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp
      ring
    rw [← hsq, Real.sqrt_sq (norm_nonneg _)]
  have hnorm_Dc : ‖(L : ℂ) - Complex.I * (T : ℂ)‖ = Real.sqrt (L ^ 2 + T ^ 2) := by
    have hsq : ‖(L : ℂ) - Complex.I * (T : ℂ)‖ ^ 2 = L ^ 2 + T ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp
      ring
    rw [← hsq, Real.sqrt_sq (norm_nonneg _)]
  rw [hnorm_D, hnorm_Dc]
  have hsqrt_pos : 0 < Real.sqrt (L ^ 2 + T ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hpow : (Real.sqrt (L ^ 2 + T ^ 2)) ^ (j + k) =
      Real.sqrt (L ^ 2 + T ^ 2) * (Real.sqrt (L ^ 2 + T ^ 2)) ^ (j + k - 1) := by
    conv_lhs => rw [show j + k = (j + k - 1) + 1 by omega, pow_succ']
  rw [hpow]
  field_simp

lemma uC_swap (L T : ℝ) :
    ∀ j k : ℕ, uC L T k j = (-1 : ℂ) ^ (j + k) * uC L T j k := by
  suffices h : ∀ d j k : ℕ, j + k = d → uC L T k j = (-1 : ℂ) ^ d * uC L T j k by
    intro j k
    exact h (j + k) j k rfl
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro j k hjk
    cases j with
    | zero =>
      cases k with
      | zero => simp [uC]
      | succ k =>
        cases k with
        | zero =>
          have hd : d = 1 := by omega
          subst hd
          simp [uC]
        | succ k =>
          have hih := ih (0 + (k + 1)) (by omega) 0 (k + 1) rfl
          have hd : d = (0 + (k + 1)) + 1 := by omega
          rw [hd, pow_succ]
          conv_lhs => rw [uC]
          conv_rhs => rw [uC]
          simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte]
          rw [hih]
          ring
    | succ j =>
      cases k with
      | zero =>
        cases j with
        | zero =>
          have hd : d = 1 := by omega
          subst hd
          simp [uC]
        | succ j =>
          have hih := ih ((j + 1) + 0) (by omega) (j + 1) 0 rfl
          have hd : d = ((j + 1) + 0) + 1 := by omega
          rw [hd, pow_succ]
          conv_lhs => rw [uC]
          conv_rhs => rw [uC]
          simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte]
          rw [hih]
          ring
      | succ k =>
        by_cases h00 : j = 0 ∧ k = 0
        · rcases h00 with ⟨rfl, rfl⟩
          have hd : d = 2 := by omega
          subst hd
          simp [uC]
        · have h00' : ¬ (k = 0 ∧ j = 0) := fun ⟨hk, hj⟩ => h00 ⟨hj, hk⟩
          have hih1 := ih (j + (k + 1)) (by omega) j (k + 1) rfl
          have hih2 := ih ((j + 1) + k) (by omega) (j + 1) k rfl
          have hih3 := ih (j + k) (by omega) j k rfl
          have hd1 : j + (k + 1) = j + k + 1 := by omega
          have hd2 : (j + 1) + k = j + k + 1 := by omega
          have hd : d = j + k + 2 := by omega
          rw [hd1] at hih1
          rw [hd2] at hih2
          rw [hd]
          simp only [uC, h00, h00', ↓reduceIte]
          rw [hih1, hih2, hih3]
          rw [show j + k + 2 = (j + k) + 2 from rfl, show j + k + 1 = (j + k) + 1 from rfl,
            pow_add, pow_add]
          ring

lemma norm_uC_swap (L T : ℝ) (j k : ℕ) : ‖uC L T k j‖ = ‖uC L T j k‖ := by
  rw [uC_swap, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]

lemma continuousAt_gCoeff_zero {L T : ℝ} (hL : 0 < L) (j k : ℕ) :
    ContinuousAt (fun t => gCoeff L T t j k) 0 := by
  have hD : (L : ℂ) + Complex.I * (T : ℂ) ≠ 0 := denom_D_ne_zero hL
  have hden_cont : ContinuousAt (fun t : ℝ => (((1 + t : ℝ) : ℂ) * ((L : ℂ) + Complex.I * (T : ℂ)))) 0 :=
    ((Complex.continuous_ofReal.comp (continuous_const.add continuous_id)).mul continuous_const).continuousAt
  have hden_ne : (((1 + (0 : ℝ) : ℝ) : ℂ) * ((L : ℂ) + Complex.I * (T : ℂ))) ≠ 0 := by
    simpa using hD
  refine continuousAt_ratCoeff continuousAt_const
    (continuousAt_const.div hden_cont hden_ne)
    (continuousAt_const.div hden_cont hden_ne)
    (continuousAt_const.div hden_cont hden_ne)
    (((Complex.continuous_ofReal.mul continuous_const).add continuous_const).continuousAt.div hden_cont hden_ne)
    ((((Complex.continuous_ofReal.mul continuous_const).add continuous_const).neg).continuousAt.div hden_cont hden_ne)
    (((Complex.continuous_ofReal.comp (continuous_const.sub continuous_id)).mul continuous_const).continuousAt.div
      hden_cont hden_ne)
    j k

lemma continuousAt_finset_sum_aux {ι : Type*} (s : Finset ι) {f : ι → ℝ → ℝ} {x : ℝ}
    (hf : ∀ i ∈ s, ContinuousAt (f i) x) :
    ContinuousAt (fun t => ∑ i ∈ s, f i t) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using continuousAt_const
  | insert a s ha ih =>
    have hfa : ContinuousAt (f a) x := hf a (Finset.mem_insert_self a s)
    have hfs : ContinuousAt (fun t => ∑ i ∈ s, f i t) x :=
      ih fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hsum : (fun t => ∑ i ∈ insert a s, f i t) = fun t => f a t + ∑ i ∈ s, f i t := by
      ext t
      exact Finset.sum_insert ha
    rw [hsum]
    exact hfa.add hfs

lemma diag_sum_le_rect_sum (f : ℕ → ℕ → ℝ) (hf : ∀ j k, 0 ≤ f j k) (N : ℕ) :
    ∑ d ∈ Finset.Icc 1 N, ∑ j ∈ Finset.range (d + 1), f j (d - j) ≤
      ∑ j ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (N + 1), f j k := by
  rw [Finset.sum_sigma', ← Finset.sum_product']
  let S : Finset (ℕ × ℕ) :=
    (Finset.Icc 1 N).sigma (fun d => Finset.range (d + 1)) |>.image (fun p => (p.2, p.1 - p.2))
  have hinj : Set.InjOn (fun p : (d : ℕ) × ℕ => (p.2, p.1 - p.2))
      ((Finset.Icc 1 N).sigma (fun d => Finset.range (d + 1)) : Set ((d : ℕ) × ℕ)) := by
    intro a ha b hb hab
    simp only [Finset.mem_coe, Finset.mem_sigma, Finset.mem_Icc, Finset.mem_range] at ha hb
    simp only [Prod.mk.injEq] at hab
    have h1 : a.1 = b.1 := by omega
    cases a; cases b
    simp only at h1 hab
    subst h1
    congr 1
    exact hab.1
  have hsum_eq :
      ∑ x ∈ (Finset.Icc 1 N).sigma (fun d => Finset.range (d + 1)), f x.2 (x.1 - x.2) =
        ∑ p ∈ S, f p.1 p.2 := by
    rw [Finset.sum_image hinj]
  rw [hsum_eq]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun p _ _ => hf p.1 p.2)
  intro p hp
  simp only [S, Finset.mem_image, Finset.mem_sigma, Finset.mem_Icc, Finset.mem_range] at hp
  rcases hp with ⟨x, ⟨⟨_, hdN⟩, hj⟩, rfl⟩
  simp only [Finset.mem_product, Finset.mem_range]
  omega

theorem bohrRadius_lt_of_uC_diag_sum_gt_one
    {L T r : ℝ} (hL : 0 < L) (hT : 0 < T) (hr : 0 < r) (N : ℕ)
    (hgt : 1 < ∑ d ∈ Finset.Icc 1 N, ∑ j ∈ Finset.range (d + 1),
      ‖uC L T j (d - j)‖ / (Real.sqrt (L ^ 2 + T ^ 2)) ^ (d - 1) * r ^ d) :
    bohrRadius < r := by
  let F : ℝ → ℝ := fun t =>
    ∑ j ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (N + 1),
      ‖gCoeff L T t j k‖ * r ^ (j + k)
  have hF0_gt : 1 < F 0 := by
    refine lt_of_lt_of_le hgt ?_
    calc ∑ d ∈ Finset.Icc 1 N, ∑ j ∈ Finset.range (d + 1),
          ‖uC L T j (d - j)‖ / (Real.sqrt (L ^ 2 + T ^ 2)) ^ (d - 1) * r ^ d
        = ∑ d ∈ Finset.Icc 1 N, ∑ j ∈ Finset.range (d + 1),
            ‖gCoeff L T 0 j (d - j)‖ * r ^ (j + (d - j)) := by
          refine Finset.sum_congr rfl fun d hd => Finset.sum_congr rfl fun j hj => ?_
          simp only [Finset.mem_Icc, Finset.mem_range] at hd hj
          have hadd : j + (d - j) = d := by omega
          rw [norm_gCoeff_zero hL j (d - j) (by omega), hadd]
      _ ≤ F 0 := diag_sum_le_rect_sum (fun j k => ‖gCoeff L T 0 j k‖ * r ^ (j + k))
          (fun j k => by positivity) N
  have hF_cont : ContinuousAt F 0 := by
    refine continuousAt_finset_sum_aux _ fun j _ => continuousAt_finset_sum_aux _ fun k _ => ?_
    exact ((continuousAt_gCoeff_zero hL j k).norm).mul continuousAt_const
  have hev : ∀ᶠ t in nhds (0 : ℝ), 1 < F t :=
    hF_cont.eventually (isOpen_Ioi.mem_nhds hF0_gt)
  rw [Metric.eventually_nhds_iff] at hev
  rcases hev with ⟨δ, hδpos, hδ⟩
  let t : ℝ := min (1 / 2) (δ / 2)
  have ht0 : 0 < t := lt_min (by norm_num) (by linarith)
  have ht1 : t < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have ht_dist : dist t 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos ht0]
    exact lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hFt : 1 < F t := hδ ht_dist
  have hmaj : 1 < finiteMajorant (fCoeff L T t) r N := by
    rw [finiteMajorant_fCoeff ht0 ht1 N]
    have hcoeff_pos : 0 < (2 * t) / (1 + t) := by positivity
    have hmul : (2 * t) / (1 + t) * 1 < (2 * t) / (1 + t) * F t :=
      mul_lt_mul_of_pos_left hFt hcoeff_pos
    have hsum1 : (1 - t) / (1 + t) + (2 * t) / (1 + t) * 1 = 1 := by
      have : (1 + t : ℝ) ≠ 0 := by linarith
      field_simp
      ring
    linarith
  exact bohrRadius_lt_of_finiteMajorant_gt_one
    (fSchur L T (1 / t)) (fCoeff L T t) r N hr
    (isSchur_fSchur hL hT (by positivity))
    (hasBidiscCoefficients_fSchur hL hT ht0)
    hmaj

/-!
## 5. Pure-Kernel Integer Recurrence, Antidiagonal DP, and Certificate Soundness
-/

def uInt (L T : ℤ) : ℕ → ℕ → ℤ × ℤ
  | 0, 0 => (0, 0)
  | j + 1, 0 =>
      if j = 0 then (-1, 0)
      else let p := uInt L T j 0; (T * p.2, -T * p.1)
  | 0, k + 1 =>
      if k = 0 then (1, 0)
      else let p := uInt L T 0 k; (-T * p.2, T * p.1)
  | j + 1, k + 1 =>
      if j = 0 ∧ k = 0 then (2 * L, 0)
      else
        let a := uInt L T j (k + 1)
        let b := uInt L T (j + 1) k
        let c := uInt L T j k
        let M := L * L + T * T
        (T * a.2 - T * b.2 - M * c.1, -T * a.1 + T * b.1 - M * c.2)
termination_by j k => j + k

lemma uC_eq_uInt (L T : ℤ) :
    ∀ j k : ℕ, uC (L : ℝ) (T : ℝ) j k =
      ((uInt L T j k).1 : ℂ) + ((uInt L T j k).2 : ℂ) * Complex.I := by
  suffices h : ∀ d j k : ℕ, j + k = d →
      uC (L : ℝ) (T : ℝ) j k =
        ((uInt L T j k).1 : ℂ) + ((uInt L T j k).2 : ℂ) * Complex.I by
    intro j k
    exact h (j + k) j k rfl
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro j k hjk
    cases j with
    | zero =>
      cases k with
      | zero => simp [uC, uInt]
      | succ k =>
        cases k with
        | zero => simp [uC, uInt]
        | succ k =>
          have hih := ih (0 + (k + 1)) (by omega) 0 (k + 1) rfl
          conv_lhs => rw [uC]
          conv_rhs => rw [uInt]
          simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte]
          rw [hih]
          push_cast
          ring_nf
          rw [Complex.I_sq]
          ring
    | succ j =>
      cases k with
      | zero =>
        cases j with
        | zero => simp [uC, uInt]
        | succ j =>
          have hih := ih ((j + 1) + 0) (by omega) (j + 1) 0 rfl
          conv_lhs => rw [uC]
          conv_rhs => rw [uInt]
          simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte]
          rw [hih]
          push_cast
          ring_nf
          rw [Complex.I_sq]
          ring
      | succ k =>
        by_cases h00 : j = 0 ∧ k = 0
        · rcases h00 with ⟨rfl, rfl⟩
          simp [uC, uInt]
        · have hih1 := ih (j + (k + 1)) (by omega) j (k + 1) rfl
          have hih2 := ih ((j + 1) + k) (by omega) (j + 1) k rfl
          have hih3 := ih (j + k) (by omega) j k rfl
          conv_lhs => rw [uC]
          conv_rhs => rw [uInt]
          simp only [h00, ↓reduceIte]
          rw [hih1, hih2, hih3]
          push_cast
          ring_nf
          rw [Complex.I_sq]
          ring

lemma norm_uC_sq_eq_natAbs (L T : ℤ) (j k : ℕ) :
    ‖uC (L : ℝ) (T : ℝ) j k‖ ^ 2 =
      (((uInt L T j k).1.natAbs * (uInt L T j k).1.natAbs +
        (uInt L T j k).2.natAbs * (uInt L T j k).2.natAbs : ℕ) : ℝ) := by
  rw [uC_eq_uInt, Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.intCast_re, Complex.intCast_im, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, sub_zero, add_zero, zero_add]
  have hsq : ∀ z : ℤ, ((z.natAbs : ℕ) : ℝ) ^ 2 = (z : ℝ) ^ 2 := fun z => by
    cases z with
    | ofNat n => simp
    | negSucc n =>
      simp only [Int.natAbs_negSucc, Int.cast_negSucc, Nat.cast_succ]
      ring
  have h1 := hsq (uInt L T j k).1
  have h2 := hsq (uInt L T j k).2
  push_cast
  nlinarith

def stepZip (T M : ℤ) :
    List (ℤ × ℤ) → List (ℤ × ℤ) → List (ℤ × ℤ) → List (ℤ × ℤ)
  | a :: as, b :: bs, c :: cs =>
      (T * a.2 - T * b.2 - M * c.1, -T * a.1 + T * b.1 - M * c.2) :: stepZip T M as bs cs
  | _, _, _ => []

def nextDiag (T M : ℤ) (prev1 prev2 : List (ℤ × ℤ)) : List (ℤ × ℤ) :=
  stepZip T M ((0, 0) :: prev1) (prev1 ++ [(0, 0)]) ((0, 0) :: (prev2 ++ [(0, 0)]))

def checkRow (d j : ℕ) (denom S2 rn2_pow : ℕ) :
    List (ℤ × ℤ) → List ℕ → ℕ → Option ℕ
  | _, [], acc => some acc
  | [], _ :: _, _ => none
  | (ur, ui) :: us, b :: bs, acc =>
      if 2 * j > d then none
      else if b == 0 then
        checkRow d (j + 1) denom S2 rn2_pow us bs acc
      else
        let n2 := ur.natAbs * ur.natAbs + ui.natAbs * ui.natAbs
        if b * b * denom ≤ S2 * n2 * rn2_pow then
          let mult := if 2 * j == d then 1 else 2
          checkRow d (j + 1) denom S2 rn2_pow us bs (acc + mult * b)
        else none

def checkLoop (T M : ℤ) (M_nat rn2 rd2 S2 : ℕ) :
    ℕ → List (ℤ × ℤ) → List (ℤ × ℤ) → ℕ → ℕ → ℕ → List (List ℕ) → ℕ → Option ℕ
  | _, _, _, _, _, _, [], acc => some acc
  | d, prev1, prev2, M_pow, rn2_pow, rd2_pow, row :: rows, acc =>
      let cur := nextDiag T M prev1 prev2
      let M_pow' := M_pow * M_nat
      let rn2_pow' := rn2_pow * rn2
      let rd2_pow' := rd2_pow * rd2
      match checkRow d 0 (M_pow' * rd2_pow') S2 rn2_pow' cur row acc with
      | none => none
      | some acc' =>
          checkLoop T M M_nat rn2 rd2 S2 (d + 1) cur prev1 M_pow' rn2_pow' rd2_pow' rows acc'

def checkCert (L T r_num r_den scale : ℕ) (rows : List (List ℕ)) : Bool :=
  let M_nat := L * L + T * T
  let rn2 := r_num * r_num
  let rd2 := r_den * r_den
  let S2 := scale * scale
  let d1 : List (ℤ × ℤ) := [(1, 0), (-1, 0)]
  let d2 : List (ℤ × ℤ) := [(0, (T : ℤ)), ((2 * (L : ℤ)), 0), (0, (T : ℤ))]
  match rows with
  | row1 :: row2 :: rest =>
      match checkRow 1 0 rd2 S2 rn2 d1 row1 0 with
      | none => false
      | some acc1 =>
          match checkRow 2 0 (M_nat * (rd2 * rd2)) S2 (rn2 * rn2) d2 row2 acc1 with
          | none => false
          | some acc2 =>
              match checkLoop (T : ℤ) (M_nat : ℤ) M_nat rn2 rd2 S2 3 d2 d1
                  M_nat (rn2 * rn2) (rd2 * rd2) rest acc2 with
              | none => false
              | some total => scale < total
  | _ => false

lemma stepZip_length (T M : ℤ) :
    ∀ (as bs cs : List (ℤ × ℤ)),
      (stepZip T M as bs cs).length = min as.length (min bs.length cs.length)
  | [], _, _ => by simp [stepZip]
  | _ :: _, [], _ => by simp [stepZip]
  | _ :: _, _ :: _, [] => by simp [stepZip]
  | a :: as, b :: bs, c :: cs => by
      simp [stepZip, stepZip_length T M as bs cs]

lemma stepZip_getElem? (T M : ℤ) :
    ∀ (as bs cs : List (ℤ × ℤ)) (i : ℕ),
      (stepZip T M as bs cs)[i]? =
        match as[i]?, bs[i]?, cs[i]? with
        | some a, some b, some c =>
            some (T * a.2 - T * b.2 - M * c.1, -T * a.1 + T * b.1 - M * c.2)
        | _, _, _ => none
  | [], _, _, i => by simp [stepZip]
  | _ :: _, [], _, i => by simp [stepZip]
  | _ :: _, _ :: _, [], i => by simp [stepZip]
  | a :: as, b :: bs, c :: cs, 0 => by simp [stepZip]
  | a :: as, b :: bs, c :: cs, i + 1 => by
      simpa [stepZip] using stepZip_getElem? T M as bs cs i

def IsDiag (L T : ℤ) (d : ℕ) (l : List (ℤ × ℤ)) : Prop :=
  l.length = d + 1 ∧ ∀ j ≤ d, l[j]? = some (uInt L T j (d - j))

lemma isDiag_d1 (L T : ℤ) : IsDiag L T 1 [(1, 0), (-1, 0)] := by
  refine ⟨rfl, fun j hj => ?_⟩
  interval_cases j <;> simp [uInt]

lemma isDiag_d2 (L T : ℤ) :
    IsDiag L T 2 [(0, T), (2 * L, 0), (0, T)] := by
  refine ⟨rfl, fun j hj => ?_⟩
  interval_cases j <;> simp [uInt]

lemma isDiag_nextDiag (L T : ℤ) {d : ℕ} (hd : 3 ≤ d)
    {prev1 prev2 : List (ℤ × ℤ)}
    (h1 : IsDiag L T (d - 1) prev1)
    (h2 : IsDiag L T (d - 2) prev2) :
    IsDiag L T d (nextDiag T (L * L + T * T) prev1 prev2) := by
  let M : ℤ := L * L + T * T
  have hlen1 : prev1.length = d := by have := h1.1; omega
  have hlen2 : prev2.length = d - 1 := by have := h2.1; omega
  constructor
  · unfold nextDiag
    rw [stepZip_length]
    simp [hlen1, hlen2]
    omega
  · intro j hj
    unfold nextDiag
    rw [stepZip_getElem?]
    have ha : ((0, 0) :: prev1)[j]? =
        if j = 0 then some (0, 0) else some (uInt L T (j - 1) (d - j)) := by
      cases j with
      | zero => simp
      | succ j' =>
        simp only [Nat.succ_ne_zero, ↓reduceIte, List.getElem?_cons_succ, Nat.add_sub_cancel]
        have := h1.2 j' (by omega)
        rw [show d - 1 - j' = d - (j' + 1) by omega] at this
        exact this
    have hb : (prev1 ++ [(0, 0)])[j]? =
        if j = d then some (0, 0) else some (uInt L T j (d - 1 - j)) := by
      by_cases hjd : j = d
      · subst hjd
        rw [List.getElem?_append_right (by omega)]
        simp [hlen1]
      · rw [List.getElem?_append_left (by omega)]
        simp only [hjd, ↓reduceIte]
        exact h1.2 j (by omega)
    have hc : ((0, 0) :: (prev2 ++ [(0, 0)]))[j]? =
        if j = 0 ∨ j = d then some (0, 0) else some (uInt L T (j - 1) (d - 1 - j)) := by
      cases j with
      | zero => simp
      | succ j' =>
        simp only [Nat.succ_ne_zero, false_or, List.getElem?_cons_succ, Nat.add_sub_cancel]
        by_cases hjd : j' + 1 = d
        · rw [List.getElem?_append_right (by omega)]
          have hsub : j' - prev2.length = 0 := by omega
          simp [hjd, hsub]
        · rw [List.getElem?_append_left (by omega)]
          simp only [hjd, ↓reduceIte]
          have := h2.2 j' (by omega)
          rw [show d - 2 - j' = d - 1 - (j' + 1) by omega] at this
          exact this
    rw [ha, hb, hc]
    by_cases hj0 : j = 0
    · subst hj0
      have hd0 : d ≠ 0 := by omega
      simp only [↓reduceIte, hd0.symm, true_or, Nat.sub_zero]
      obtain ⟨k, rfl⟩ : ∃ k, d = k + 2 := ⟨d - 2, by omega⟩
      simp [uInt]
    · by_cases hjd : j = d
      · subst hjd
        simp only [hj0, ↓reduceIte, or_true, Nat.sub_self]
        obtain ⟨m, rfl⟩ : ∃ m, j = m + 2 := ⟨j - 2, by omega⟩
        simp [uInt]
      · simp only [hj0, hjd, or_self, ↓reduceIte]
        obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
        obtain ⟨k', hk'⟩ : ∃ k', d - (j' + 1) = k' + 1 := ⟨d - (j' + 1) - 1, by omega⟩
        have hnot00 : ¬ (j' = 0 ∧ k' = 0) := by omega
        have heq1 : d - 1 - (j' + 1) = k' := by omega
        rw [hk', heq1]
        simp only [Nat.add_sub_cancel]
        have hu : uInt L T (j' + 1) (k' + 1) =
            (T * (uInt L T j' (k' + 1)).2 - T * (uInt L T (j' + 1) k').2 - M * (uInt L T j' k').1,
             -T * (uInt L T j' (k' + 1)).1 + T * (uInt L T (j' + 1) k').1 - M * (uInt L T j' k').2) := by
          simp [uInt, hnot00, M]
        rw [hu]

lemma symm_diag_sum (d : ℕ) (f : ℕ → ℝ) (hsym : ∀ j ≤ d, f (d - j) = f j) :
    ∑ j ∈ Finset.range (d / 2 + 1), (if 2 * j = d then (1 : ℝ) else 2) * f j =
      ∑ j ∈ Finset.range (d + 1), f j := by
  rcases Nat.even_or_odd' d with ⟨m, rfl | rfl⟩
  · have hdiv : (2 * m) / 2 = m := by omega
    rw [hdiv]
    have h1 :
        ∑ j ∈ Finset.range (m + 1), (if 2 * j = 2 * m then (1 : ℝ) else 2) * f j =
          f m + 2 * ∑ j ∈ Finset.range m, f j := by
      rw [Finset.sum_range_succ, if_pos rfl, one_mul, Finset.mul_sum]
      have hcongr :
          ∑ j ∈ Finset.range m, (if 2 * j = 2 * m then (1 : ℝ) else 2) * f j =
            ∑ j ∈ Finset.range m, 2 * f j := by
        refine Finset.sum_congr rfl fun j hj => ?_
        simp only [Finset.mem_range] at hj
        rw [if_neg (by omega)]
      rw [hcongr, add_comm]
    have h2 :
        ∑ j ∈ Finset.range (2 * m + 1), f j =
          f m + 2 * ∑ j ∈ Finset.range m, f j := by
      rw [show 2 * m + 1 = (m + 1) + m by omega, Finset.sum_range_add, Finset.sum_range_succ]
      have hrefl : ∑ i ∈ Finset.range m, f (m + 1 + i) = ∑ i ∈ Finset.range m, f i := by
        rw [← Finset.sum_range_reflect f m]
        refine Finset.sum_congr rfl fun i hi => ?_
        simp only [Finset.mem_range] at hi
        have h := hsym (m - 1 - i) (by omega)
        rw [show 2 * m - (m - 1 - i) = m + 1 + i by omega] at h
        exact h
      rw [hrefl]
      ring
    rw [h1, h2]
  · have hdiv : (2 * m + 1) / 2 = m := by omega
    rw [hdiv]
    have h1 :
        ∑ j ∈ Finset.range (m + 1), (if 2 * j = 2 * m + 1 then (1 : ℝ) else 2) * f j =
          2 * ∑ j ∈ Finset.range (m + 1), f j := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j hj => ?_
      simp only [Finset.mem_range] at hj
      rw [if_neg (by omega)]
    have h2 :
        ∑ j ∈ Finset.range (2 * m + 1 + 1), f j =
          2 * ∑ j ∈ Finset.range (m + 1), f j := by
      rw [show 2 * m + 1 + 1 = (m + 1) + (m + 1) by omega, Finset.sum_range_add]
      have hrefl : ∑ i ∈ Finset.range (m + 1), f (m + 1 + i) = ∑ i ∈ Finset.range (m + 1), f i := by
        rw [← Finset.sum_range_reflect f (m + 1)]
        refine Finset.sum_congr rfl fun i hi => ?_
        simp only [Finset.mem_range] at hi
        have h := hsym (m + 1 - 1 - i) (by omega)
        rw [show 2 * m + 1 - (m + 1 - 1 - i) = m + 1 + i by omega] at h
        exact h
      rw [hrefl]
      ring
    rw [h1, h2]

noncomputable def diagTerm (L T : ℕ) (r : ℝ) (d j : ℕ) : ℝ :=
  ‖uC (L : ℝ) (T : ℝ) j (d - j)‖ /
    (Real.sqrt ((L : ℝ) ^ 2 + (T : ℝ) ^ 2)) ^ (d - 1) * r ^ d

lemma diagTerm_nonneg (L T : ℕ) {r : ℝ} (hr : 0 ≤ r) (d j : ℕ) :
    0 ≤ diagTerm L T r d j := by
  unfold diagTerm
  positivity

lemma checkRow_sound
    {L T r_num r_den scale d : ℕ}
    (hL : 0 < L) (hT : 0 < T) (hrd : 0 < r_den)
    (bs : List ℕ) :
    ∀ (j₀ : ℕ) (us : List (ℤ × ℤ)) (acc acc' : ℕ),
      (∀ m < us.length, j₀ + m ≤ d ∧ us[m]? = some (uInt L T (j₀ + m) (d - (j₀ + m)))) →
      checkRow d j₀ ((L * L + T * T) ^ (d - 1) * (r_den * r_den) ^ d)
        (scale * scale) ((r_num * r_num) ^ d) us bs acc = some acc' →
      (acc' : ℝ) ≤ (acc : ℝ) +
        (scale : ℝ) * ∑ j ∈ Finset.Ico j₀ (d / 2 + 1),
          (if 2 * j = d then (1 : ℝ) else 2) *
            diagTerm L T ((r_num : ℝ) / (r_den : ℝ)) d j := by
  let r : ℝ := (r_num : ℝ) / (r_den : ℝ)
  have hr : 0 ≤ r := by positivity
  induction bs with
  | nil =>
    intro j₀ us acc acc' _ hchk
    simp only [checkRow, Option.some.injEq] at hchk
    subst hchk
    have hnn : 0 ≤ (scale : ℝ) * ∑ j ∈ Finset.Ico j₀ (d / 2 + 1),
        (if 2 * j = d then (1 : ℝ) else 2) * diagTerm L T r d j := by
      refine mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg fun j _ => ?_)
      have hm : 0 ≤ (if 2 * j = d then (1 : ℝ) else 2) := by split_ifs <;> norm_num
      exact mul_nonneg hm (diagTerm_nonneg L T hr d j)
    linarith
  | cons b bs ih =>
    intro j₀ us acc acc' hus hchk
    cases us with
    | nil => simp [checkRow] at hchk
    | cons u us' =>
      rcases u with ⟨ur, ui⟩
      have hu0 : (ur, ui) = uInt L T j₀ (d - j₀) := by
        have h := hus 0 (by simp)
        simpa using h.2
      have hus' : ∀ m < us'.length,
          j₀ + 1 + m ≤ d ∧ us'[m]? = some (uInt L T (j₀ + 1 + m) (d - (j₀ + 1 + m))) := by
        intro m hm
        have h := hus (m + 1) (by simp; omega)
        rw [show j₀ + (m + 1) = j₀ + 1 + m by omega] at h
        simpa using h
      simp only [checkRow] at hchk
      by_cases hjgt : 2 * j₀ > d
      · simp [hjgt] at hchk
      · simp only [hjgt, ↓reduceIte] at hchk
        have hjle : j₀ ≤ d / 2 := by omega
        have hIco : Finset.Ico j₀ (d / 2 + 1) = insert j₀ (Finset.Ico (j₀ + 1) (d / 2 + 1)) := by
          ext x
          simp only [Finset.mem_Ico, Finset.mem_insert]
          omega
        have hnotmem : j₀ ∉ Finset.Ico (j₀ + 1) (d / 2 + 1) := by simp
        by_cases hb0 : (b == 0) = true
        · simp only [hb0] at hchk
          have hrec := ih (j₀ + 1) us' acc acc' hus' hchk
          rw [hIco, Finset.sum_insert hnotmem, mul_add]
          have hnn : 0 ≤ (scale : ℝ) * ((if 2 * j₀ = d then (1 : ℝ) else 2) * diagTerm L T r d j₀) := by
            have hm : 0 ≤ (if 2 * j₀ = d then (1 : ℝ) else 2) := by split_ifs <;> norm_num
            exact mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hm (diagTerm_nonneg L T hr d j₀))
          linarith
        · simp only [hb0] at hchk
          by_cases hle :
              b * b * ((L * L + T * T) ^ (d - 1) * (r_den * r_den) ^ d) ≤
                scale * scale * (ur.natAbs * ur.natAbs + ui.natAbs * ui.natAbs) *
                  (r_num * r_num) ^ d
          · simp only [hle, ↓reduceIte] at hchk
            have hrec := ih (j₀ + 1) us' (acc + (if (2 * j₀ == d) = true then 1 else 2) * b) acc' hus' hchk
            have hb_le : (b : ℝ) ≤ (scale : ℝ) * diagTerm L T r d j₀ := by
              have hcast :
                  ((b * b * ((L * L + T * T) ^ (d - 1) * (r_den * r_den) ^ d) : ℕ) : ℝ) ≤
                    ((scale * scale * (ur.natAbs * ur.natAbs + ui.natAbs * ui.natAbs) *
                      (r_num * r_num) ^ d : ℕ) : ℝ) := by
                exact_mod_cast hle
              have hn2 :
                  (((ur.natAbs * ur.natAbs + ui.natAbs * ui.natAbs : ℕ) : ℝ)) =
                    ‖uC (L : ℝ) (T : ℝ) j₀ (d - j₀)‖ ^ 2 := by
                have h := norm_uC_sq_eq_natAbs (L : ℤ) (T : ℤ) j₀ (d - j₀)
                rw [← hu0] at h
                simpa using h.symm
              have hMpos : 0 < (L : ℝ) ^ 2 + (T : ℝ) ^ 2 := by positivity
              have hrdpos : 0 < (r_den : ℝ) := by positivity
              have hsqrt_sq : (Real.sqrt ((L : ℝ) ^ 2 + (T : ℝ) ^ 2)) ^ 2 = (L : ℝ) ^ 2 + (T : ℝ) ^ 2 :=
                Real.sq_sqrt hMpos.le
              have hcast' :
                  (b : ℝ) ^ 2 * (((L : ℝ) ^ 2 + (T : ℝ) ^ 2) ^ (d - 1) * ((r_den : ℝ) ^ d) ^ 2) ≤
                    (scale : ℝ) ^ 2 * ‖uC (L : ℝ) (T : ℝ) j₀ (d - j₀)‖ ^ 2 * ((r_num : ℝ) ^ d) ^ 2 := by
                have h1 : (((L * L + T * T) ^ (d - 1) * (r_den * r_den) ^ d : ℕ) : ℝ) =
                    ((L : ℝ) ^ 2 + (T : ℝ) ^ 2) ^ (d - 1) * ((r_den : ℝ) ^ d) ^ 2 := by
                  push_cast
                  rw [show (L : ℝ) * L = (L : ℝ) ^ 2 by ring,
                    show (T : ℝ) * T = (T : ℝ) ^ 2 by ring,
                    show (r_den : ℝ) * r_den = (r_den : ℝ) ^ 2 by ring,
                    ← pow_mul, mul_comm 2 d, pow_mul]
                have h2 : (((r_num * r_num) ^ d : ℕ) : ℝ) = ((r_num : ℝ) ^ d) ^ 2 := by
                  push_cast
                  rw [show (r_num : ℝ) * r_num = (r_num : ℝ) ^ 2 by ring,
                    ← pow_mul, mul_comm 2 d, pow_mul]
                have hcast2 :
                    (b : ℝ) ^ 2 * (((L * L + T * T) ^ (d - 1) * (r_den * r_den) ^ d : ℕ) : ℝ) ≤
                      (scale : ℝ) ^ 2 *
                        (((ur.natAbs * ur.natAbs + ui.natAbs * ui.natAbs : ℕ) : ℝ)) *
                        (((r_num * r_num) ^ d : ℕ) : ℝ) := by
                  push_cast at hcast ⊢
                  nlinarith
                rw [h1, hn2, h2] at hcast2
                exact hcast2
              have hden_pos' : 0 < ((L : ℝ) ^ 2 + (T : ℝ) ^ 2) ^ (d - 1) * ((r_den : ℝ) ^ d) ^ 2 := by
                positivity
              have hrhs_eq :
                  ((scale : ℝ) * diagTerm L T r d j₀) ^ 2 =
                    ((scale : ℝ) ^ 2 * ‖uC (L : ℝ) (T : ℝ) j₀ (d - j₀)‖ ^ 2 * ((r_num : ℝ) ^ d) ^ 2) /
                      (((L : ℝ) ^ 2 + (T : ℝ) ^ 2) ^ (d - 1) * ((r_den : ℝ) ^ d) ^ 2) := by
                unfold diagTerm
                dsimp [r]
                rw [mul_pow, mul_pow, div_pow, div_pow, div_pow, ← pow_mul, mul_comm (d - 1) 2,
                  pow_mul, hsqrt_sq]
                ring
              have hsq : (b : ℝ) ^ 2 ≤ ((scale : ℝ) * diagTerm L T r d j₀) ^ 2 := by
                rw [hrhs_eq, le_div_iff₀ hden_pos']
                exact hcast'
              have hrhs_nn : 0 ≤ (scale : ℝ) * diagTerm L T r d j₀ :=
                mul_nonneg (Nat.cast_nonneg _) (diagTerm_nonneg L T hr d j₀)
              nlinarith
            have hmult_eq :
                (if (2 * j₀ == d) = true then (1 : ℝ) else 2) = (if 2 * j₀ = d then (1 : ℝ) else 2) := by
              by_cases h : 2 * j₀ = d <;> simp [h]
            have hmult_nn : 0 ≤ (if 2 * j₀ = d then (1 : ℝ) else 2) := by split_ifs <;> norm_num
            rw [hIco, Finset.sum_insert hnotmem, mul_add]
            push_cast at hrec
            rw [hmult_eq] at hrec
            have hmb : (if 2 * j₀ = d then (1 : ℝ) else 2) * (b : ℝ) ≤
                (scale : ℝ) * ((if 2 * j₀ = d then (1 : ℝ) else 2) * diagTerm L T r d j₀) := by
              have := mul_le_mul_of_nonneg_left hb_le hmult_nn
              linarith
            linarith
          · simp [hle] at hchk

lemma checkRow_diag_sound
    {L T r_num r_den scale d : ℕ}
    (hL : 0 < L) (hT : 0 < T) (hrd : 0 < r_den)
    {diag : List (ℤ × ℤ)} (hdiag : IsDiag L T d diag)
    (row : List ℕ) (acc acc' : ℕ)
    (hchk : checkRow d 0 ((L * L + T * T) ^ (d - 1) * (r_den * r_den) ^ d)
      (scale * scale) ((r_num * r_num) ^ d) diag row acc = some acc') :
    (acc' : ℝ) ≤ (acc : ℝ) +
      (scale : ℝ) * ∑ j ∈ Finset.range (d + 1),
        diagTerm L T ((r_num : ℝ) / (r_den : ℝ)) d j := by
  have hus : ∀ m < diag.length, 0 + m ≤ d ∧ diag[m]? = some (uInt L T (0 + m) (d - (0 + m))) := by
    intro m hm
    have hmle : m ≤ d := by have := hdiag.1; omega
    exact ⟨by omega, by simpa using hdiag.2 m hmle⟩
  have h := checkRow_sound hL hT hrd row 0 diag acc acc' hus hchk
  rw [Nat.Ico_zero_eq_range] at h
  have hsym : ∀ j ≤ d, diagTerm L T ((r_num : ℝ) / (r_den : ℝ)) d (d - j) =
      diagTerm L T ((r_num : ℝ) / (r_den : ℝ)) d j := by
    intro j hj
    unfold diagTerm
    rw [show d - (d - j) = j by omega, norm_uC_swap]
  rw [symm_diag_sum d _ hsym] at h
  exact h

lemma checkLoop_sound
    {L T r_num r_den scale : ℕ}
    (hL : 0 < L) (hT : 0 < T) (hrd : 0 < r_den)
    (rows : List (List ℕ)) :
    ∀ (d : ℕ) (prev1 prev2 : List (ℤ × ℤ)) (acc total : ℕ),
      3 ≤ d →
      IsDiag L T (d - 1) prev1 →
      IsDiag L T (d - 2) prev2 →
      checkLoop (T : ℤ) ((L * L + T * T : ℕ) : ℤ) (L * L + T * T)
        (r_num * r_num) (r_den * r_den) (scale * scale)
        d prev1 prev2
        ((L * L + T * T) ^ (d - 2)) ((r_num * r_num) ^ (d - 1)) ((r_den * r_den) ^ (d - 1))
        rows acc = some total →
      (total : ℝ) ≤ (acc : ℝ) +
        (scale : ℝ) * ∑ m ∈ Finset.Ico d (d + rows.length),
          ∑ j ∈ Finset.range (m + 1),
            diagTerm L T ((r_num : ℝ) / (r_den : ℝ)) m j := by
  induction rows with
  | nil =>
    intro d prev1 prev2 acc total _ _ _ hchk
    simp only [checkLoop, Option.some.injEq] at hchk
    subst hchk
    simp
  | cons row rows ih =>
    intro d prev1 prev2 acc total hd h1 h2 hchk
    simp only [checkLoop] at hchk
    have hMcast : ((L * L + T * T : ℕ) : ℤ) = (L : ℤ) * L + (T : ℤ) * T := by push_cast; rfl
    have hcur : IsDiag L T d (nextDiag (T : ℤ) ((L * L + T * T : ℕ) : ℤ) prev1 prev2) := by
      rw [hMcast]
      exact isDiag_nextDiag L T hd h1 h2
    have hMpow : (L * L + T * T) ^ (d - 2) * (L * L + T * T) = (L * L + T * T) ^ (d - 1) := by
      rw [← pow_succ, show d - 2 + 1 = d - 1 by omega]
    have hrnpow : (r_num * r_num) ^ (d - 1) * (r_num * r_num) = (r_num * r_num) ^ d := by
      rw [← pow_succ, show d - 1 + 1 = d by omega]
    have hrdpow : (r_den * r_den) ^ (d - 1) * (r_den * r_den) = (r_den * r_den) ^ d := by
      rw [← pow_succ, show d - 1 + 1 = d by omega]
    rw [hMpow, hrnpow, hrdpow] at hchk
    cases hrow : checkRow d 0 ((L * L + T * T) ^ (d - 1) * (r_den * r_den) ^ d)
        (scale * scale) ((r_num * r_num) ^ d)
        (nextDiag (T : ℤ) ((L * L + T * T : ℕ) : ℤ) prev1 prev2) row acc with
    | none => rw [hrow] at hchk; simp at hchk
    | some acc' =>
      rw [hrow] at hchk
      have hstep := checkRow_diag_sound hL hT hrd hcur row acc acc' hrow
      have h1' : IsDiag L T (d + 1 - 1) (nextDiag (T : ℤ) ((L * L + T * T : ℕ) : ℤ) prev1 prev2) := by
        simpa using hcur
      have h2' : IsDiag L T (d + 1 - 2) prev1 := by
        simpa [show d + 1 - 2 = d - 1 by omega] using h1
      have hchk' :
          checkLoop (T : ℤ) ((L * L + T * T : ℕ) : ℤ) (L * L + T * T)
            (r_num * r_num) (r_den * r_den) (scale * scale)
            (d + 1) (nextDiag (T : ℤ) ((L * L + T * T : ℕ) : ℤ) prev1 prev2) prev1
            ((L * L + T * T) ^ (d + 1 - 2)) ((r_num * r_num) ^ (d + 1 - 1))
            ((r_den * r_den) ^ (d + 1 - 1)) rows acc' = some total := by
        simpa [show d + 1 - 2 = d - 1 by omega] using hchk
      have hrec := ih (d + 1) _ prev1 acc' total (by omega) h1' h2' hchk'
      have hIco : Finset.Ico d (d + (row :: rows).length) =
          insert d (Finset.Ico (d + 1) (d + 1 + rows.length)) := by
        ext x
        simp only [List.length_cons, Finset.mem_Ico, Finset.mem_insert]
        omega
      have hnotmem : d ∉ Finset.Ico (d + 1) (d + 1 + rows.length) := by simp
      rw [hIco, Finset.sum_insert hnotmem, mul_add]
      linarith

theorem bohrRadius_lt_of_checkCert
    {L T r_num r_den scale : ℕ} {rows : List (List ℕ)}
    (hL : 0 < L) (hT : 0 < T) (hrn : 0 < r_num) (hrd : 0 < r_den) (hscale : 0 < scale)
    (hcert : checkCert L T r_num r_den scale rows = true) :
    bohrRadius < (r_num : ℝ) / (r_den : ℝ) := by
  cases rows with
  | nil => simp [checkCert] at hcert
  | cons row1 rest1 =>
    cases rest1 with
    | nil => simp [checkCert] at hcert
    | cons row2 rest =>
      simp only [checkCert] at hcert
      cases h1 : checkRow 1 0 (r_den * r_den) (scale * scale) (r_num * r_num)
          [(1, 0), (-1, 0)] row1 0 with
      | none => rw [h1] at hcert; simp at hcert
      | some acc1 =>
        rw [h1] at hcert
        dsimp only at hcert
        cases h2 : checkRow 2 0 ((L * L + T * T) * (r_den * r_den * (r_den * r_den)))
            (scale * scale) (r_num * r_num * (r_num * r_num))
            [(0, (T : ℤ)), (2 * (L : ℤ), 0), (0, (T : ℤ))] row2 acc1 with
        | none => rw [h2] at hcert; simp at hcert
        | some acc2 =>
          rw [h2] at hcert
          dsimp only at hcert
          cases hloop : checkLoop (T : ℤ) ((L * L + T * T : ℕ) : ℤ) (L * L + T * T)
              (r_num * r_num) (r_den * r_den) (scale * scale) 3
              [(0, (T : ℤ)), (2 * (L : ℤ), 0), (0, (T : ℤ))] [(1, 0), (-1, 0)]
              (L * L + T * T) (r_num * r_num * (r_num * r_num))
              (r_den * r_den * (r_den * r_den)) rest acc2 with
          | none => rw [hloop] at hcert; simp at hcert
          | some total =>
            rw [hloop] at hcert
            dsimp only at hcert
            have hlt_nat : scale < total := of_decide_eq_true hcert
            have hs1 : (acc1 : ℝ) ≤ (0 : ℝ) + (scale : ℝ) *
                ∑ j ∈ Finset.range 2, diagTerm L T ((r_num : ℝ) / (r_den : ℝ)) 1 j := by
              have h := checkRow_diag_sound (r_num := r_num) hL hT hrd (isDiag_d1 L T) row1 0 acc1
                (by simpa using h1)
              simpa using h
            have hs2 : (acc2 : ℝ) ≤ (acc1 : ℝ) + (scale : ℝ) *
                ∑ j ∈ Finset.range 3, diagTerm L T ((r_num : ℝ) / (r_den : ℝ)) 2 j := by
              exact checkRow_diag_sound hL hT hrd (isDiag_d2 L T) row2 acc1 acc2
                (by simpa [pow_two] using h2)
            have hs3 : (total : ℝ) ≤ (acc2 : ℝ) + (scale : ℝ) *
                ∑ m ∈ Finset.Ico 3 (3 + rest.length),
                  ∑ j ∈ Finset.range (m + 1), diagTerm L T ((r_num : ℝ) / (r_den : ℝ)) m j := by
              exact checkLoop_sound hL hT hrd rest 3 _ _ acc2 total le_rfl
                (isDiag_d2 L T) (isDiag_d1 L T) (by simpa [pow_two] using hloop)
            have hIcc : Finset.Icc 1 (rest.length + 2) =
                insert 1 (insert 2 (Finset.Ico 3 (3 + rest.length))) := by
              ext x
              simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ico]
              omega
            have htot_le : (total : ℝ) ≤ (scale : ℝ) *
                ∑ d ∈ Finset.Icc 1 (rest.length + 2),
                  ∑ j ∈ Finset.range (d + 1), diagTerm L T ((r_num : ℝ) / (r_den : ℝ)) d j := by
              rw [hIcc, Finset.sum_insert (by simp), Finset.sum_insert (by simp)]
              linarith
            have hscale_pos : (0 : ℝ) < (scale : ℝ) := by positivity
            have hlt_real : (scale : ℝ) < (total : ℝ) := by exact_mod_cast hlt_nat
            have hsum_gt : 1 < ∑ d ∈ Finset.Icc 1 (rest.length + 2),
                ∑ j ∈ Finset.range (d + 1), diagTerm L T ((r_num : ℝ) / (r_den : ℝ)) d j := by
              nlinarith
            exact bohrRadius_lt_of_uC_diag_sum_gt_one
              (by positivity : (0 : ℝ) < (L : ℝ))
              (by positivity : (0 : ℝ) < (T : ℝ))
              (by positivity : (0 : ℝ) < (r_num : ℝ) / (r_den : ℝ))
              (rest.length + 2)
              hsum_gt

/-!
## 6. Certified Witness Tables and World-Record Theorems (`C_59a`)

Both certificates are verified purely inside Lean 4's kernel (`decide`, ZERO `native_decide`,
ZERO `sorry`, ZERO extra axioms beyond `{propext, Classical.choice, Quot.sound}`).
-/

/-- Compact N = 44 integer lower-bound witness table (L = 10^9, T = 1226959270, scale = 10^21). -/
private def rows44 : List (List ℕ) :=
  [[302825279490987600000],
  [71084243397641460191, 115870583703469570252],
  [16686089311660373571, 29370808907138740087],
  [3916839558370323478, 8236572774604218972, 5627832381574735249],
  [919426465930143056, 2367099343119519219, 1509108144883814237],
  [215823245669147241, 672765183113367163, 452539248044028403, 469056730955186306],
  [50661662565958975, 187435589230779759, 141034566851758243, 138421456704824926],
  [11892157612538373, 51207934280343270, 45283530373015293, 39437745926260422, 36313709264817692],
  [2791527271678621, 13754621656868406, 14654940973642944, 11140006502342497, 9830797862492860],
  [655274237225834, 3642329041936069, 4680235707414446, 3108350091066497, 2868419994053753, 2893425237605051],
  [153816991267901, 953142515049397, 1460136924790200, 862881321541018, 871702048551380, 885448086983973],
  [36106511531530, 246957746352389, 444081438324035, 246533219148748, 270389576693218, 262456811701745, 255675413973701],
  [8475527730912, 63452018902533, 131869732980437, 75365811910226, 84176468848053, 76046700080939, 71249544285001],
  [1989518435053, 16186939370442, 38335863755379, 24629477468181, 25746057005617, 21743106781513, 20425273290624, 20282064145044],
  [467013232578, 4104070976482, 10940782084073, 8283955035556, 7613399317079, 6191505725812, 6088679076673, 6159789756692],
  [109625201536, 1035020950064, 3073005328577, 2771514105869, 2164338323286, 1798439588145, 1861505480633, 1869284456784, 1859097968992],
  [25733071299, 259811119275, 851303911466, 907750792127, 595207148421, 547528944507, 574565352897, 554770927735, 536950401808],
  [6040499349, 64950304720, 233022950252, 289836218384, 162099837551, 174403378633, 175624922118, 161652331232, 153876158541, 151985521116],
  [1417927613, 16177848369, 63119458976, 90281025714, 45751539643, 56321220201, 52244554268, 46616134176, 45123067648, 45093509429],
  [332839820, 4016485891, 16940601439, 27499107161, 13999935111, 17870663690, 15025595213, 13526438692, 13597127041, 13738250947, 13762885337],
  [78129761, 994264849, 4509805770, 8212227156, 4629371880, 5475835622, 4222395709, 4045863070, 4169206249, 4151209885, 4101073631],
  [18339931, 245477705, 1191903042, 2410385403, 1582847840, 1610107497, 1197241065, 1258552441, 1279328168, 1231634386, 1191755309, 1178719169],
  [4305057, 60462061, 312975275, 696825856, 539200586, 454408411, 357339186, 398805119, 385655099, 359747961, 346960838, 343450580],
  [1010555, 14859613, 81705063, 198777560, 179997358, 123911223, 113768484, 124769657, 112967934, 104545021, 103040380, 103456313, 103685709],
  [237214, 3644741, 21217878, 56038661, 58631477, 33265423, 37461839, 37731838, 32318504, 30841165, 31268546, 31491570, 31464888],
  [55682, 892343, 5483783, 15633445, 18648012, 9150487, 12268904, 10949436, 9264637, 9396947, 9593406, 9487113, 9327889, 9263968],
  [13070, 218105, 1411133, 4320678, 5804016, 2716751, 3905782, 3067425, 2760561, 2938068, 2923594, 2811230, 2727042, 2691112],
  [3068, 53226, 361681, 1184112, 1772094, 883964, 1197647, 849110, 867103, 917565, 871466, 822531, 802166, 797936, 797694],
  [720, 12970, 92362, 322056, 531983, 303091, 352878, 242538, 279883, 279104, 253328, 240994, 240335, 241840, 242553],
  [169, 3156, 23507, 86991, 157335, 104706, 99979, 74390, 89489, 81777, 72972, 72129, 73282, 73497, 73148, 72949],
  [39, 767, 5964, 23350, 45921, 35609, 27344, 24340, 27684, 23214, 21497, 22218, 22450, 22079, 21649, 21412],
  [9, 186, 1508, 6231, 13246, 11835, 7300, 8142, 8209, 6551, 6622, 6925, 6789, 6531, 6361, 6289, 6271],
  [2, 45, 380, 1654, 3780, 3842, 1955, 2687, 2334, 1916, 2105, 2127, 2006, 1915, 1885, 1884, 1887],
  [0, 10, 95, 437, 1068, 1220, 552, 860, 643, 597, 667, 632, 582, 566, 568, 572, 573, 573],
  [0, 2, 24, 114, 299, 380, 171, 265, 176, 194, 205, 182, 170, 171, 173, 173, 172, 171],
  [0, 0, 6, 30, 83, 116, 57, 78, 50, 63, 60, 51, 51, 53, 53, 52, 50, 50, 50],
  [0, 0, 1, 7, 23, 35, 20, 22, 15, 20, 17, 15, 16, 16, 15, 15, 15, 14, 14],
  [0, 0, 0, 2, 6, 10, 6, 6, 5, 6, 4, 4, 5, 4, 4, 4, 4, 4, 4, 4],
  [0, 0, 0, 0, 1, 3, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

/-- Sharp 21-digit N = 56 integer lower-bound witness table (L = 10^12, T = 1226959270039, scale = 10^26). -/
private def rows56 : List (List ℕ) :=
  [[30282527949098759482200000],
  [7108424339854328987715648, 11587058370125654374000855],
  [1668608931208375912304907, 2937080890681744895691179],
  [391683955851939978015211, 823657277455140318884010, 562783238155980419176407],
  [91942646597680132448305, 236709934311932341667877, 150910814485264905791543],
  [21582324568283775925556, 67276518311912187552494, 45253924802968592664050, 46905673094126872443510],
  [5066166256981537766556, 18743558923428836402994, 14103456684627802463685, 13842145670249853475015],
  [1189215761359448653688, 5120793428186878836720, 4528353037113825373555, 3943774592603319439904, 3631370926480969101328],
  [279152727196194523234, 1375462165743786515737, 1465494097308973663031, 1114000650237846743738, 983079786240905187490],
  [65527423730065462162, 364232904213036145606, 468023570727794886686, 310835009109652438710, 286841999398398303129, 289342523751599458972],
  [15381699128741597854, 95314251511182374345, 146013692476419216408, 86288132154611248183, 87170204852133994377, 88544808696042471632],
  [3610651153656970873, 24695774637159957997, 44408143832176612483, 24653321914449950931, 27038957668323186707, 26245681169825686319, 25567541397212936381],
  [847552773220248062, 6345201890825539654, 13186973298151741535, 7536581190626345792, 8417646884554065666, 7604670008082835796, 7124954428495040601],
  [198951843538186220, 1618693937210411856, 3833586375621182268, 2462947746628711403, 2574605700526650310, 2174310678163959634, 2042527329035716870, 2028206414461867964],
  [46701323266105406, 410407097695535171, 1094078208445972496, 828395503488447813, 761339931714444898, 619150572582768288, 608867907650137958, 615978975649663445],
  [10962520155721306, 103502095019697973, 307300532872784835, 277151410566992109, 216433832335513412, 179843958811280028, 186150548056574394, 186928445674095700, 185909796895984915],
  [2573307130503025, 25981111931227744, 85130391151943807, 90775079207629370, 59520714844979115, 54752894448176405, 57456535287873671, 55477092773073973, 53695040180807772],
  [604049935036311, 6495030473041517, 23302295026973389, 28983621837352788, 16209983755831861, 17440337862201800, 17562492211551192, 16165233123284868, 15387615854101811, 15198552111574866],
  [141792761420611, 1617784837218963, 6311945898217672, 9028102571213157, 4575153964281405, 5632122019854529, 5224455426876128, 4661613417708428, 4512306764772220, 4509350942793387],
  [33283982043758, 401648589232733, 1694060144134311, 2749910716126343, 1399993511005490, 1787066368958685, 1502559521431576, 1352643869192283, 1359712704106163, 1373825094699678, 1376288533689276],
  [7812976132138, 99426484966380, 450980577121186, 821222715648049, 462937188022894, 547583562228432, 422239570994211, 404586307083978, 416920624961180, 415120988530534, 410107363158228],
  [1833993179094, 24547770538249, 119190304224152, 241038540400432, 158284783985781, 161010749748185, 119724106532469, 125855244158852, 127932816848545, 123163438685123, 119175530966419, 117871916928154],
  [430505728429, 6046206183083, 31297527548457, 69682585653282, 53920058612250, 45440841170970, 35733918617680, 39880511962793, 38565509935039, 35974796104100, 34696083824427, 34345058085778],
  [101055546074, 1485961386975, 8170506379941, 19877756076458, 17999735843831, 12391122373327, 11376848476172, 12476965709869, 11296793425097, 10454502194472, 10304038010134, 10345631328194, 10368570957266],
  [23721457620, 364474194175, 2121787834290, 5603866182400, 5863147758642, 3326542371155, 3746183905861, 3773183874879, 3231850495945, 3084116547056, 3126854637244, 3149157018775, 3146488818718],
  [5568299549, 89234314662, 548378390230, 1563344524609, 1864801240313, 915048779600, 1226890472172, 1094943669765, 926463715417, 939694706990, 959340698843, 948711301681, 932788979139, 926396819268],
  [1307084934, 21810502381, 141113344360, 432067898602, 580401634670, 271675195084, 390578275683, 306742518933, 276056165317, 293806857537, 292359491660, 281123036205, 272704282045, 269111254142],
  [306820962, 5322600085, 36168144223, 118411237509, 177209404213, 88396446575, 119764778936, 84911014308, 86710314425, 91756508887, 87146613095, 82253190047, 80216679729, 79793691289, 79769429313],
  [72022177, 1297047971, 9236265108, 32205676088, 53198323136, 30309150479, 35287875280, 24253835714, 27988310067, 27910409373, 25332824727, 24099446843, 24033529522, 24184076350, 24255324352],
  [16906256, 315650649, 2350735479, 8699157213, 15733584020, 10470662518, 9997987352, 7439027610, 8948901352, 8177785257, 7297269790, 7212985146, 7328294453, 7349737595, 7314835668, 7294900888],
  [3968521, 76721248, 596430009, 2335036528, 4592144609, 3560984323, 2734485492, 2434090161, 2768478771, 2321494340, 2149786378, 2221800265, 2245000924, 2207981311, 2164944046, 2141270385],
  [931558, 18625970, 150890765, 623181799, 1324615599, 1183535116, 730026618, 814227128, 820966423, 655177979, 662250213, 692568503, 678994235, 653180939, 636183615, 628942398, 627158000],
  [218670, 4516988, 38071675, 165441687, 378080894, 384235863, 195550438, 268701445, 233450509, 191692013, 210532216, 212729766, 200626364, 191542682, 188593050, 188448112, 188738264],
  [51330, 1094297, 9582022, 43708388, 106894699, 122068965, 55236302, 86011095, 64340732, 59718811, 66745455, 63291195, 58234235, 56626698, 56897321, 57264470, 57366367, 57366883],
  [12049, 264852, 2406024, 11495673, 29963715, 38037698, 17165547, 26552968, 17667771, 19439406, 20541732, 18241553, 17003354, 17154588, 17398967, 17369735, 17220956, 17113160],
  [2828, 64044, 602831, 3010901, 8333766, 11651937, 5785000, 7896596, 5066333, 6347133, 6067438, 5198567, 5133744, 5310358, 5312077, 5202593, 5096123, 5033776, 5014508],
  [663, 15473, 150731, 785558, 2301372, 3515742, 2011272, 2263311, 1574026, 2018817, 1724524, 1520648, 1606929, 1642739, 1594194, 1536767, 1504215, 1492224, 1489305],
  [155, 3735, 37616, 204218, 631377, 1046666, 695839, 626318, 521792, 617328, 480616, 469211, 507567, 496526, 468247, 452227, 448876, 450016, 451250, 451659],
  [36, 901, 9370, 52911, 172176, 307892, 236078, 168200, 176266, 180827, 136526, 150699, 156951, 145464, 136427, 134974, 136186, 136879, 136801, 136556],
  [8, 217, 2330, 13665, 46691, 89602, 78279, 44480, 58664, 50868, 41237, 48507, 46753, 41798, 40490, 41267, 41683, 41421, 40936, 40566, 40436],
  [2, 52, 578, 3519, 12597, 25824, 25389, 11989, 18953, 13893, 13291, 15189, 13425, 12151, 12446, 12776, 12663, 12367, 12120, 11981, 11925],
  [0, 12, 143, 903, 3382, 7377, 8071, 3474, 5917, 3784, 4400, 4564, 3787, 3688, 3908, 3912, 3772, 3650, 3592, 3577, 3577, 3578],
  [0, 3, 35, 231, 904, 2090, 2521, 1113, 1783, 1078, 1439, 1314, 1090, 1167, 1216, 1166, 1105, 1079, 1078, 1083, 1086, 1087],
  [0, 0, 8, 59, 240, 588, 775, 382, 519, 334, 455, 366, 332, 373, 367, 338, 324, 325, 328, 329, 328, 326, 326],
  [0, 0, 2, 15, 63, 164, 235, 133, 146, 111, 138, 101, 106, 116, 106, 98, 97, 100, 100, 99, 98, 97, 96],
  [0, 0, 0, 3, 16, 45, 70, 46, 39, 37, 40, 29, 34, 34, 30, 29, 30, 30, 30, 29, 29, 28, 28, 28],
  [0, 0, 0, 0, 4, 12, 20, 15, 10, 12, 11, 9, 11, 10, 8, 9, 9, 9, 8, 8, 8, 8, 8, 8],
  [0, 0, 0, 0, 1, 3, 6, 5, 2, 4, 3, 2, 3, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2],
  [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

set_option maxRecDepth 100000 in
private theorem checkCert_44 :
    checkCert (10 ^ 9) 1226959270 3028252794909876 (10 ^ 16) (10 ^ 21) rows44 = true := by
  decide

set_option maxRecDepth 100000 in
private theorem checkCert_56 :
    checkCert (10 ^ 12) 1226959270039 302825279490987594822 (10 ^ 21) (10 ^ 26) rows56 = true := by
  decide

/-- Compact N = 44 world-record upper bound on the bidisc Bohr radius `K_2`:
`K_2 < 3028252794909876 / 10 ^ 16 = 0.3028252794909876`, strictly improving both
`[P2026]` (`0.302825279492`) and unformalized `[T2026]` (`0.302825279490988`). -/
theorem bohrRadius_lt_3028252794909876_div_10pow16 :
    bohrRadius < (3028252794909876 : ℝ) / 10 ^ 16 := by
  have h := bohrRadius_lt_of_checkCert
    (by decide : 0 < 10 ^ 9)
    (by decide : 0 < 1226959270)
    (by decide : 0 < 3028252794909876)
    (by decide : 0 < 10 ^ 16)
    (by decide : 0 < 10 ^ 21)
    checkCert_44
  convert h using 1
  norm_num

/-- Sharp 21-digit N = 56 world-record upper bound on the bidisc Bohr radius `K_2`:
`K_2 < 302825279490987594822 / 10 ^ 21 = 0.302825279490987594822`, strictly improving
unformalized `[T2026]` (`0.302825279490988`) by `4.05178 × 10⁻¹⁶`. -/
theorem bohrRadius_lt_302825279490987594822_div_10pow21 :
    bohrRadius < (302825279490987594822 : ℝ) / 10 ^ 21 := by
  have h := bohrRadius_lt_of_checkCert
    (by decide : 0 < 10 ^ 12)
    (by decide : 0 < 1226959270039)
    (by decide : 0 < 302825279490987594822)
    (by decide : 0 < 10 ^ 21)
    (by decide : 0 < 10 ^ 26)
    checkCert_56
  convert h using 1
  norm_num

end Optim.BohrRadius
