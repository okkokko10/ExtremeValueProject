/-
Copyright (c) 2025 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä, ...
-/
import ExtremeValueProject.PseudoInverses
import ExtremeValueProject.AffineTransformation

section extend_cdf

namespace CumulativeDistributionFunction

/-- The natural extension of a c.d.f. to a function `[-∞,+∞] → [0,+∞]`. -/
noncomputable def extend (F : CumulativeDistributionFunction) (x : EReal) :
    ENNReal := match x with
  | ⊥ => 0
  | ⊤ => 1
  | some (some ξ) => ENNReal.ofReal (F ξ)

@[simp] lemma extend_bot (F : CumulativeDistributionFunction) :
    F.extend ⊥ = 0 :=
  rfl

@[simp] lemma extend_top (F : CumulativeDistributionFunction) :
    F.extend ⊤ = 1 :=
  rfl

@[simp] lemma extend_ofReal (F : CumulativeDistributionFunction)
    (x : ℝ) :
    F.extend x = ENNReal.ofReal (F x) :=
  rfl

lemma extend_nonneg (F : CumulativeDistributionFunction) :
    0 ≤ F.extend := by
  intro x
  match x with
  | ⊥ => simp
  | ⊤ => simp
  | some (some ξ) =>
    change 0 ≤ F.extend ξ
    have : 0 ≤ F ξ := apply_nonneg F ξ
    simp_all

lemma extend_le_one (F : CumulativeDistributionFunction) :
    F.extend ≤ 1 := by
  intro x
  match x with
  | ⊥ => simp
  | ⊤ => simp
  | some (some ξ) =>
    change F.extend ξ ≤ 1
    simpa using apply_le_one F ξ

lemma extend_mono (F : CumulativeDistributionFunction) :
    Monotone F.extend := by
  intro x y hxy
  match x with
  | ⊥ => simp
  | ⊤ => simp [eq_top_iff.mpr hxy]
  | some (some ξ) => match y with
    | ⊥ => simp at hxy -- contradiction
    | ⊤ => simpa using extend_le_one _ _
    | some (some η) =>
      have ξ_le_η : ξ ≤ η := EReal.coe_le_coe_iff.mp hxy
      exact ENNReal.ofReal_le_ofReal (F.mono ξ_le_η)

lemma extend_affine (F : CumulativeDistributionFunction)
    (A : orientationPreservingAffineEquiv) :
    (A • F).extend = F.extend ∘ (A⁻¹ : ℝ ≃ᵃ[ℝ] ℝ).extend := by
  ext x
  simp [extend]
  match x with
  | ⊥ =>
    simp [show 0 < (A⁻¹ : ℝ ≃ᵃ[ℝ] ℝ).toAffineMap.coefs_of_field.1 from Subgroup.inv_mem _ A.prop]
  | ⊤ =>
    simp [show 0 < (A⁻¹ : ℝ ≃ᵃ[ℝ] ℝ).toAffineMap.coefs_of_field.1 from Subgroup.inv_mem _ A.prop]
  | some (some ξ) =>
    change (A • F).extend ξ = F.extend ((A⁻¹ : ℝ ≃ᵃ[ℝ] ℝ).extend ξ)
    simp [extend_ofReal]

lemma extend_continuousAt_bot (F : CumulativeDistributionFunction) :
    ContinuousAt F.extend ⊥ := by
  sorry

lemma extend_continuousAt_top (F : CumulativeDistributionFunction) :
    ContinuousAt F.extend ⊤ := by
  sorry

lemma extend_continuousAt (F : CumulativeDistributionFunction) {x : ℝ}
    (hx : ContinuousAt F x) :
    ContinuousAt F.extend x := by
  sorry

open MeasureTheory

/-- If `F` is the c.d.f. of a probability measure `μ`, then `F x = μ (-∞, x]` for all `x ∈ ℝ`.
The natural analogue of this holds for the extension `F⁺` of `F` to `[-∞,+∞]`: we have
`F⁺ x = μ⁺ [-∞, x]` for all `x ∈ [-∞,+∞]`, where `μ⁺` is the push-forward measure of
`μ` along the inclusion `ℝ ↪ [-∞,+∞]`. -/
lemma extend_apply_eq_map_measure_Iic (F : CumulativeDistributionFunction) (x : EReal) :
    F.extend x = F.measure.map ((↑) : ℝ → EReal) (Set.Iic x) := by
  match x with
  | ⊥ =>
    rw [Measure.map_apply measurable_coe_real_ereal measurableSet_Iic]
    convert show 0 = F.measure ∅ by simp
    ext x
    simp
  | ⊤ =>
    rw [Measure.map_apply measurable_coe_real_ereal measurableSet_Iic]
    simp
  | some (some ξ) =>
    change F.extend ξ = F.measure.map ((↑) : ℝ → EReal) (Set.Iic ξ)
    have aux : F.measure.map ((↑) : ℝ → EReal) (Set.Iic ξ) = F.measure (Set.Iic ξ) := by
      simp [Measure.map_apply measurable_coe_real_ereal measurableSet_Iic]
    rw [aux, extend_ofReal, ← ENNReal.ofReal_toReal (measure_ne_top F.measure _)]
    congr
    exact F.apply_eq_measure_Iic ξ

end CumulativeDistributionFunction

end extend_cdf

noncomputable section transform_cdf
/-!
# Transformed cumulative distribution functions
-/

open Set ENNReal NNReal

def transformAux (p : ℝ≥0∞) := (1 : ℝ≥0∞) / (1 - p)

@[simp] lemma transformAux_zero :
    transformAux 0 = 1 := by
  simp [transformAux]

lemma transformAux_of_ge_one {p : ℝ≥0∞} (hp : 1 ≤ p) :
    transformAux p = ∞ := by
  simp only [transformAux, one_div, inv_eq_top, tsub_eq_zero_of_le hp]

@[simp] lemma transformAux_one :
    transformAux 1 = ∞ :=
  transformAux_of_ge_one (le_refl 1)

lemma transformAux_mono :
    Monotone transformAux := by
  intro p q hpq
  simp only [transformAux, one_div, ENNReal.inv_le_inv]
  exact tsub_le_tsub_left hpq 1

lemma transformAux_strictMonoOn :
    StrictMonoOn transformAux (Iic 1) := by
  intro p hp q hq hpq
  simp only [transformAux, one_div, ENNReal.inv_lt_inv]
  apply ENNReal.sub_lt_of_sub_lt hq (by left ; exact one_ne_top)
  convert hpq
  refine ENNReal.sub_sub_cancel one_ne_top hp

namespace CumulativeDistributionFunction

/-- An auxiliary transform of a cumulative distribution function `F` to a function
`[-∞,+∞] → [0,+∞]` by the formula `x ↦ 1 / (1 - F(x))`. -/
def oneDivOneSub (F : CumulativeDistributionFunction) :
    EReal → ℝ≥0∞ :=
  transformAux ∘ F.extend

lemma oneDivOneSub_apply (F : CumulativeDistributionFunction) (x : EReal) :
    F.oneDivOneSub x = 1 / (1 - F.extend x) :=
  rfl

@[simp] lemma oneDivOneSub_apply_bot (F : CumulativeDistributionFunction) :
    F.oneDivOneSub ⊥ = 1 := by
  simp [oneDivOneSub]

@[simp] lemma oneDivOneSub_apply_top (F : CumulativeDistributionFunction) (x : EReal) :
    F.oneDivOneSub x = 1 / (1 - F.extend x) :=
  rfl

@[simp] lemma oneDivOneSub_apply_ofReal (F : CumulativeDistributionFunction) (x : ℝ) :
    F.oneDivOneSub x = 1 / (1 - ENNReal.ofReal (F x)) :=
  rfl

lemma oneDivOneSub_continuousAt_bot (F : CumulativeDistributionFunction) :
    ContinuousAt F.oneDivOneSub ⊥ := by
  sorry

lemma oneDivOneSub_continuousAt_top (F : CumulativeDistributionFunction) :
    ContinuousAt F.oneDivOneSub ⊤ := by
  sorry

lemma oneDivOneSub_continuousAt (F : CumulativeDistributionFunction) {x : ℝ}
    (hx : ContinuousAt F x) :
    ContinuousAt F.oneDivOneSub x := by
  sorry

lemma oneDivOneSub_affine (F : CumulativeDistributionFunction)
    (A : orientationPreservingAffineEquiv) :
    ((A • F).oneDivOneSub) = F.oneDivOneSub ∘ (A⁻¹ : ℝ ≃ᵃ[ℝ] ℝ).extend := by
  ext x
  simp [oneDivOneSub, extend_affine]

/-- A transform of a cumulative distribution function `F` to a function
`[0,+∞] → [-∞,+∞]`: the left-continuous inverse of the function `x ↦ 1 / (1 - F(x))`. -/
def rcInvOneDivOneSub (F : CumulativeDistributionFunction) :
    ℝ≥0∞ → EReal :=
  rcInv (F.oneDivOneSub)

lemma rcInvOneDivOneSub_continuousAt_bot (F : CumulativeDistributionFunction) :
    ContinuousAt F.rcInvOneDivOneSub ⊥ := by
  sorry

lemma rcInvOneDivOneSub_continuousAt_top (F : CumulativeDistributionFunction) :
    ContinuousAt F.rcInvOneDivOneSub ⊤ := by
  sorry

-- TODO: What is the good statement about continuity of F.rcInvOneDivOneSub at `u ∈ (1,+∞)`?
-- The hypothesis should be continuity and local increase of `F` at `F⁻¹ (1 - 1/u)`?

lemma rcInvOneDivOneSub_affine (F : CumulativeDistributionFunction)
    (A : orientationPreservingAffineEquiv) :
    ((A • F).rcInvOneDivOneSub) = (A : ℝ ≃ᵃ[ℝ] ℝ).extend ∘ F.rcInvOneDivOneSub := by
  rw [rcInvOneDivOneSub, oneDivOneSub_affine]
  apply rcInv_comp F.oneDivOneSub (A⁻¹ : AffineEquiv _ _ _).extend ?_
  exact AffineMap.leftOrdContinuous_extend _

end CumulativeDistributionFunction



end transform_cdf
