/-
Copyright (c) 2025 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä, ...
-/
import ExtremeValueProject.CumulativeDistributionFunction
import Mathlib.MeasureTheory.Measure.DiracProba



section degenerate_cdf

open MeasureTheory Topology Filter Set ENNReal NNReal

namespace CumulativeDistributionFunction

/-- A c.d.f. F is degenerate if its only possible values are 0 or 1. -/
def IsDegenerate (F : CumulativeDistributionFunction) : Prop :=
  ∀ x, F x = 0 ∨ F x = 1

lemma isDegenerate_def (F : CumulativeDistributionFunction) :
    F.IsDegenerate ↔ ∀ x, F x = 0 ∨ F x = 1 := by rfl

/-- A c.d.f. F is degenerate if and only if it jumps from 0 to 1 at some point x₀. -/
lemma isDegenerate_iff (F : CumulativeDistributionFunction) :
    F.IsDegenerate ↔ ∃ x₀, F.toFun = (Set.Ici x₀).indicator (fun _ ↦ 1) := by
  sorry

-- TODO: This probably belongs to Mathlib?
lemma _root_.MeasureTheory.diracProba_apply' {X : Type*} [MeasurableSpace X] (x₀ : X)
    {s : Set X} (s_mble : MeasurableSet s) :
    (diracProba x₀) s = s.indicator 1 x₀ := by
  sorry

-- TODO: This probably also belongs to Mathlib? (Note slightly different hypotheses to the above.)
lemma _root_.MeasureTheory.diracProba_apply {X : Type*} [MeasurableSpace X]
    [MeasurableSingletonClass X] (x₀ : X) (s : Set X) :
    (diracProba x₀) s = s.indicator 1 x₀ := by
  sorry

lemma cdf_diracProba_apply (x₀ x : ℝ) :
    (diracProba x₀).cdf x = if x < x₀ then 0 else 1 := by
  -- `MeasureTheory.diracProba_apply` or ``MeasureTheory.diracProba_apply'`` should be the keys
  sorry

/-- The c.d.f. of Dirac delta mass at a point x₀ is degenerate. -/
lemma diracProba_is_degenerate (x₀ : ℝ) :
    IsDegenerate (diracProba x₀).cdf := by
  rw [isDegenerate_iff]
  use x₀
  ext x
  simp [cdf_diracProba_apply, indicator]
  by_cases hx : x < x₀
  · have aux : ¬ (x₀ ≤ x) := by exact not_le_of_lt hx
    simp [hx, aux]
  · have aux : x₀ ≤ x := by exact le_of_not_lt hx
    simp [hx, aux]

/-- If the c.d.f. of a probability measure μ on ℝ is degenerate, then μ is the Dirac delta mass
at some point x₀. -/
lemma eq_diracProba_of_isDegenerate (μ : ProbabilityMeasure ℝ) (degen : μ.cdf.IsDegenerate) :
    ∃ x₀, μ = diracProba x₀ := by
  sorry

end CumulativeDistributionFunction

end degenerate_cdf
