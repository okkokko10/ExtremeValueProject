/-
Copyright (c) 2025 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä, ...
-/
import ExtremeValueProject.CumulativeDistributionFunction
import ExtremeValueProject.AffineTransformation
import Mathlib

section weak_convergence_cdf

open Filter Topology NNReal ENNReal Set

/-- Lemma 4.3 (cdf-tight) in blueprint. -/
lemma CumulativeDistributionFunction.forall_pos_exists_lt_gt_continuousAt
    (F : CumulativeDistributionFunction) {ε : ℝ} (ε_pos : 0 < ε) :
    ∃ (a b : ℝ), a < b ∧ F a < ε ∧ 1 - ε < F b ∧ ContinuousAt F a ∧ ContinuousAt F b := by
  sorry -- **Issue #16**

/-- Lemma 4.4 (subdivision-dense) in blueprint:
An interval `[a,b]` can be subdivided with points from a dense set so that the consecutive
differences are smaller than a given `δ > 0`. -/
lemma forall_exists_subdivision_diff_lt_of_dense {D : Set ℝ} (D_dense : Dense D)
    {a b : ℝ} (ha : a ∈ D) (hb : b ∈ D) (a_lt_b : a < b) {δ : ℝ} (δ_pos : 0 < δ) :
    ∃ (k : ℕ) (cs : Fin (k + 1) → ℝ),
      (cs 0 = a) ∧ (cs (Fin.last _) = b) ∧ (Monotone cs) ∧ (∀ k, cs k ∈ D) ∧
      (∀ (j : Fin k), cs j.succ - cs j < δ) := by
  sorry -- **Issue #22**

/-- Lemma 4.5 (continuous-function-approximation-subdivision) in blueprint:
An interval `[a,b]` can be subdivided with points from a dense set so that for a given
continuous function `f` the function values on the parts of the subdivision are smaller than
a given `ε > 0`. -/
lemma forall_exists_subdivision_dist_apply_lt_of_dense_of_continuous {D : Set ℝ} (D_dense : Dense D)
    {f : ℝ → ℝ} (f_cont : Continuous f) {a b : ℝ} (ha : a ∈ D) (hb : b ∈ D) (a_lt_b : a < b)
    {ε : ℝ} (ε_pos : 0 < ε) :
    ∃ (k : ℕ) (cs : Fin (k + 1) → ℝ),
      (cs 0 = a) ∧ (cs (Fin.last _) = b) ∧ (Monotone cs) ∧ (∀ k, cs k ∈ D) ∧
      (∀ (j : Fin k), ∀ x ∈ Icc (cs j) (cs j.succ), ∀ y ∈ Icc (cs j) (cs j.succ),
        dist (f x) (f y) < ε) := by
  sorry -- **Issue #17**

/-- Preliminary to Lemma 4.6 (simple-integral-cdf-difference) in blueprint. -/
lemma CumulativeDistributionFunction.integral_indicator_eq (F : CumulativeDistributionFunction)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {κ : Type*} {s : Finset κ} {a b : ℝ} (a_le_b : a ≤ b) (α : E) :
    ∫ x, (indicator (Ioc a b) (fun _ ↦ α)) x ∂ F.measure =
      (F b - F a) • α := by
  sorry -- **Issue #19**

/-- Lemma 4.6 (simple-integral-cdf-difference) in blueprint. -/
lemma CumulativeDistributionFunction.integral_sum_indicator_eq (F : CumulativeDistributionFunction)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {κ : Type*} {s : Finset κ} (as : κ → ℝ) (bs : κ → ℝ) (h : ∀ j, as j ≤ bs j) (α : κ → E) :
    ∫ x, ((∑ j ∈ s, indicator (Ioc (as j) (bs j)) (fun _ ↦ α j)) x) ∂ F.measure =
      ∑ j in s, (F (bs j) - F (as j)) • α j := by
  -- It may be worthwhile to think about an improved phrasing of this.
  -- The previous lemma `CumulativeDistributionFunction.integral_indicator_eq` should be
  -- the key anyway.
  sorry -- **Issue #18**

open MeasureTheory Topology

/-- Theorem 4.8 (convergence-in-distribution-with-cdf) in blueprint:
Convergence of a sequence of c.d.f.s pointwise at all continuity points of the limit c.d.f. imply
convergence in distribution of the corresponding Borel probability measures on `ℝ`. -/
theorem tendsto_of_forall_continuousAt_tendsto_cdf
    (μs : ℕ → ProbabilityMeasure ℝ) (μ : ProbabilityMeasure ℝ)
    (h : ∀ x, ContinuousAt μ.cdf x → Tendsto (fun n ↦ (μs n).cdf x) atTop (𝓝 (μ.cdf x))) :
    Tendsto μs atTop (𝓝 μ) := by
  sorry -- **Issue #20** (a big one)

end weak_convergence_cdf



section levy_prokhorov_metric

open MeasureTheory Filter Topology

variable (F G :CumulativeDistributionFunction)

namespace CumulativeDistributionFunction

lemma tendsto_probabilityMeasure_iff_forall_continuousAt_tendsto
    (Fs : ℕ → CumulativeDistributionFunction) (G : CumulativeDistributionFunction) :
    Tendsto (fun i ↦ (Fs i).probabilityMeasure) atTop (𝓝 G.probabilityMeasure)
      ↔ ∀ x, ContinuousAt G x → Tendsto (fun i ↦ Fs i x) atTop (𝓝 (G x)) := by
  constructor
  · intro h x hGx
    have key := @tendsto_apply_of_tendsto_of_continuousAt ℕ atTop
                (fun i ↦ (Fs i).probabilityMeasure) G.probabilityMeasure h x
    simp_all
  · intro h
    apply tendsto_of_forall_continuousAt_tendsto_cdf
    simpa using h

noncomputable def equiv_levyProkhorov :
    CumulativeDistributionFunction ≃ LevyProkhorov (ProbabilityMeasure ℝ) :=
  equiv_probabilityMeasure.trans (LevyProkhorov.equiv (ProbabilityMeasure ℝ)).symm

noncomputable instance : MetricSpace CumulativeDistributionFunction := by
  apply MetricSpace.induced equiv_levyProkhorov
  · intro F G h
    simpa only [EmbeddingLike.apply_eq_iff_eq] using h
  · exact levyProkhorovDist_metricSpace_probabilityMeasure

noncomputable def homeomorph_levyProkhorov :
    CumulativeDistributionFunction ≃ₜ LevyProkhorov (ProbabilityMeasure ℝ) :=
  Equiv.toHomeomorphOfIsInducing equiv_levyProkhorov ⟨rfl⟩

noncomputable def homeomorph_probabilityMeasure :
    CumulativeDistributionFunction ≃ₜ ProbabilityMeasure ℝ :=
  homeomorph_levyProkhorov.trans homeomorph_probabilityMeasure_levyProkhorov.symm

lemma homeomorph_probabilityMeasure_apply_eq (F : CumulativeDistributionFunction) :
    homeomorph_probabilityMeasure F = F.probabilityMeasure :=
  rfl

/-- The standard characterization of convergence of cumulative distribution functions. -/
lemma tendsto_iff_forall_continuousAt_tendsto
    (Fs : ℕ → CumulativeDistributionFunction) (G : CumulativeDistributionFunction) :
    Tendsto Fs atTop (𝓝 G) ↔
      ∀ x, ContinuousAt G x → Tendsto (fun i ↦ Fs i x) atTop (𝓝 (G x)) := by
  rw [← tendsto_probabilityMeasure_iff_forall_continuousAt_tendsto]
  constructor
  · intro h
    simp_rw [← homeomorph_probabilityMeasure_apply_eq]
    apply homeomorph_probabilityMeasure.continuous.continuousAt.tendsto.comp h
  · intro h
    convert homeomorph_probabilityMeasure.symm.continuous.continuousAt.tendsto.comp h
    · ext1 i
      exact EquivLike.inv_apply_eq_iff_eq_apply.mp rfl
    · exact EquivLike.inv_apply_eq_iff_eq_apply.mp rfl

end CumulativeDistributionFunction

end levy_prokhorov_metric



section continuous_mulAction

namespace CumulativeDistributionFunction

lemma continuous_mulAction :
    Continuous fun (⟨A, F⟩ : AffineIncrEquiv × CumulativeDistributionFunction) ↦ A • F := by
  rw [continuous_iff_seqContinuous]
  intro AFs BG h_lim
  rw [tendsto_iff_forall_continuousAt_tendsto]
  intro x hBGx
  simp only [Function.comp_apply, mulAction_apply_eq]
  sorry -- **Issue #54** (action-on-cdf-continuous)

end CumulativeDistributionFunction

end continuous_mulAction
