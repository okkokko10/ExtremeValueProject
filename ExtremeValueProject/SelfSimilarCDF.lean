/-
Copyright (c) 2025 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä, ...
-/
import Mathlib
import ExtremeValueProject.OneParameterAffine
import ExtremeValueProject.OrderContinuity
import ExtremeValueProject.ExtremeValueDistribution

section self_similar_cdf

noncomputable def CumulativeDistributionFunction.comp_rightOrdContinuous
    (F : CumulativeDistributionFunction) (φ : ℝ → ℝ) (hφ : RightOrdContinuous φ)
    (hφ0 : φ 0 = 0) (hφ0 : φ 1 = 1) :
    CumulativeDistributionFunction where
  toFun x := φ (F x)
  mono' := by sorry
  right_continuous' := by sorry
  tendsto_atTop := by sorry
  tendsto_atBot := by sorry

open Set Topology in
lemma Real.rightOrdContinuous_indicator_Ici_rpow {t : ℝ} (t_nn : 0 < t) :
    RightOrdContinuous (indicator (Ici 0) (fun p ↦ Real.rpow p t)) := by
  -- This is a bad proof. Should just prove continuity.
  refine Monotone.rightOrdContinuous_of_forall_continuousWithinAt_Ici ?_ ?_
  · intro p₁ p₂ hp
    by_cases nn₁ : 0 ≤ p₁
    · simpa [show p₁ ∈ Ici 0 from nn₁, show p₂ ∈ Ici 0 from nn₁.trans hp]
        using rpow_le_rpow nn₁ hp t_nn.le
    · have hp₁ : ¬ p₁ ∈ Ici 0 := nn₁
      by_cases nn₂ : 0 ≤ p₂
      · simpa [hp₁, show p₂ ∈ Ici 0 from nn₂] using rpow_nonneg nn₂ t
      · simp [hp₁, show ¬ p₂ ∈ Ici 0 from nn₂]
  · intro p
    by_cases p_nn : 0 ≤ p
    · apply ContinuousWithinAt.congr (f := fun q ↦ Real.rpow q t)
      · exact (continuous_rpow_const t_nn.le).continuousWithinAt
      · intro y hy
        simp [p_nn.trans hy]
      · simp [p_nn]
    · apply ContinuousWithinAt.congr_of_eventuallyEq (f := 0)
      · exact continuous_const.continuousWithinAt
      · have nhd : Iio 0 ∈ 𝓝[≥] p :=
          mem_nhdsGE_iff_exists_Ico_subset.mpr ⟨0, lt_of_not_ge p_nn, Ico_subset_Iio_self⟩
        filter_upwards [nhd] with y hy
        simp [show ¬ y ∈ Ici 0 from not_mem_Ici.mpr hy]
      · simp [p_nn]

noncomputable def CumulativeDistributionFunction.pow
    (F : CumulativeDistributionFunction) {t : ℝ} (t_pos : 0 < t) :
    CumulativeDistributionFunction :=
  F.comp_rightOrdContinuous _ (Real.rightOrdContinuous_indicator_Ici_rpow t_pos)
    (by simpa using Real.zero_rpow t_pos.ne.symm) (by simp)

lemma CumulativeDistributionFunction.pow_apply_eq
    (F : CumulativeDistributionFunction) {t : ℝ} (t_pos : 0 < t) (x : ℝ) :
    F.pow t_pos x = (F x) ^ t := by
  simp [pow, comp_rightOrdContinuous, show ¬ F x < 0 by simpa using apply_nonneg F x]

open Real

lemma gumbel_type_of_selfSimilar_index_zero' {G : CumulativeDistributionFunction}
    (G_nondeg : ¬ G.IsDegenerate) {β : ℝ} (β_pos : 0 < β)
    (hG : ∀ s, (AffineIncrEquiv.homOfIndex₀ β s) • G = G.pow (exp_pos s)) (x : ℝ) :
    G x = exp (-(exp (-β⁻¹ * x + log (- (log (G 0)))))) := by
  sorry

theorem gumbel_type_of_selfSimilar_index_zero
    {G : CumulativeDistributionFunction} (G_nondeg : ¬ G.IsDegenerate) {β : ℝ} (β_pos : 0 < β)
    (hG : ∀ s, (AffineIncrEquiv.homOfIndex₀ β s) • G = G.pow (exp_pos s)) :
    G = (AffineIncrEquiv.mkOfCoefs (Right.inv_pos.mpr β_pos) (-(log (- (log (G 0))))))⁻¹
        • standardGumbelCDF := by
  ext x
  rw [gumbel_type_of_selfSimilar_index_zero' G_nondeg β_pos hG]
  simp only [CumulativeDistributionFunction.mulAction_apply_eq, inv_inv, AffineIncrEquiv.apply_eq,
             AffineIncrEquiv.coefs_fst_mkOfCoefs, one_mul, AffineIncrEquiv.coefs_snd_mkOfCoefs]
  rw [standardGumbelCDF_apply_eq]
  simp only [neg_mul, log_neg_eq_log, neg_add_rev, neg_neg, exp_eq_exp, neg_inj]
  ring

lemma frechet_type_of_selfSimilar_index_pos' {G : CumulativeDistributionFunction}
    (G_nondeg : ¬ G.IsDegenerate) {α c : ℝ} (α_pos : 0 < α)
    (hG : ∀ s, (AffineIncrEquiv.homOfIndex α c s) • G = G.pow (exp_pos s)) {x : ℝ}
    (hx : c ≤ x) :
    G x = exp (-(((x - c) / ((-(log (G (c + 1)))) ^ α)) ^ (-α⁻¹))) := by
  sorry

-- theorem frechet_type_of_selfSimilar_index_pos

lemma weibull_type_of_selfSimilar_index_neg' {G : CumulativeDistributionFunction}
    (G_nondeg : ¬ G.IsDegenerate) {α c : ℝ} (α_neg : α < 0)
    (hG : ∀ s, (AffineIncrEquiv.homOfIndex α c s) • G = G.pow (exp_pos s)) {x : ℝ}
    (hx : x ≤ c) :
    G x = exp (-(((c - x) / ((-(log (G (c - 1)))) ^ α)) ^ (-α⁻¹))) := by
  sorry

-- theorem weibull_type_of_selfSimilar_index_neg

end self_similar_cdf
