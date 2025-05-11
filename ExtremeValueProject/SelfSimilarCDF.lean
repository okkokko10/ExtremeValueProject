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

lemma CumulativeDistributionFunction.npow_apply_eq
    (F : CumulativeDistributionFunction) {n : ℕ} (n_pos : 0 < n) (x : ℝ) :
    F.pow (show 0 < (n : ℝ) from Nat.cast_pos'.mpr n_pos) x = (F x) ^ n := by
  simp [pow, comp_rightOrdContinuous, show ¬ F x < 0 by simpa using apply_nonneg F x]

@[simp] lemma CumulativeDistributionFunction.smul_pow_eq_pow_smul
    (F : CumulativeDistributionFunction) (A : AffineIncrEquiv) {t : ℝ} (t_pos : 0 < t) :
    A • (F.pow t_pos) = (A • F).pow t_pos := by
  ext x
  simp only [mulAction_apply_eq, pow_apply_eq]

open Real

lemma CumulativeDistributionFunction.conjugate_smul_self_eq (G : CumulativeDistributionFunction)
    {F : CumulativeDistributionFunction} {A : AffineIncrEquiv} (hAG : A • G = F)
    (B : AffineIncrEquiv) :
    (B * A * B⁻¹) • (B • G) = B • F := by
  ext x
  rw [← congr_fun (f := fun x ↦ ((B * A * B⁻¹) • (B • G)) x) (g := fun x ↦ (B • F) x) ?_ x]
  simp only [show B • F = (B * A) • G by simp only [mul_smul, hAG],
             ← mul_smul, mul_assoc, inv_mul_cancel, mul_one]

open AffineIncrEquiv in
lemma CumulativeDistributionFunction.selfSimilar_index_zero_transform
    (G : CumulativeDistributionFunction) {β s : ℝ} (β_pos : 0 < β)
    (hG : (homOfIndex₀ β s) • G = G.pow (exp_pos s)) :
    (homOfIndex₀ 1 s) • ((mkOfCoefs (Right.inv_pos.mpr β_pos) 0) • G)
      = ((mkOfCoefs (Right.inv_pos.mpr β_pos) 0) • G).pow (exp_pos s) := by
  have obs := ((mkOfCoefs (Right.inv_pos.mpr β_pos) 0)).conjugate_homOfIndex₀ β s
  simp only [coefs_fst_mkOfCoefs, mul_inv_cancel₀ β_pos.ne.symm] at obs
  rw [← smul_pow_eq_pow_smul, ← hG, ← obs]
  simp [← mul_smul]

open AffineIncrEquiv in
lemma gumbel_type_of_selfSimilar_index_zero'' {G : CumulativeDistributionFunction}
    (G_nondeg : ¬ G.IsDegenerate) (hG : ∀ s, (homOfIndex₀ 1 s) • G = G.pow (exp_pos s)) (x : ℝ) :
    G x = exp (-(exp (-x + log (- (log (G 0)))))) := by
  sorry

open AffineIncrEquiv in
lemma gumbel_type_of_selfSimilar_index_zero' {G : CumulativeDistributionFunction}
    (G_nondeg : ¬ G.IsDegenerate) {β : ℝ} (β_pos : 0 < β)
    (hG : ∀ s, (homOfIndex₀ β s) • G = G.pow (exp_pos s)) :
    ∀ x, G x = exp (-(exp (-β⁻¹ * x + log (- (log (G 0)))))) := by
  sorry

open AffineIncrEquiv in
theorem gumbel_type_of_selfSimilar_index_zero
    {G : CumulativeDistributionFunction} (G_nondeg : ¬ G.IsDegenerate) {β : ℝ} (β_pos : 0 < β)
    (hG : ∀ s, (homOfIndex₀ β s) • G = G.pow (exp_pos s)) :
    G = (mkOfCoefs (Right.inv_pos.mpr β_pos) (-(log (- (log (G 0))))))⁻¹ • standardGumbelCDF := by
  ext x
  rw [gumbel_type_of_selfSimilar_index_zero' G_nondeg β_pos hG]
  simp only [CumulativeDistributionFunction.mulAction_apply_eq, inv_inv, apply_eq,
             coefs_fst_mkOfCoefs, one_mul, coefs_snd_mkOfCoefs]
  rw [standardGumbelCDF_apply_eq]
  simp only [neg_mul, log_neg_eq_log, neg_add_rev, neg_neg, exp_eq_exp, neg_inj]
  ring

open AffineIncrEquiv Topology Filter in
lemma apply_eq_zero_of_lt_of_selfSimilar_index_pos' {G : CumulativeDistributionFunction}
    {α c : ℝ} (α_pos : 0 < α) (hG : ∀ s, (homOfIndex α c s) • G = G.pow (exp_pos s))
    {x : ℝ} (hx : x < c) :
    G x = 0 := by
  have Gx_eq : (G x) ^ 2 = G x := by
    have Gx_sq : (homOfIndex α c (Real.log 2) • G) x = (G x) ^ 2 := by
      rw [← CumulativeDistributionFunction.npow_apply_eq G zero_lt_two x, hG (Real.log 2)]
      congr
      simpa only [Nat.cast_ofNat] using exp_log zero_lt_two
    have obs : (homOfIndex α c (Real.log 2))⁻¹ x > x := by
      simp only [homOfIndex_inv, apply_eq, homOfIndex_coefs_fst, neg_mul, homOfIndex_coefs_snd]
      have aux_pos : 0 < rexp (-(log 2 * α)) := exp_pos _
      have aux_lt_one : rexp (-(log 2 * α)) < 1 := by
        simpa only [exp_lt_one_iff, Left.neg_neg_iff] using mul_pos (log_pos one_lt_two) α_pos
      linarith [show (c - x) * (1 - rexp (-(log 2 * α))) > 0
                from mul_pos (by linarith) (by linarith)]
    apply le_antisymm
    · exact pow_le_of_le_one (G.apply_nonneg x) (G.apply_le_one x) two_ne_zero
    · simpa only [← Gx_sq] using G.mono obs.le
  have Gx_eq_01 : G x = 0 ∨ G x = 1 := by
    rw [← sub_eq_zero (b := (1 : ℝ)), ← mul_eq_zero]
    linarith
  cases' Gx_eq_01 with h0 h1
  · exact h0 -- This what actually happens.
  -- The other case leads to a contradiction.
  exfalso
  have Gx_pow (s) : (homOfIndex α c s • G) x = Real.rpow (G x) (Real.exp s) := by
    simp only [rpow_eq_pow, ← CumulativeDistributionFunction.pow_apply_eq G (exp_pos s) x, hG s]
  have but : Tendsto (fun s ↦ (homOfIndex α c s)⁻¹ x) atBot atBot := by
    have same_but : Tendsto (fun s ↦ Real.exp (-(s * α)) * (x - c) + c) atBot atBot := by
      apply tendsto_atBot_add_const_right atBot c
      apply (tendsto_mul_const_atBot_of_neg (show x - c < 0 by linarith)).mpr
      apply tendsto_exp_atTop.comp
      simp only [tendsto_neg_atTop_iff]
      exact (tendsto_mul_const_atBot_of_pos α_pos).mpr tendsto_id
    convert same_but using 1
    ext s
    simp only [homOfIndex_inv, apply_eq, homOfIndex_coefs_fst, neg_mul, homOfIndex_coefs_snd]
    ring
  have oops (s) : G ((homOfIndex α c s)⁻¹ x) = 1 := by
    change (homOfIndex α c s • G) x = 1
    rw [Gx_pow s] -- (Keep this as a separate step to avoid risk of unwanted simping.)
    simp [h1]
  have well := (G.tendsto_atBot).comp but
  apply zero_lt_one.ne
    (tendsto_nhds_unique (Tendsto.congr (f₂ := fun _ ↦ 1) ?_ well) tendsto_const_nhds)
  intro s
  dsimp
  rw [← CumulativeDistributionFunction.mulAction_apply_eq, Gx_pow] -- (Avoid unwanted simping.)
  simp [h1]

open AffineIncrEquiv in
lemma frechet_scale_pos_of_selfSimilar_index_pos' {G : CumulativeDistributionFunction}
    (G_nondeg : ¬ G.IsDegenerate) {α c : ℝ} (α_pos : 0 < α)
    (hG : ∀ s, (homOfIndex α c s) • G = G.pow (exp_pos s)) :
    0 < (-(log (G (c + 1)))) ^ α := by
  apply rpow_pos_of_pos
  simp only [Left.neg_pos_iff]
  apply log_neg
  -- Both G(c+1)=0 and G(c+1)=1 lead to a contradiction with the nondegeneracy of G,
  -- like in the proof of `apply_eq_zero_of_lt_of_selfSimilar_index_pos'`.
  · sorry
  · sorry

open AffineIncrEquiv in
lemma frechet_type_of_selfSimilar_index_pos' {G : CumulativeDistributionFunction}
    (G_nondeg : ¬ G.IsDegenerate) {α c : ℝ} (α_pos : 0 < α)
    (hG : ∀ s, (homOfIndex α c s) • G = G.pow (exp_pos s)) {x : ℝ} (hx : c < x) :
    G x = exp (-(((x - c) / ((-(log (G (c + 1)))) ^ α)) ^ (-α⁻¹))) := by
  sorry

open AffineIncrEquiv in
theorem frechet_type_of_selfSimilar_index_pos
    {G : CumulativeDistributionFunction} (G_nondeg : ¬ G.IsDegenerate) {α c : ℝ} (α_pos : 0 < α)
    (hG : ∀ s, (homOfIndex α c s) • G = G.pow (exp_pos s)) :
    G = (mkOfCoefs (frechet_scale_pos_of_selfSimilar_index_pos' G_nondeg α_pos hG) c)
        • standardFrechetCDF (Right.inv_pos.mpr α_pos) := by
  have scale_pos := frechet_scale_pos_of_selfSimilar_index_pos' G_nondeg α_pos hG
  have scale_inv_pos : 0 < ((-log (G (c + 1))) ^ α)⁻¹ := Right.inv_pos.mpr scale_pos
  set A := (mkOfCoefs (frechet_scale_pos_of_selfSimilar_index_pos' G_nondeg α_pos hG) c) with def_A
  apply CumulativeDistributionFunction.eq_of_forall_dense_eq (dense_compl_singleton c)
  intro x x_ne_c
  by_cases hxc : x < c
  · rw [apply_eq_zero_of_lt_of_selfSimilar_index_pos' α_pos hG hxc]
    have Ainv_x_neg : A⁻¹ x < 0 := by
      simp only [def_A, apply_eq, inv_coefs_fst, coefs_fst_mkOfCoefs, inv_coefs_snd,
                 coefs_snd_mkOfCoefs, neg_mul, add_neg_lt_iff_lt_add, zero_add]
      exact (mul_lt_mul_iff_of_pos_left scale_inv_pos).mpr hxc
    simp only [CumulativeDistributionFunction.mulAction_apply_eq]
    rw [standardFrechetCDF_apply_nonpos_eq]
    exact Ainv_x_neg.le
  · have hxc' : c < x := lt_of_le_of_ne (not_lt.mp hxc) fun h ↦ x_ne_c h.symm
    rw [frechet_type_of_selfSimilar_index_pos' G_nondeg α_pos hG hxc']
    have Ainv_x_pos : 0 < A⁻¹ x := by
      simp only [def_A, apply_eq, inv_coefs_fst, coefs_fst_mkOfCoefs, inv_coefs_snd,
                 coefs_snd_mkOfCoefs, neg_mul, lt_add_neg_iff_add_lt, zero_add]
      exact (mul_lt_mul_iff_of_pos_left scale_inv_pos).mpr hxc'
    simp only [CumulativeDistributionFunction.mulAction_apply_eq]
    rw [standardFrechetCDF_apply_pos_eq _ Ainv_x_pos]
    simp only [def_A, apply_eq, inv_coefs_fst, coefs_fst_mkOfCoefs, inv_coefs_snd,
               coefs_snd_mkOfCoefs, neg_mul, rpow_eq_pow, exp_eq_exp, neg_inj]
    congr
    ring

open AffineIncrEquiv Topology Filter in
lemma apply_eq_one_of_gt_of_selfSimilar_index_neg' {G : CumulativeDistributionFunction}
    {α c : ℝ} (α_neg : α < 0) (hG : ∀ s, (homOfIndex α c s) • G = G.pow (exp_pos s))
    {x : ℝ} (hx : c < x) :
    G x = 1 := by
  -- (Compare with the proof of `apply_eq_zero_of_lt_of_selfSimilar_index_pos'`.)
  sorry -- **Issue ?**

open AffineIncrEquiv in
lemma weibull_scale_pos_of_selfSimilar_index_neg' {G : CumulativeDistributionFunction}
    (G_nondeg : ¬ G.IsDegenerate) {α c : ℝ} (α_neg : α < 0)
    (hG : ∀ s, (homOfIndex α c s) • G = G.pow (exp_pos s)) :
    0 < (-(log (G (c - 1)))) ^ (-α) := by
  apply rpow_pos_of_pos
  simp only [Left.neg_pos_iff]
  apply log_neg
  -- Both G(c-1)=0 and G(c-1)=1 lead to a contradiction with the nondegeneracy of G,
  -- like in the proof of `apply_eq_zero_of_lt_of_selfSimilar_index_pos'`.
  · sorry
  · sorry

open AffineIncrEquiv in
lemma weibull_type_of_selfSimilar_index_neg' {G : CumulativeDistributionFunction}
    (G_nondeg : ¬ G.IsDegenerate) {α c : ℝ} (α_neg : α < 0)
    (hG : ∀ s, (homOfIndex α c s) • G = G.pow (exp_pos s)) {x : ℝ} (hx : x ≤ c) :
    G x = exp (-(((c - x) / ((-(log (G (c - 1)))) ^ α)) ^ (-α⁻¹))) := by
  sorry

example (ξ : ℝ) (hξ : ξ < 0) : 0 < -ξ⁻¹ := by simp [hξ]

open AffineIncrEquiv in
theorem weibull_type_of_selfSimilar_index_neg
    {G : CumulativeDistributionFunction} (G_nondeg : ¬ G.IsDegenerate) {α c : ℝ} (α_neg : α < 0)
    (hG : ∀ s, (homOfIndex α c s) • G = G.pow (exp_pos s)) :
    G = (mkOfCoefs (weibull_scale_pos_of_selfSimilar_index_neg' G_nondeg α_neg hG) c)
        • standardWeibullCDF (show 0 < -α⁻¹ by simp [α_neg]) := by
  sorry

end self_similar_cdf
