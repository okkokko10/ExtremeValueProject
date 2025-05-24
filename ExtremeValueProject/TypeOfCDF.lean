/-
Copyright (c) 2025 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä, ...
-/
import Mathlib
import ExtremeValueProject.CumulativeDistributionFunction
import ExtremeValueProject.AffineTransformation

import ExtremeValueProject.WeakConvergenceCDF

section preliminaries_for_type_of_cdf

open Topology Filter

open scoped Topology


/-- Construct an orientation preserving affine isomorphism `x ↦ a * x + b` of `ℝ` from
coefficients `a > 0` and `b ∈ ℝ`. -/
noncomputable def orientationPreservingAffineEquiv.mkOfCoefs {a : ℝ} (a_pos : 0 < a) (b : ℝ) :
    orientationPreservingAffineEquiv where
  val := AffineEquiv.mkOfCoefs_of_field a_pos.ne.symm b
  property := by
    change (AffineEquiv.mkOfCoefs_of_field a_pos.ne.symm b).IsOrientationPreserving
    rw [AffineEquiv.IsOrientationPreserving]
    convert a_pos
    simp

lemma orientationPreservingAffineEquiv.mkOfCoefs_apply {a : ℝ} (a_pos : 0 < a) (b : ℝ) (x : ℝ) :
    (mkOfCoefs a_pos b).val x = a * x + b :=
  rfl

lemma orientationPreservingAffineEquiv.mkOfCoefs_val {a : ℝ} (a_pos : 0 < a) (b : ℝ) (x : ℝ) :
    (mkOfCoefs a_pos b).val = AffineEquiv.mkOfCoefs_of_field a_pos.ne.symm b :=
  rfl

namespace CumulativeDistributionFunction

lemma exists₂_continuousAt_of_not_isDegenerate
    (F : CumulativeDistributionFunction) (hF : ¬ F.IsDegenerate) :
    ∃ x₁ x₂, (x₁ < x₂) ∧ (0 < F x₁) ∧ (F x₂ < 1) ∧ (ContinuousAt F x₁) ∧ (ContinuousAt F x₂) := by
  sorry -- **Issue #38**

lemma unique_orientationPreservingAffineEquiv_smul_eq_not_isDegenerate
    {F G : CumulativeDistributionFunction} {A₁ A₂ : AffineIncrEquiv}
    (hG : ¬ G.IsDegenerate) (h₁ : A₁ • F = G) (h₂ : A₂ • F = G) :
    A₁ = A₂ := by
  sorry -- **Issue #39**

open AffineIncrEquiv in
/-- If we have c.d.f. convergence `Fₙ → G` and `Aₙ • Fₙ → G'`, where `Aₙ(x) = aₙ * x + bₙ`
with `aₙ → 0` and `bₙ → β`, then `G'(x) = 0` for all `x < β`. -/
lemma apply_eq_zero_of_tendsto_of_lt
    {F : ℕ → CumulativeDistributionFunction} {G G' : CumulativeDistributionFunction}
    {a : ℕ → ℝ} (a_pos : ∀ n, 0 < a n) {b : ℕ → ℝ} {β : ℝ}
    (a_lim : Tendsto a atTop (𝓝 0)) (b_lim : Tendsto b atTop (𝓝 β))
    (F_lim : ∀ x, ContinuousAt G x → Tendsto (fun n ↦ F n x) atTop (𝓝 (G x)))
    (F_lim' : ∀ x, ContinuousAt G' x →
      Tendsto (fun n ↦ ((mkOfCoefs (a_pos n) (b n)) • (F n)) x) atTop (𝓝 (G' x)))
    {x : ℝ} (x_lt : x < β) :
    G x = 0 := by
  sorry

open AffineIncrEquiv in
/-- If we have c.d.f. convergence `Fₙ → G` and `Aₙ • Fₙ → G'`, where `Aₙ(x) = aₙ * x + bₙ`
with `aₙ → 0` and `bₙ → β`, then `G'(x) = 1` for all `x > β`. -/
lemma apply_eq_one_of_tendsto_of_gt
    {F : ℕ → CumulativeDistributionFunction} {G G' : CumulativeDistributionFunction}
    {a : ℕ → ℝ} (a_pos : ∀ n, 0 < a n) {b : ℕ → ℝ} {β : ℝ}
    (a_lim : Tendsto a atTop (𝓝 0)) (b_lim : Tendsto b atTop (𝓝 β))
    (F_lim : ∀ x, ContinuousAt G x → Tendsto (fun n ↦ F n x) atTop (𝓝 (G x)))
    (F_lim' : ∀ x, ContinuousAt G' x →
      Tendsto (fun n ↦ ((mkOfCoefs (a_pos n) (b n)) • (F n)) x) atTop (𝓝 (G' x)))
    {x : ℝ} (x_gt : β < x) :
    G x = 1 := by
  sorry

open AffineIncrEquiv in
/-- If we have c.d.f. convergence `Fₙ → G` and `Aₙ • Fₙ → G'`, where `Aₙ(x) = aₙ * x + bₙ`
with `aₙ → 0` and `bₙ → β`, then `G'` is degenerate (a delta mass at `β`). -/
lemma isDegenerate_of_tendsto_shrinking
    {F : ℕ → CumulativeDistributionFunction} {G G' : CumulativeDistributionFunction}
    {a : ℕ → ℝ} (a_pos : ∀ n, 0 < a n) {b : ℕ → ℝ} {β : ℝ}
    (a_lim : Tendsto a atTop (𝓝 0)) (b_lim : Tendsto b atTop (𝓝 β))
    (F_lim : ∀ x, ContinuousAt G x → Tendsto (fun n ↦ F n x) atTop (𝓝 (G x)))
    (F_lim' : ∀ x, ContinuousAt G' x →
      Tendsto (fun n ↦ ((mkOfCoefs (a_pos n) (b n)) • (F n)) x) atTop (𝓝 (G' x))) :
    G.IsDegenerate := by
  rw [isDegenerate_iff]
  use β
  suffices (∀ x < β, G x = 0) ∧ (∀ x > β, G x = 1) by
    funext x
    by_cases x_lt : x < β
    · have obs : ¬ x ∈ Set.Ici β := by simpa using x_lt
      simp [obs, this.1 _ x_lt]
    · have obs : x ∈ Set.Ici β := by simpa using x_lt
      by_cases x_eq : x = β
      · simp only [obs, Set.indicator_of_mem]
        have key := G.right_continuous
        have key' : ContinuousWithinAt G (Set.Ioi β) β := continuousWithinAt_Ioi_iff_Ici.mpr (key β)
        have aux : ∀ᶠ x in (𝓝[>] β), G x = 1 := by
          filter_upwards [self_mem_nhdsWithin] with x hx using this.2 _ hx
        have wow := Tendsto.congr' aux key'
        rw [tendsto_const_nhds_iff] at wow
        rw [x_eq, wow]
      have x_gt : β < x := lt_of_le_of_ne (le_of_not_lt x_lt) ((Ne.eq_def _ _).symm ▸ x_eq).symm
      simp [obs, this.2 _ x_gt]
  refine ⟨?_, ?_⟩
  · intro x hx
    exact apply_eq_zero_of_tendsto_of_lt a_pos a_lim b_lim F_lim F_lim' hx
  · intro x hx
    exact apply_eq_one_of_tendsto_of_gt a_pos a_lim b_lim F_lim F_lim' hx

open orientationPreservingAffineEquiv in
/-- If we have c.d.f. convergence `Fₙ → G` where `G` is nondegenerate and if `Aₙ`
is a sequence of oriented affine isomorphisms with scaling coefficients `aₙ → +∞`,
then `Aₙ • Fₙ` cannot converge to any c.d.f. -/
lemma not_tendsto_cdf_of_expanding_of_tendsto_not_isDegenerate
    {F : ℕ → CumulativeDistributionFunction} {G G' : CumulativeDistributionFunction}
    (F_lim : ∀ x, ContinuousAt G x → Tendsto (fun n ↦ F n x) atTop (𝓝 (G x)))
    (hG : ¬ G.IsDegenerate) {A : ℕ → AffineIncrEquiv}
    (a_lim : Tendsto (fun n ↦ (A n).val.toAffineMap.coefs_of_field.1) atTop atTop) :
    ¬ ∀ x, ContinuousAt G' x → Tendsto (fun n ↦ ((A n) • (F n)) x) atTop (𝓝 (G' x)) := by
  intro nottrue
  have ⟨x1,x2,x1_lt_x2,Gx1_pos,Gx2_bound,x1_cont,x2_cont⟩:= CumulativeDistributionFunction.exists₂_continuousAt_of_not_isDegenerate _ hG
  have right_tendsto {z : ℝ} (z_spec_cont : ContinuousAt G' z) {s : ℕ → ℕ} (s_atTop : Tendsto s atTop atTop) : Tendsto (fun k ↦ (A (s k) • F (s k)) z) atTop (𝓝 (G' z)) := by
    change Tendsto ((fun n ↦ (A n • F n) z) ∘ s) atTop (𝓝 (G' z))
    have z_converge := nottrue z z_spec_cont
    unfold Tendsto at z_converge ⊢
    refine le_trans ?_ z_converge
    exact fun ⦃u⦄ ↦ (s_atTop ·)
  have left_tendsto {x1 : ℝ} (x1_cont : ContinuousAt G x1) {s : ℕ → ℕ} (s_atTop : Tendsto s atTop atTop) : Tendsto (fun k ↦ F (s k) x1) atTop (𝓝 (G x1)) := by
    unfold Tendsto
    have x1_tendsto:= F_lim _ x1_cont
    refine le_trans ?_ x1_tendsto
    rw [(by rfl : (fun n ↦ F (s n) x1) = (fun n ↦ F n x1) ∘ s)]
    exact fun ⦃u⦄ ↦ (s_atTop ·)
  have not_bounded_after' {B : ℕ → ℝ} {lt : ℝ → ℝ → Prop} {min : ℝ → ℝ → ℝ}
      (not_bounded : ∀z, ∃ x, lt (B x) z )
      (lt_inf_iff : ∀ ⦃a b c⦄, lt a (min b c) ↔ lt a b ∧ lt a c)
      (ne : ∀ ⦃a b⦄, lt a b → a ≠ b)
      (z) (t) : ∃ x ≥ t, lt (B x) z := by
    induction t generalizing z with
    | zero =>
      simp only [ge_iff_le, zero_le, true_and]
      exact not_bounded z
    | succ t prev =>
      -- `prev (min (B t) z)` ensures that `y ≠ t`, using `B y < B t`
      have ⟨y, y_gt_t, y_spec⟩ := prev (min (B t) z)
      rw [lt_inf_iff] at y_spec
      have yyt : t ≠ y := by
        intro con
        exact (con ▸  ne y_spec.left) rfl
      refine ⟨y, Nat.lt_iff_add_one_le.mp (Nat.lt_of_le_of_ne y_gt_t yyt), y_spec.right⟩
  have ⟨below,claim_below⟩ : ∃ below, ∀ n, A n x1 > below := by
    by_contra not_bounded
    simp only [gt_iff_lt, not_exists, not_forall, not_lt] at not_bounded
    have not_bounded' (z) : ∃ x, (A x) x1 < z := by
        have ⟨x,x_spec⟩ := not_bounded (z - 1)
        use x
        linarith only [x_spec]
    have not_bounded_after := not_bounded_after' not_bounded' (@lt_inf_iff _ _) (@ne_of_lt _ _)
    have ⟨z,z_spec_cont,z_spec_lt⟩ : ∃z, ContinuousAt G' z ∧ G' z < G x1 := by
      have ⟨z,_,_,z_lt,_,z_cont,_⟩:= G'.forall_pos_exists_lt_gt_continuousAt Gx1_pos
      use z
    have ⟨(s : ℕ → ℕ), (s_atTop : Tendsto s atTop atTop), (s_spec : ∀ (n : ℕ), A (s n) x1 < z)⟩
      := subseq_forall_of_frequently tendsto_id (frequently_atTop.mpr (not_bounded_after z))
    have ineq (k) : F (s k) x1 ≤ (A (s k) • F (s k)) z := by
      rw [←mulAction_apply_eq_self_apply (F (s k)) (A (s k)) x1]
      set qf := A (s k) • F (s k)
      exact (qf.mono) (s_spec k).le
    exact (tendsto_le_of_eventuallyLE (left_tendsto x1_cont s_atTop)
      (right_tendsto z_spec_cont s_atTop) (Eventually.of_forall ineq)).not_lt z_spec_lt

  have ⟨above,claim_above⟩ : ∃ above, ∀ n, A n x2 < above := by
    by_contra not_bounded
    simp [-AffineIncrEquiv.apply_eq] at not_bounded
    have not_bounded' (z) : ∃ x, (A x) x2 > z := by
        have ⟨x,x_spec⟩ := not_bounded (z + 1)
        use x
        linarith only [x_spec]
    have not_bounded_after := not_bounded_after' not_bounded' (@sup_lt_iff _ _) (@ne_of_gt _ _)
    have ⟨z,z_spec_cont,z_spec_lt⟩ : ∃z, ContinuousAt G' z ∧ G' z > G x2 := by
      have Gx2_pos' : 0 < 1 - (G x2) := by linarith [Gx1_pos, G.mono x1_lt_x2.le]
      have ⟨_,w,_,_,w_lt,_,w_cont⟩:= G'.forall_pos_exists_lt_gt_continuousAt Gx2_pos'
      simp only [sub_sub_cancel] at w_lt
      use w
    have ⟨(s : ℕ → ℕ), (s_atTop : Tendsto s atTop atTop), (s_spec : ∀ (n : ℕ), A (s n) x2 > z)⟩
      := subseq_forall_of_frequently tendsto_id (frequently_atTop.mpr (not_bounded_after z))
    have ineq (k) : F (s k) x2 ≥ (A (s k) • F (s k)) z := by
      rw [←mulAction_apply_eq_self_apply (F (s k)) (A (s k)) x2]
      set qf := A (s k) • F (s k)
      exact (qf.mono) (s_spec k).le
    exact (tendsto_le_of_eventuallyLE (right_tendsto z_spec_cont s_atTop)
      (left_tendsto x2_cont s_atTop) (Eventually.of_forall ineq)).not_lt z_spec_lt


  have an_value (n) : (A n).val.toAffineMap.coefs_of_field.1 = (A n x2 - A n x1) / (x2 - x1) :=
    by
    simp
    rw [←mul_sub_left_distrib]
    set x2x1 := x2 - x1
    have x2x1_nonzero: x2x1 ≠ 0 := by
      rw [ne_eq]
      rw [sub_eq_zero]
      exact x1_lt_x2.ne'
    simp [x2x1_nonzero]
    rfl
  have ⟨an_above,an_claim_above⟩ : ∃ a_above, ∀ n, ((A n).val.toAffineMap.coefs_of_field.1) < a_above :=
    by
    simp_rw [an_value]
    set x2x1 := x2 - x1
    have x2x1_positive: 0 < x2x1 := by
      unfold x2x1
      norm_num
      exact x1_lt_x2
    use (above - below) / x2x1
    intro n
    suffices ((A n) x2 - (A n) x1) < (above - below) by
      exact (div_lt_div_iff_of_pos_right x2x1_positive).mpr this

    specialize claim_above n
    specialize claim_below n
    -- apply neg_lt_neg at claim_below
    linarith only [claim_below, claim_above]

  clear * - a_lim an_claim_above
  set W := fun n ↦ ((A n)).val.toAffineMap.coefs_of_field.1
  -- simp_rw [] at an_claim_above
  change ∀ (n : ℕ), W n < an_above at an_claim_above

  have := Filter.tendsto_atTop'.mp a_lim
  -- simp at this
  revert this
  simp
  use (Set.Ioi an_above)
  simp
  constructor
  · use an_above + 1
    intro _ _
    linarith
  intro x
  use x
  simp
  apply (an_claim_above x).le

  -- **Issue #40**

end CumulativeDistributionFunction

end preliminaries_for_type_of_cdf


section type_of_cdf

end type_of_cdf
