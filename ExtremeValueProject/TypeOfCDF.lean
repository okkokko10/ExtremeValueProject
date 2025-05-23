/-
Copyright (c) 2025 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä, ...
-/
import Mathlib
import ExtremeValueProject.CumulativeDistributionFunction
import ExtremeValueProject.AffineTransformation


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
  -- at all continuity points x of G, Fn tends to G as n grows


  -- notes: if the affine sequence inverses have the offset grow faster than the multiplier,
  -- then as n increases, the halfway point is moved further left of right,
  --   and all positions tend to the same bound as n increases.
  -- wait, nevermind...

  -- it seems to flatten out.

  intro nottrue
  -- needs: all CDF have some continuity points.
  --
  have ⟨x1,x2,x1_lt_x2,Gx1_pos,Gx2_bound,x1_cont,x2_cont⟩:= CumulativeDistributionFunction.exists₂_continuousAt_of_not_isDegenerate _ hG

  have x1_tendsto:= F_lim _ x1_cont
  --
  --special case
  -- by_cases test : F = fun n ↦ G
  -- ·
  --   by_cases test2 : A = fun (n : ℕ) ↦ AffineIncrEquiv.mkOfCoefs (?_ : (n : ℝ) + 1 > 0) 0
  --   · sorry
  --   ·
  --     simp at nottrue
  --     simp_all only [test,test2]
  --     simp_all
  --     sorry
  --   sorry

  have ⟨below,claim_below⟩ : ∃ below, ∀ n, A n x1 > below := by
    have ⟨z,z_spec_cont,z_spec_lt⟩ : ∃z, ContinuousAt G' z ∧ G' z < G x1 := sorry
    have z_converge:= nottrue z z_spec_cont
    by_contra not_bounded
    simp [-AffineIncrEquiv.apply_eq] at not_bounded


    set B := (A · x1)

    -- have not_z_bounded :=
    have not_bounded' (y) : ∃ x, B x < y := by
      have ⟨x,x_spec⟩ := not_bounded (y - 1)
      use x
      linarith
    have not_bounded_after (t) : ∃ x > t, B x < z := by
      have ⟨init,init_spec⟩ := not_bounded' z
      by_cases h : init > t
      · use init, h
      simp at h
      let qq := ⨅ i ≤ t, B i
      have : qq ≤ B init := by
        unfold qq
        sorry


      -- have ⟨succ,succ_spec⟩ := not_bounded ((A init) x1 - 1)
      have gen: ∀n, ∃y > n, B y ≤ B n := by
        intro n
        have ⟨succ,succ_spec⟩ := not_bounded (B n)
        use succ
        sorry

      sorry

    -- (nₖ)_(k∈ℕ)
    -- have ⟨s,s_increasing,s_spec⟩ : ∃ s : ℕ → ℕ, StrictMono s ∧ ∀ k, A (s k) x1 < z := by
    --   have ⟨init,init_spec⟩ := not_bounded (z - 1)
    --   -- have ⟨succ,succ_spec⟩ := not_bounded ((A init) x1 - 1)
    --   have gen: ∀n, ∃y > n, (A y) x1 ≤ (A n) x1 := by
    --     intro n
    --     have ⟨succ,succ_spec⟩ := not_bounded ((A n) x1)
    --     use succ

    --     sorry


    --   -- let rec ff(n) : ℕ := match n with
    --   --   | 0 => init
    --   --   | n+1 => (gen (ff n)).choose


    --   sorry
    -- #check subseq_tendsto_of_neBot
    have id_top : Tendsto (id : ℕ → ℕ) atTop atTop := by exact fun ⦃U⦄ a => a
    have key: ∃ᶠ (n : ℕ) in atTop, (fun k => B k < z) (id n) := by
      simp [-AffineIncrEquiv.apply_eq]
      refine Nat.frequently_atTop_iff_infinite.mpr ?_


      sorry
      -- exact frequently_atTop'.mpr not_bounded_after

    -- #check subseq_forall_of_frequently
    have ⟨s,s_atTop,s_spec⟩ := subseq_forall_of_frequently (p := (fun k ↦ B k < z)) id_top key


    -- have s_atTop : Filter.map s atTop ≤ atTop := by
    --   exact s_increasing.tendsto_atTop
      -- #check tendsto_atTop_atTop_of_monotone
      -- refine tendsto_atTop_mono (f := id) (g := s) (l:= atTop) ?_ ?_
      -- · intro n
      --   simp only [id_eq]
      --   unfold StrictMono at s_increasing
      --   induction' n with n prev
      --   ·
      --     simp only [zero_le]
      --   ·

      --     sorry


    have ineq(k): F (s k) x1 ≤ (A (s k) • F (s k)) z := by
      have in_other_words : F (s k) x1 = (A (s k) • F (s k)) (A (s k) x1) := by
        simp only [mulAction_apply_eq]
        set w := (A (s k))⁻¹ ((A (s k)) x1) with w_def
        set q := A (s k)
        have w_eq_x1: w = x1 := by
          rw [w_def]
          simp
          ring_nf
          have q_pos: q.coefs.1 ≠ 0 := by exact (AffineIncrEquiv.coefs_fst_pos q).ne'
          rw [CommGroupWithZero.mul_inv_cancel q.coefs.1 q_pos]
          exact one_mul x1
        rw [w_eq_x1]

      rw [in_other_words]
      set qf := A (s k) • F (s k)
      exact (qf.mono) (s_spec k).le

    have left_tendsto : Tendsto (fun k ↦ F (s k) x1) atTop (𝓝 (G x1)) := by
      -- #check x1_tendsto
      have : Filter.map ((fun n ↦ F n x1) ∘ s) atTop ≤ Filter.map (fun n ↦ F (n) x1) atTop := by
        rw [←Filter.map_map]
        rw [le_def]
        set q := map s atTop
        intro x lx
        exact s_atTop lx

      unfold Tendsto
      trans
      · exact this
      · exact x1_tendsto

    have right_tendsto : Tendsto (fun k ↦ (A (s k) • F (s k)) z) atTop (𝓝 (G' z)) := by
      change Tendsto ((fun n ↦ (A n • F n) z) ∘ s) atTop (𝓝 (G' z))
      unfold Tendsto at z_converge ⊢
      refine le_trans ?_ z_converge
      rw [←Filter.map_map]
      rw [le_def]
      set q := map s atTop
      intro x lx
      exact s_atTop lx
    -- #check tendsto_le_of_eventuallyLE
    have := tendsto_le_of_eventuallyLE left_tendsto right_tendsto ?_
    exact this.not_lt z_spec_lt
    clear * - ineq
    unfold EventuallyLE
    simp only [ineq]
    simp





  have ⟨above,claim_above⟩ : ∃ above, ∀ n, A n x2 < above := sorry
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
    linarith

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
