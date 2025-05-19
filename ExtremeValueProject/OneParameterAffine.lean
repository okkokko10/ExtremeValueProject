/-
Copyright (c) 2025 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä, ...
-/
import Mathlib
import ExtremeValueProject.AffineTransformation

section cauchy_hamel_functional_equation

open Real Set Pointwise MeasureTheory

lemma exists_Ioo_subset_diff_self_of_measure_pos {A : Set ℝ}
    (A_mble : MeasurableSet A) (A_pos : 0 < volume A) :
    ∃ δ > 0, Ioo (-δ) δ ⊆ A - A := by
  sorry

lemma exists_Ioo_subset_diff_of_measure_pos {A B : Set ℝ}
    (A_mble : MeasurableSet A) (A_pos : 0 < volume A)
    (B_mble : MeasurableSet B) (B_pos : 0 < volume B) :
    ∃ (a b : ℝ), a < b ∧ Ioo a b ⊆ A - B := by
  sorry

lemma exists_Ioo_subset_add_of_measure_pos {A : Set ℝ}
    (A_mble : MeasurableSet A) (A_pos : 0 < volume A) :
    ∃ (a b : ℝ), a < b ∧ Ioo a b ⊆ A + A := by
  obtain ⟨a, b, a_lt_b, hab⟩ := exists_Ioo_subset_diff_of_measure_pos
        A_mble A_pos A_mble.neg (by simpa only [Measure.measure_neg] using A_pos)
  refine ⟨a, b, a_lt_b, by simpa only [sub_neg_eq_add] using hab⟩

lemma eq_top_of_subgroup_of_measure_pos {S : AddSubgroup ℝ}
    {A : Set ℝ} (A_le_S : A ⊆ S) (A_mble : MeasurableSet A) (A_pos : 0 < volume A) :
    S = ⊤ := by
  sorry

lemma exists_forall_abs_le_of_additive_of_le_on_measure_pos
    {f : ℝ → ℝ} (f_add : ∀ t₁ t₂, f (t₁ + t₂) = f t₁ + f t₂)
    {A : Set ℝ} (A_mble : MeasurableSet A) (A_pos : 0 < volume A)
    {M : ℝ} (f_bdd_on_A : ∀ a ∈ A, f a ≤ M) :
    ∃ δ > 0, ∃ c, ∀ x ∈ Ioo (-δ) δ, |f x| ≤ c := by
  sorry

open Topology in
lemma exists_nhd_abs_le_of_additive_of_le_on_measure_pos
    {f : ℝ → ℝ} (f_add : ∀ t₁ t₂, f (t₁ + t₂) = f t₁ + f t₂)
    {A : Set ℝ} (A_mble : MeasurableSet A) (A_pos : 0 < volume A)
    {M : ℝ} (f_bdd_on_A : ∀ a ∈ A, f a ≤ M) :
    ∃ B ∈ 𝓝 (0 : ℝ), ∃ c, ∀ x ∈ B, |f x| ≤ c := by
  obtain ⟨δ, δ_pos, hδ⟩ :=
    exists_forall_abs_le_of_additive_of_le_on_measure_pos f_add A_mble A_pos f_bdd_on_A
  exact ⟨Ioo (-δ) δ, Ioo_mem_nhds (by linarith) δ_pos, hδ⟩

lemma linear_of_additive_of_le_on_measure_pos
    {f : ℝ → ℝ} (f_add : ∀ t₁ t₂, f (t₁ + t₂) = f t₁ + f t₂)
    {A : Set ℝ} (A_mble : MeasurableSet A) (A_pos : 0 < volume A)
    {M : ℝ} (f_bdd_on_A : ∀ a ∈ A, f a ≤ M) (x : ℝ) :
    f x = (f 1) * x := by
  sorry

open ENNReal in
lemma linear_of_additive_of_measurable
    {f : ℝ → ℝ} (f_add : ∀ t₁ t₂, f (t₁ + t₂) = f t₁ + f t₂) (f_mble : Measurable f) (x : ℝ) :
    f x = (f 1) * x := by
  set As : ℕ → Set ℝ := fun n ↦ {y | f y ≤ n} with def_As
  have cover : ⋃ n, As n = ⊤ := by
    ext x
    simp [exists_nat_ge (f x), def_As]
  have As_mble (n : ℕ) : MeasurableSet (As n) := f_mble measurableSet_Iic
  obtain ⟨n, hn⟩ : ∃ n, 0 < volume (As n) := by
    apply exists_measure_pos_of_not_measure_iUnion_null
    simp [cover]
  exact linear_of_additive_of_le_on_measure_pos f_add (As_mble n) hn (M := n) (by simp [def_As]) x

/-- A measurable additive map ℝ → ℝ is linear.
(The only measurable solutions to the Cauchy-Hamel functional equation are the obvious ones.) -/
lemma eq_const_mul_of_additive_of_measurable {f : ℝ → ℝ}
    (f_add : ∀ s₁ s₂, f (s₁ + s₂) = f s₁ + f s₂) (f_mble : Measurable f) :
    ∃ α, f = fun s ↦ α * s := by
  use f 1
  ext x
  exact linear_of_additive_of_measurable f_add f_mble x

/-- A measurable multiplicative map ℝ → (0,+∞) is of the form s ↦ exp(α * s) for some α ∈ ℝ.
(The only measurable solutions to the multiplicative version of the Cauchy-Hamel functional
equation are the obvious ones.) -/
lemma eq_exp_const_mul_of_multiplicative_of_measurable {f : ℝ → ℝ} (f_pos : ∀ s, 0 < f s)
    (f_multiplicative : ∀ s₁ s₂, f (s₁ + s₂) = f s₁ * f s₂) (f_mble : Measurable f) :
    ∃ α, f = fun s ↦ exp (α * s) := by
  let g := fun s ↦ log (f s)
  have f_eq_exp_g (s) : f s = exp (g s) := by
    simpa [g] using (exp_log (f_pos s)).symm
  have g_mble : Measurable g := measurable_log.comp f_mble
  have g_additive (s₁ s₂) : g (s₁ + s₂) = g s₁ + g s₂ := by
    simpa only [g, f_multiplicative] using log_mul (f_pos _).ne.symm (f_pos _).ne.symm
  obtain ⟨α, key⟩ := eq_const_mul_of_additive_of_measurable g_additive g_mble
  refine ⟨α, by ext s ; rw [f_eq_exp_g, key]⟩

end cauchy_hamel_functional_equation


section one_parameter_subgroups_of_affine_transformations

/-- The homomorphism `ℝ → AffineIncrEquiv` given by `s ↦ Aₛ`, where `Aₛ x = x + β * s`.
(`β` is a real parameter: each `β` gives a different (but related) homomorphism) -/
noncomputable def AffineIncrEquiv.homOfIndex₀ (β : ℝ) :
    MonoidHom (Multiplicative ℝ) AffineIncrEquiv where
  toFun s := .mkOfCoefs zero_lt_one (s.toAdd * β)
  map_one' := by ext x ; simp
  map_mul' s₁ s₂ := by
    ext x
    simp
    ring

/-- The homomorphism `ℝ → AffineIncrEquiv` given by `s ↦ Aₛ`, where
`Aₛ x = exp(α * s) * (x - c) + c`.
(`α c` are real parameters: each `α c` give a different homomorphism) -/
noncomputable def AffineIncrEquiv.homOfIndex (α c : ℝ) :
    MonoidHom (Multiplicative ℝ) AffineIncrEquiv where
  toFun s := .mkOfCoefs (show 0 < Real.exp (s.toAdd * α) from Real.exp_pos _)
              (c * (1 - Real.exp (s.toAdd * α)))
  map_one' := by ext x ; simp
  map_mul' s₁ s₂ := by
    ext x
    simp [add_mul, Real.exp_add]
    ring

@[simp] lemma AffineIncrEquiv.homOfIndex₀_coefs_fst {β s : ℝ} :
    (homOfIndex₀ β s).coefs.1 = 1 := by
  simp [homOfIndex₀, MonoidHom.coe_mk, OneHom.coe_mk, coefs_fst_mkOfCoefs]

@[simp] lemma AffineIncrEquiv.homOfIndex₀_coefs_snd {β s : ℝ} :
    (homOfIndex₀ β s).coefs.2 = s * β := by
  simp only [homOfIndex₀, MonoidHom.coe_mk, OneHom.coe_mk, coefs_snd_mkOfCoefs]
  congr

@[simp] lemma AffineIncrEquiv.homOfIndex_coefs_fst {α c s : ℝ} :
    (homOfIndex α c s).coefs.1 = Real.exp (s * α) := by
  simp only [homOfIndex, MonoidHom.coe_mk, OneHom.coe_mk, coefs_fst_mkOfCoefs, Real.exp_eq_exp]
  congr

@[simp] lemma AffineIncrEquiv.homOfIndex_coefs_snd {α c s : ℝ} :
    (homOfIndex α c s).coefs.2 = c * (1 - Real.exp (s * α)) := by
  simp only [homOfIndex, MonoidHom.coe_mk, OneHom.coe_mk, coefs_snd_mkOfCoefs]
  congr

@[simp] lemma AffineIncrEquiv.homOfIndex₀_zero' (β : ℝ) :
    homOfIndex₀ β (.ofAdd 0) = 1 :=
  map_one ..

@[simp] lemma AffineIncrEquiv.homOfIndex₀_zero (β : ℝ) :
    homOfIndex₀ β (@OfNat.ofNat ℝ 0 Zero.toOfNat0) = 1 :=
  map_one ..

lemma AffineIncrEquiv.homOfIndex₀_zero_apply' (β : ℝ) (x : ℝ) :
    homOfIndex₀ β (.ofAdd 0) x = x := by
  simp

lemma AffineIncrEquiv.homOfIndex₀_zero_apply (β : ℝ) (x : ℝ) :
    homOfIndex₀ β (@OfNat.ofNat ℝ 0 Zero.toOfNat0) x = x := by
  simp

lemma AffineIncrEquiv.homOfIndex₀_add (β : ℝ) (s₁ s₂ : ℝ) :
    homOfIndex₀ β (s₁ + s₂) = homOfIndex₀ β s₁ * homOfIndex₀ β s₂ :=
  map_mul ..

@[simp] lemma AffineIncrEquiv.homOfIndex₀_inv (β : ℝ) (s : ℝ) :
    (homOfIndex₀ β s)⁻¹ = homOfIndex₀ β (-s) := by
  have obs := homOfIndex₀_add β s (-s)
  simp only [add_neg_cancel, homOfIndex₀_zero] at obs
  exact DivisionMonoid.inv_eq_of_mul _ _ obs.symm

@[simp] lemma AffineIncrEquiv.homOfIndex₀_add_apply {β : ℝ} {s₁ s₂ : ℝ} (x : ℝ) :
    homOfIndex₀ β (s₁ + s₂) x = homOfIndex₀ β s₁ (homOfIndex₀ β s₂ x) := by
  simp only [homOfIndex₀_add, mul_apply_eq_comp_apply]

lemma AffineIncrEquiv.homOfIndex₀_eq_homOfIndex₀_one_mul {β s : ℝ} :
    homOfIndex₀ β s = homOfIndex₀ 1 (β * s) := by
  ext x
  simp [mul_comm]

lemma AffineIncrEquiv.conjugate_homOfIndex₀ (A : AffineIncrEquiv) (β : ℝ) (s : ℝ) :
    A * homOfIndex₀ β s * A⁻¹ = homOfIndex₀ (β * A.coefs.1) s := by
  sorry -- **Issue #46**

@[simp] lemma AffineIncrEquiv.homOfIndex_zero' (α c : ℝ) :
    homOfIndex α c (.ofAdd 0) = 1 :=
  map_one ..

@[simp] lemma AffineIncrEquiv.homOfIndex_zero (α c : ℝ) :
    homOfIndex α c (@OfNat.ofNat ℝ 0 Zero.toOfNat0) = 1 :=
  map_one ..

lemma AffineIncrEquiv.homOfIndex_zero_apply' (α c : ℝ) (x : ℝ) :
    homOfIndex α c (.ofAdd 0) x = x := by
  simp

lemma AffineIncrEquiv.homOfIndex_zero_apply (α c : ℝ) (x : ℝ) :
    homOfIndex α c (@OfNat.ofNat ℝ 0 Zero.toOfNat0) x = x := by
  simp

lemma AffineIncrEquiv.homOfIndex_add (α c : ℝ) (s₁ s₂ : ℝ) :
    homOfIndex α c (s₁ + s₂) = homOfIndex α c s₁ * homOfIndex α c s₂ :=
  map_mul ..

@[simp] lemma AffineIncrEquiv.homOfIndex_inv (α c : ℝ) (s : ℝ) :
    (homOfIndex α c s)⁻¹ = homOfIndex α c (-s) := by
  have obs := homOfIndex_add α c s (-s)
  simp only [add_neg_cancel, homOfIndex_zero] at obs
  exact DivisionMonoid.inv_eq_of_mul _ _ obs.symm

@[simp] lemma AffineIncrEquiv.homOfIndex_add_apply {α c : ℝ} {s₁ s₂ : ℝ} (x : ℝ) :
    homOfIndex α c (s₁ + s₂) x = homOfIndex α c s₁ (homOfIndex α c s₂ x) := by
  simp only [homOfIndex_add, mul_apply_eq_comp_apply]

lemma AffineIncrEquiv.homOfIndex_eq_homOfIndex_one_mul {α c s : ℝ} :
    homOfIndex α c s = homOfIndex 1 c (s * α) := by
  ext x
  simp

lemma AffineIncrEquiv.conjugate_homOfIndex (A : AffineIncrEquiv) (α c : ℝ) (s : ℝ) :
    A * homOfIndex α c s * A⁻¹ = homOfIndex α (A c) s := by
  sorry -- **Issue #46**

/-- The one-parameter subgroup of `AffineIncrEquiv` consisting of elements `Aₛ` of the form
`Aₛ x = x + β * s`, where `s ∈ ℝ`.
(`β` is a real parameter: each `β ≠ 0` in fact gives the same subgroup) -/
noncomputable def AffineIncrEquiv.subGroupOfIndex₀' (β : ℝ) :
    Subgroup AffineIncrEquiv :=
  Subgroup.map (AffineIncrEquiv.homOfIndex₀ β) ⊤

/-- The one-parameter subgroup of `AffineIncrEquiv` consisting of elements `Aₛ` of the form
`Aₛ x = x + s`, where `s ∈ ℝ`. -/
noncomputable def AffineIncrEquiv.subGroupOfIndex₀ :
    Subgroup AffineIncrEquiv :=
  Subgroup.map (AffineIncrEquiv.homOfIndex₀ 1) ⊤

@[simp] lemma AffineIncrEquiv.subGroupOfIndex₀'_eq_of_ne_zero {β : ℝ} (hβ : β ≠ 0) :
    AffineIncrEquiv.subGroupOfIndex₀' β = AffineIncrEquiv.subGroupOfIndex₀ := by
  sorry -- **Issue 44**

@[simp] lemma AffineIncrEquiv.subGroupOfIndex₀'_eq_bot :
    AffineIncrEquiv.subGroupOfIndex₀' 0 = ⊥ := by
  sorry -- **Issue 44**

@[simp] lemma AffineIncrEquiv.mem_subGroupOfIndex₀_of_no_fixed_point (A : AffineIncrEquiv)
    {α : ℝ} (hα : α ≠ 0) (c : ℝ) (hA : ∀ x, A x ≠ x) :
    A ∈ subGroupOfIndex₀ := by
  sorry -- **Issue 44**

/-- The one-parameter subgroup of `AffineIncrEquiv` consisting of elements `Aₛ` of the form
`Aₛ x = exp(α * s) * (x - c) + c` where `s ∈ ℝ`.
(`α c` are real parameters) -/
noncomputable def AffineIncrEquiv.subGroupOfIndex (α c : ℝ) :
    Subgroup AffineIncrEquiv :=
  Subgroup.map (AffineIncrEquiv.homOfIndex α c) ⊤

@[simp] lemma AffineIncrEquiv.subGroupOfIndex_eq_bot (c : ℝ) :
    subGroupOfIndex 0 c = ⊥ := by
  sorry -- **Issue 45**

@[simp] lemma AffineIncrEquiv.fixed_point_of_mem_subGroupOfIndex (A : AffineIncrEquiv)
    {α c : ℝ} (hA : A ∈ subGroupOfIndex α c):
    A c = c := by
  obtain ⟨s, _, hs⟩ := hA
  simp only [← hs, apply_eq, homOfIndex_coefs_fst, homOfIndex_coefs_snd]
  ring

@[simp] lemma AffineIncrEquiv.mem_subGroupOfIndex_iff_fixed_point (A : AffineIncrEquiv)
    {α : ℝ} (hα : α ≠ 0) (c : ℝ) :
    A ∈ subGroupOfIndex α c ↔ A c = c := by
  sorry -- **Issue 45**

/-- Functional equation for scaling coefficients of a homomorphism `f : ℝ → AffineIncrEquiv`. -/
lemma AffineIncrEquiv.homomorphism_coef_eqn_fst
    (f : MonoidHom (Multiplicative ℝ) AffineIncrEquiv) (s₁ s₂ : ℝ) :
    (f (s₁ + s₂)).coefs.1 = (f s₁).coefs.1 * (f s₂).coefs.1 := by
  simp [show f (s₁ + s₂) = f s₁ * f s₂ by rw [← f.map_mul] ; rfl]

/-- Functional equation for translation coefficients of a homomorphism `f : ℝ → AffineIncrEquiv`. -/
lemma AffineIncrEquiv.homomorphism_coef_eqn_snd
    (f : MonoidHom (Multiplicative ℝ) AffineIncrEquiv) (s₁ s₂ : ℝ) :
    (f (s₁ + s₂)).coefs.2 = (f s₁).coefs.1 * (f s₂).coefs.2 + (f s₁).coefs.2 := by
  simp [show f (s₁ + s₂) = f s₁ * f s₂ by rw [← f.map_mul] ; rfl]

open Real

lemma eq_of_functional_eqn_of_ne_zero {f : ℝ → ℝ} {α : ℝ} (α_ne_zero : α ≠ 0)
    (f_eqn : ∀ s₁ s₂, f (s₁ + s₂) = exp (α * s₁) * f s₂ + f s₁) :
    ∃ c, f = fun s ↦ c * (1 - exp (α * s)) := by
  sorry

/-- We endow the space of orientation-preserving affine isomorphisms of `ℝ` with the Borel
σ-algebra of the topology of pointwise convergence. -/
instance : MeasurableSpace AffineIncrEquiv := borel AffineIncrEquiv

instance : BorelSpace AffineIncrEquiv := ⟨rfl⟩

lemma AffineIncrEquiv.measurable_coefs_fst :
    Measurable (fun (A : AffineIncrEquiv) ↦ A.coefs.1) :=
  continuous_coefs_fst.measurable

lemma AffineIncrEquiv.measurable_coefs_snd :
    Measurable (fun (A : AffineIncrEquiv) ↦ A.coefs.2) :=
  continuous_coefs_snd.measurable

lemma AffineIncrEquiv.continuous_mkOfCoefs :
    Continuous fun (p : {a : ℝ // 0 < a} × ℝ) ↦ mkOfCoefs p.1.prop p.2 := by
  apply (continuous_induced_rng ..).mpr
  exact continuous_pi (by continuity)

lemma AffineIncrEquiv.measurable_mkOfCoefs :
    Measurable fun (p : {a : ℝ // 0 < a} × ℝ) ↦ mkOfCoefs p.1.prop p.2 := by
  have _bs1 : BorelSpace {a : ℝ // 0 < a} := Subtype.borelSpace _
  have _bs2 : BorelSpace ({a : ℝ // 0 < a} × ℝ) := Prod.borelSpace
  exact continuous_mkOfCoefs.measurable

lemma AffineIncrEquiv.continuous_of_continuous_coefs {Z : Type*} [TopologicalSpace Z]
    {f : Z → AffineIncrEquiv} (f_fst_cont : Continuous fun z ↦ (f z).coefs.1)
    (f_snd_cont : Continuous fun z ↦ (f z).coefs.2) :
    Continuous f := by
  convert AffineIncrEquiv.continuous_mkOfCoefs.comp <|
    show Continuous fun z ↦ (⟨⟨(f z).coefs.1, (f z).isOrientationPreserving⟩, (f z).coefs.2⟩) by
      continuity
  ext z x
  simp

lemma AffineIncrEquiv.measurable_of_measurable_coefs {Z : Type*} [MeasurableSpace Z]
    {f : Z → AffineIncrEquiv} (f_fst_cont : Measurable fun z ↦ (f z).coefs.1)
    (f_snd_cont : Measurable fun z ↦ (f z).coefs.2) :
    Measurable f := by
  convert AffineIncrEquiv.measurable_mkOfCoefs.comp <|
    show Measurable fun z ↦ (⟨⟨(f z).coefs.1, (f z).isOrientationPreserving⟩, (f z).coefs.2⟩) by
      measurability
  ext z x
  simp

instance : MeasurableSpace (Multiplicative ℝ) := borel (Multiplicative ℝ)

instance : BorelSpace (Multiplicative ℝ) := ⟨rfl⟩

lemma measurable_toAdd :
    Measurable (fun (s : Multiplicative ℝ) ↦ s.toAdd) :=
  continuous_toAdd.measurable

lemma measurable_toMultiplicative :
    Measurable (fun (s : ℝ) ↦ Multiplicative.ofAdd s) :=
  continuous_ofAdd.measurable

/-- Characterization of homomorphisms `f : ℝ → AffineIncrEquiv`. -/
theorem AffineIncrEquiv.homomorphism_from_Real_characterization
    (f : MonoidHom (Multiplicative ℝ) AffineIncrEquiv) (f_mble : Measurable f) :
    (∃ β, f = homOfIndex₀ β) ∨ (∃ α c, f = homOfIndex α c) := by
  sorry -- TODO: Create issue.

/-- Characterization of nontrivial homomorphisms `f : ℝ → AffineIncrEquiv`. -/
theorem AffineIncrEquiv.homomorphism_from_Real_characterization_of_nontrivial
    {f : MonoidHom (Multiplicative ℝ) AffineIncrEquiv} (f_nontriv : ¬ f = 1)
    (f_mble : Measurable f) :
    (∃ β, β ≠ 0 ∧ f = homOfIndex₀ β) ∨ (∃ α c, α ≠ 0 ∧ f = homOfIndex α c) := by
  cases' homomorphism_from_Real_characterization f f_mble with h₀ h₁
  · obtain ⟨β, hβ⟩ := h₀
    refine Or.inl ⟨β, ?_, hβ⟩
    by_contra maybe_zero
    apply f_nontriv
    ext x
    simp [hβ, maybe_zero]
  · obtain ⟨α, c, h⟩ := h₁
    refine Or.inr ⟨α, c, ?_, h⟩
    by_contra maybe_zero
    apply f_nontriv
    ext x
    simp [h, maybe_zero]

end one_parameter_subgroups_of_affine_transformations
