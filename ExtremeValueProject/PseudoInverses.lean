/-
Copyright (c) 2025 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä, ...
-/
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.OrdContinuous



noncomputable section pseudoinverses
/-!
# Left-continuous and right-continuous (pseudo)inverses
-/

open Set

variable {R S : Type} [CompleteLinearOrder R] [CompleteLinearOrder S]

/-- The left-continuous pseudoinverse of a function. -/
def lcInv (F : R → S) (y : S) := sInf {x | y ≤ F x}

/-- The right-continuous pseudoinverse of a function. -/
def rcInv (F : R → S) (y : S) := sSup {x | F x ≤ y}

lemma rcInv_eq_lcInv_dual (F : R → S) :
    rcInv F = @lcInv Rᵒᵈ Sᵒᵈ _ _ F :=
  rfl

variable {F : R → S}

/-- The function `lcInv F` is increasing. -/
lemma lcInv_mono (F : R → S) :
    Monotone (lcInv F) := by
  intro y₁ y₂ hy
  have key : {x | y₂ ≤ F x} ⊆ {x | y₁ ≤ F x} := fun x hx ↦ le_trans hy hx
  apply sInf_le_sInf key

/-- The function `rcInv F` is increasing. -/
lemma rcInv_mono (F : R → S) :
    Monotone (rcInv F) := by
  intro y₁ y₂ hy
  apply sSup_le_sSup fun x hx ↦ le_trans hx hy

lemma lcInv_apply_self_le (x : R) :
    (lcInv F) (F x) ≤ x :=
  sInf_le <| by simpa only [Set.mem_setOf_eq] using le_rfl

lemma le_rcInv_apply_self (x : R) :
    x ≤ (rcInv F) (F x) :=
  @lcInv_apply_self_le Rᵒᵈ Sᵒᵈ _ _ F x

lemma le_sInf_setOf_lcInv_ge {F : R → S} (x x' : R) (hx : x' < x) :
    F x' ≤ sInf {y | x ≤ lcInv F y} := by
  have aux : (lcInv F) (F x') < x := lt_of_le_of_lt (sInf_le (by simp)) hx
  apply le_sInf fun y hy ↦ ?_
  simp only [mem_setOf_eq] at hy
  by_contra con
  simp only [ge_iff_le, not_le] at con
  simpa using lt_of_le_of_lt (hy.trans (lcInv_mono F con.le)) aux

lemma sSup_setOf_rcInv_le_le {F : R → S} (x x' : R) (hx : x < x') :
    sSup {y | rcInv F y ≤ x} ≤ F x' :=
  @le_sInf_setOf_lcInv_ge Rᵒᵈ Sᵒᵈ _ _ F x x' hx

lemma sInf_setOf_lcInv_ge_ge_sSup (x : R) :
    sInf {y | x ≤ lcInv F y} ≥ sSup (F '' Iio x) := by
  apply sSup_le
  intro y ⟨x', hxx', hyx'⟩
  rw [← hyx']
  exact le_sInf_setOf_lcInv_ge _ _ hxx'

lemma sSup_setOf_rcInv_le_le_sInf (x : R) :
    sSup {y | rcInv F y ≤ x} ≤ sInf (F '' Ioi x) :=
  @sInf_setOf_lcInv_ge_ge_sSup Rᵒᵈ Sᵒᵈ _ _ F x

lemma lcInv_ge_of_sSup_lt (x : R) (z : S) (hz : sSup (F '' Iio x) < z) :
    lcInv F z ≥ x := by
  have aux (x' : R) (hx : x' < x) : F x' < z := by
    apply lt_of_le_of_lt (le_sSup ?_) hz
    exact mem_image_of_mem F hx
  apply le_sInf
  intro x' hx'
  by_contra con'
  simpa using lt_of_le_of_lt hx' (aux _ (not_le.mp con'))

lemma rcInv_le_of_lt_sInf (x : R) (z : S) (hz : z < sInf (F '' Ioi x)) :
    rcInv F z ≤ x :=
  @lcInv_ge_of_sSup_lt Rᵒᵈ Sᵒᵈ _ _ F x z hz

lemma ge_sInf_setOf_lcInv_ge (x : R) (z : S) (hz : sSup (F '' Iio x) < z) :
    z ≥ sInf {y | x ≤ lcInv F y} := by
  apply sInf_le
  exact lcInv_ge_of_sSup_lt _ _ hz

lemma le_sSup_setOf_rcInv_le (x : R) (z : S) (hz : z < sInf (F '' Ioi x)) :
    z ≤ sSup {y | rcInv F y ≤ x} :=
  @ge_sInf_setOf_lcInv_ge Rᵒᵈ Sᵒᵈ _ _ F x z hz

lemma sInf_setOf_lcInv_ge_le_sSup (x : R) [DenselyOrdered S] :
    sInf {y | x ≤ lcInv F y} ≤ sSup (F '' Iio x) := by
  suffices ∀ z, sSup (F '' Iio x) < z → sInf {y | x ≤ lcInv F y} ≤ z by
    have obs : sInf {y | x ≤ lcInv F y} ≤ sInf {z | sSup (F '' Iio x) < z} :=
      le_sInf fun z hz ↦ this _ hz
    apply obs.trans (le_of_eq ?_)
    apply sInf_eq_of_forall_ge_of_forall_gt_exists_lt
    · exact fun z hz ↦ le_of_lt hz
    · exact fun z hz ↦ exists_between hz
  exact ge_sInf_setOf_lcInv_ge x

lemma sSup_setOf_rcInv_le_ge_sInf (x : R) [DenselyOrdered S] :
    sSup {y | rcInv F y ≤ x} ≥ sInf (F '' Ioi x) :=
  @sInf_setOf_lcInv_ge_le_sSup Rᵒᵈ Sᵒᵈ _ _ F x _

/-- If `G` is the left-continuous pseudoinverse of `F`, then we have
`inf {y | G(y) ≥ x} = sup {F(x') | x' < x}`. -/
theorem sInf_setOf_lcInv_ge_eq_sSup [DenselyOrdered S] (x : R) :
    sInf {y | x ≤ lcInv F y} = sSup (F '' Iio x) :=
  le_antisymm (sInf_setOf_lcInv_ge_le_sSup x) (sInf_setOf_lcInv_ge_ge_sSup x)

/-- If `G` is the right-continuous pseudoinverse of `F`, then we have
`sup {y | x ≤ G(y)} = inf {F(x') | x' > x}`. -/
theorem sSup_setOf_rcInv_le_eq_sInf [DenselyOrdered S] (x : R) :
    sSup {y | rcInv F y ≤ x} = sInf (F '' Ioi x) :=
  @sInf_setOf_lcInv_ge_eq_sSup Rᵒᵈ Sᵒᵈ _ _ F _ x

variable (F)

-- TODO: Generalize so that the composed equivalence can be between different types.
lemma lcInv_comp_symm (φ : R ≃ R) (hφ : RightOrdContinuous φ) :
    lcInv (F ∘ φ.symm) = φ ∘ (lcInv F) := by
  ext y
  simp only [lcInv, Function.comp_apply, RightOrdContinuous.map_sInf' hφ _]
  congr
  ext x
  simp

lemma lcInv_comp (φ : R ≃ R) (hφ : RightOrdContinuous φ.symm) :
    lcInv (F ∘ φ) = φ.symm ∘ (lcInv F) :=
  lcInv_comp_symm F φ.symm hφ

lemma rcInv_comp_symm (φ : R ≃ R) (hφ : LeftOrdContinuous φ) :
    rcInv (F ∘ φ.symm) = φ ∘ (rcInv F) :=
  @lcInv_comp_symm Rᵒᵈ Sᵒᵈ _ _ F φ hφ

lemma rcInv_comp (φ : R ≃ R) (hφ : LeftOrdContinuous φ.symm) :
    rcInv (F ∘ φ) = φ.symm ∘ (rcInv F) :=
  rcInv_comp_symm F φ.symm hφ

end pseudoinverses
