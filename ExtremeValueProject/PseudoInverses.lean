/-
Copyright (c) 2025 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä, ...
-/
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.OrdContinuous
import Mathlib.Topology.Order.Basic



open Set

noncomputable section order_continuity_vs_continuity
/-!
# Left/right-order-continuous functions are (topologically) left/right-continuous

This is (mostly?) in PR #23309 to Mathlib.
-/

section ConditionallyCompleteLinearOrder

variable {X : Type*} [ConditionallyCompleteLinearOrder X] [TopologicalSpace X] [OrderTopology X]
variable {Y : Type*} [ConditionallyCompleteLinearOrder Y] [TopologicalSpace Y] [OrderTopology Y]
variable [DenselyOrdered X] {f : X → Y} {x : X}

/-- An order-theoretically left-continuous function is topologically left-continuous, assuming
the function is between conditionally complete linear orders with order topologies, and the domain
is densely ordered. -/
lemma LeftOrdContinuous.continuousWithinAt_Iic (hf : LeftOrdContinuous f) :
    ContinuousWithinAt f (Iic x) x := by
  rw [ContinuousWithinAt, OrderTopology.topology_eq_generate_intervals (α := Y)]
  simp_rw [TopologicalSpace.tendsto_nhds_generateFrom_iff, mem_nhdsWithin]
  rintro V ⟨z, rfl | rfl⟩ hxz
  -- The case `V = Ioi z`.
  · obtain ⟨_, ⟨a, hax, rfl⟩, hza⟩ := (lt_isLUB_iff <| hf isLUB_Iio).mp hxz
    exact ⟨Ioi a, isOpen_Ioi, hax, fun b hab ↦ hza.trans_le <| hf.mono hab.1.le⟩
  -- The case `V = Iio z`.
  · exact ⟨univ, isOpen_univ, trivial, fun a ha ↦ (hf.mono ha.2).trans_lt hxz⟩

/-- An order-theoretically right-continuous function is topologically right-continuous, assuming
the function is between conditionally complete linear orders with order topologies, and the domain
is densely ordered. -/
lemma RightOrdContinuous.continuousWithinAt_Ici (hf : RightOrdContinuous f) :
    ContinuousWithinAt f (Ici x) x := hf.orderDual.continuousWithinAt_Iic

-- TODO: Add `ContinuousAt` versions with weaker (pointwise) hypotheses than left/right
-- order continuity?

end ConditionallyCompleteLinearOrder

end order_continuity_vs_continuity


noncomputable section modification
/-!
# Left-continuous and right-continuous modifications of functions
-/

variable {R S : Type*}

/-- Left-continuous modification of F. -/
def lcMod [Preorder R] [SupSet S] (F : R → S) (x : R) := sSup (F '' Iio x)

/-- right-continuous modification of F. -/
def rcMod [Preorder R] [InfSet S] (F : R → S) (x : R) := sInf (F '' Ioi x)

lemma lcMod_mono [Preorder R] [CompleteSemilatticeSup S] (F : R → S) :
    Monotone (lcMod F) :=
  fun _ _ hx ↦ sSup_le_sSup <| image_mono <| Iio_subset_Iio hx

lemma rcMod_mono [Preorder R] [CompleteSemilatticeInf S] (F : R → S) :
    Monotone (rcMod F) :=
  fun _ _ hx ↦ sInf_le_sInf <| image_mono <| Ioi_subset_Ioi hx

lemma lcMod_apply_le_self_apply [Preorder R] [CompleteSemilatticeSup S] {F : R → S}
    (F_mono : Monotone F) (x : R) :
    lcMod F x ≤ F x := by
  apply sSup_le
  intro y ⟨x', x'_lt, Fx'_eq_y⟩
  simpa [← Fx'_eq_y] using F_mono x'_lt.le

lemma self_apply_le_rcMod_apply [Preorder R] [CompleteSemilatticeInf S] {F : R → S}
    (F_mono : Monotone F) (x : R) :
    F x ≤ rcMod F x :=
  lcMod_apply_le_self_apply (R := Rᵒᵈ) (S := Sᵒᵈ) (F := F) (by exact fun _ _ hx ↦ F_mono hx) x

lemma lcMod_le_self [Preorder R] [CompleteSemilatticeSup S] {F : R → S} (F_mono : Monotone F) :
    lcMod F ≤ F :=
  fun x ↦ lcMod_apply_le_self_apply F_mono x

lemma self_le_rcMod [Preorder R] [CompleteSemilatticeInf S] {F : R → S} (F_mono : Monotone F) :
    F ≤ rcMod F :=
  fun x ↦ self_apply_le_rcMod_apply F_mono x

lemma le_lcMod_apply_of_lt [Preorder R] [CompleteSemilatticeSup S] (F : R → S) {x' x : R}
    (h : x' < x) :
    F x' ≤ lcMod F x :=
  le_sSup (mem_image_of_mem F h)

lemma rcMod_apply_le_of_lt [Preorder R] [CompleteSemilatticeInf S] (F : R → S) {x' x : R}
    (h : x < x') :
    rcMod F x ≤ F x' :=
  sInf_le (mem_image_of_mem F h)

/-- The left-continuous modification of a function is left-continuous. -/
lemma leftOrdContinuous_lcMod [LinearOrder R] [CompleteSemilatticeSup S] (F : R → S) :
    LeftOrdContinuous (lcMod F) := by
  intro s lub_s h_lub_s
  refine ⟨?_, ?_⟩
  · simp only [mem_upperBounds, mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    intro x x_in_s
    exact lcMod_mono _ (h_lub_s.1 x_in_s)
  · simp only [mem_lowerBounds, mem_upperBounds, mem_image, forall_exists_index, and_imp,
               forall_apply_eq_imp_iff₂]
    intro y hy
    apply sSup_le
    intro z ⟨x, hx, Fx_eq_z⟩
    rw [← Fx_eq_z]
    obtain ⟨x', x'_in_s, x_lt_x'⟩ : ∃ x' ∈ s, x < x' := by
      by_contra con
      simp only [not_exists, not_and, not_lt] at con
      exact lt_irrefl _ (hx.trans_le (h_lub_s.2 con))
    exact (le_lcMod_apply_of_lt F x_lt_x').trans (hy x' x'_in_s)

/-- The right-continuous modification of a function is right-continuous. -/
lemma rightOrdContinuous_rcMod [LinearOrder R] [CompleteSemilatticeInf S](F : R → S) :
    RightOrdContinuous (rcMod F) :=
  leftOrdContinuous_lcMod (R := Rᵒᵈ) (S := Sᵒᵈ) (F := F)

end modification


noncomputable section pseudoinverses
/-!
# Left-continuous and right-continuous (pseudo)inverses
-/

variable {R S : Type*} [CompleteLinearOrder R] [CompleteLinearOrder S]

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
  have aux : (lcInv F) (F x') < x := (sInf_le (by simp)).trans_lt hx
  apply le_sInf fun y hy ↦ ?_
  simp only [mem_setOf_eq] at hy
  by_contra con
  simp only [ge_iff_le, not_le] at con
  simpa using (hy.trans (lcInv_mono F con.le)).trans_lt aux

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
    apply (le_sSup ?_).trans_lt hz
    exact mem_image_of_mem F hx
  apply le_sInf
  intro x' hx'
  by_contra con'
  simpa using hx'.trans_lt (aux _ (not_le.mp con'))

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

/-- The double left-continuous inverse `lcInv (lcInv F)` of `F` is the left-continuous
modification `lcMod` of `F`. -/
theorem lcInv_lcInv_apply_eq_lcMod_apply [DenselyOrdered S] (x : R) :
    lcInv (lcInv F) x = lcMod F x :=
  sInf_setOf_lcInv_ge_eq_sSup _

/-- The double right-continuous inverse `rcInv (rcInv F)` of `F` is the right-continuous
modification `rcMod` of `F`. -/
theorem rcInv_rcInv_apply_eq_rcMod_apply [DenselyOrdered S] (x : R) :
    rcInv (rcInv F) x = rcMod F x :=
  sSup_setOf_rcInv_le_eq_sInf _

/-- The double left-continuous inverse `lcInv (lcInv F)` of `F` is the left-continuous
modification `lcMod` of `F`. -/
theorem lcInv_lcInv_eq_lcMod [DenselyOrdered S] :
    lcInv (lcInv F) = lcMod F := by
  ext x
  exact lcInv_lcInv_apply_eq_lcMod_apply x

/-- The double right-continuous inverse `rcInv (rcInv F)` of `F` is the right-continuous
modification `rcMod` of `F`. -/
theorem rcInv_rcInv_eq_rcMod [DenselyOrdered S] :
    rcInv (rcInv F) = rcMod F := by
  ext x
  exact rcInv_rcInv_apply_eq_rcMod_apply x

/-- The left-continuous (pseudo-)inverse is left-continuous. -/
lemma leftOrdContinuous_lcInv [DenselyOrdered R] (F_mono : Monotone F) :
    LeftOrdContinuous (lcInv F) := by
  -- TODO: Improve this proof?
  intro s lub_s h_lub_s
  refine ⟨?_, ?_⟩
  · simp only [mem_upperBounds, mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    intro x x_in_s
    exact lcInv_mono _ (h_lub_s.1 x_in_s)
  · intro u hu
    simp only [mem_upperBounds, mem_image, forall_exists_index, and_imp,
               forall_apply_eq_imp_iff₂] at hu
    by_contra con
    simp only [not_le] at con
    obtain ⟨z, u_lt_z, z_lt⟩ := exists_between con
    have obs_z : F z ∈ upperBounds s := by
      intro y' y'_in_s
      by_contra maybe
      simp only [not_le] at maybe
      have z_le : lcInv F y' ≥ z := by
        apply le_sInf
        intro x' le_Fx'
        by_contra con'
        simp only [not_le] at con'
        apply lt_irrefl _ ((le_Fx'.trans (F_mono con'.le)).trans_lt maybe)
      exact lt_irrefl _ (u_lt_z.trans_le (z_le.trans (hu _ y'_in_s)))
    have oops : F z < lub_s := by
      by_contra maybe
      simp only [not_lt] at maybe
      have le_z : z ≥ lcInv F lub_s := sInf_le maybe
      exact lt_irrefl _ (z_lt.trans_le le_z)
    exact lt_irrefl _ (oops.trans_le (h_lub_s.2 obs_z))

/-- The right-continuous (pseudo-)inverse is right-continuous. -/
lemma rightOrdContinuous_lcInv [DenselyOrdered R] (F_mono : Monotone F) :
    RightOrdContinuous (rcInv F) :=
  leftOrdContinuous_lcInv (R := Rᵒᵈ) (S := Sᵒᵈ) (F := F) (fun _ _ hx ↦ F_mono hx)

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
