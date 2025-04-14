import Mathlib

example {f : ℝ → ℝ} (hf : Monotone f) : ∀ᵐ (x : ℝ), DifferentiableAt ℝ f x :=
  Monotone.ae_differentiableAt (hf : Monotone f)

#check Set.Countable.dense_compl

example (f : ℝ → ℝ ) (f_mono : Monotone f) : Set.Countable {x | ¬ ContinuousAt f x} := by
  exact Monotone.countable_not_continuousAt f_mono

example ( s : Set ℝ ) (hs : Set.Countable s) : Dense sᶜ := by
  exact @Set.Countable.dense_compl ℝ ℝ _ _ _ _ _ _ _ _ s hs
