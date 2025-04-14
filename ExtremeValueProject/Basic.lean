import Mathlib

example {f : ℝ → ℝ} (hf : Monotone f) : ∀ᵐ (x : ℝ), DifferentiableAt ℝ f x :=
  Monotone.ae_differentiableAt (hf : Monotone f)
