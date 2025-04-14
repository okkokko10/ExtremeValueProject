import Mathlib.Analysis.Calculus.Monotone

example {f : ℝ → ℝ} (hf : Monotone f) : ∀ᵐ (x : ℝ), DifferentiableAt ℝ f x :=
  Monotone.ae_differentiableAt (hf : Monotone f)
