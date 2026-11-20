import Mathlib.Basic.Real.Basic

def IsExtraction (φ : ℕ → ℕ) : Prop :=
  StrictMono φ

variable (φ : ℕ → ℕ)

example
  (hφ : ∀ n, φ n < φ (n + 1))
  : IsExtraction φ :=
by
  sorry
