-- Reto_41.lean
-- Si los picos de una sucesión no están acotados, entonces tiene
--   una subsucesión monótona.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 13-noviembre-2026
-- ---------------------------------------------------------------

-- ---------------------------------------------------------------
-- Demostrar que si los picos de una sucesión no están acotados,
-- entonces tiene una subsucesión monótona.
-- ---------------------------------------------------------------

module

import Mathlib.Tactic
import RetosLean4.Defs -- IsAPeak, UnBddPeaks, IsExtraction, Subseq
import RetosLean4.Reto_33 -- isExtraction_of_Iterate

variable {X : Type*} [LinearOrder X]
variable {a : ℕ → X}

lemma MonotoneSubseq_of_BddPeaks
  (ha : ¬ UnBddPeaks a)
  : ∃ b, Subseq b a ∧ Monotone b :=
by
  unfold UnBddPeaks at ha
  -- ha : ¬∀ (k : ℕ), ∃ n > k, IsAPeak a n
  push Not at ha
  -- ha : ∃ k, ∀ n > k, ¬IsAPeak a n
  obtain ⟨k, hk⟩ := ha
  -- hk : ∀ n > k, ¬IsAPeak a n
  unfold IsAPeak at hk
  -- hk : ∀ n > k, ¬∀ m > n, a m ≤ a n
  push Not at hk
  -- hk : ∀ n > k, ∃ m > n, a n < a m
  choose! τ τ_gt hτ using hk
  -- τ : ℕ → ℕ
  -- τ_gt : ∀ n > k, τ n > n
  -- hτ : ∀ n > k, a n < a (τ n)
  set τ' : ℕ → ℕ := fun n => if n ≤ k
                             then n + 1
                             else τ n
  have τ'_gt : ∀ n, n < τ' n := by grind
  set σ : ℕ → ℕ := fun n ↦ τ'^[n] (k+1)
  have σ_eq : ∀ n, σ n = τ'^[n] (k+1) := by grind
  have hσ : ∀ n, k < σ n := by
    intro n
    -- n : ℕ
    -- ⊢ k < σ n
    induction' n with n hn
    · -- ⊢ k < σ 0
      calc k
           < k + 1          := by norm_num
         _ = τ'^[0] (k + 1) := by norm_num
         _ = σ 0            := (σ_eq 0).symm
    · -- hn : k < σ n
      -- ⊢ k < σ (n + 1)
      calc k
           < σ n               := hn
         _ < τ' (σ n)          := τ'_gt (σ n)
         _ = τ' (τ'^[n] (k+1)) := by rw [σ_eq n]
         _ = τ'^[n+1] (k+1)    := by rw [Function.iterate_succ_apply']
         _ = σ (n+1)           := (σ_eq (n+1)).symm
  set b := a ∘ σ with hb
  use b
  -- ⊢ Subseq b a ∧ Monotone b
  constructor
  · -- ⊢ Subseq b a
    use σ
    -- ⊢ IsExtraction σ ∧ b = a ∘ σ
    constructor
    · -- ⊢ IsExtraction σ
      exact isExtraction_of_Iterate τ' τ'_gt (k+1)
    · -- ⊢ b = a ∘ σ
      exact hb
  · -- ⊢ Monotone b
    apply monotone_nat_of_le_succ
    -- ⊢ ∀ (n : ℕ), b n ≤ b (n + 1)
    intro n
    -- n : ℕ
    -- ⊢ b n ≤ b (n + 1)
    have h1 : k < τ'^[n] (k+1) := by
      calc k
           < σ n          := hσ n
         _ = τ'^[n] (k+1) := σ_eq n
    calc b n
         = (a ∘ σ) n             := by rw [hb]
       _ = a (σ n)               := Function.comp_apply
       _ = a (τ'^[n] (k+1))      := by rw [σ_eq n]
       _ ≤ a (τ (τ'^[n] (k+1)))  := le_of_lt (hτ _ h1)
       _ = a (τ' (τ'^[n] (k+1))) := by grind
       _ = a (τ'^[n+1] (k+1))    := by rw [Function.iterate_succ_apply']
       _ = a (σ (n+1))           := by rw [σ_eq (n+1)]
       _ = (a ∘ σ) (n+1)         := Function.comp_apply
       _ = b (n+1)               := by rw [hb]
