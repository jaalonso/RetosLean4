-- Reto_41.lean
-- Si los picos de una sucesión están acotados, entonces tiene
--   una subsucesión monótona.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 13-noviembre-2026
-- ---------------------------------------------------------------

-- ---------------------------------------------------------------
-- Demostrar que si los picos de una sucesión están acotados,
-- entonces tiene una subsucesión monótona.
-- ---------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Recordemos las definiciones:
--    + n es un pico si, para todo m > n, a(m) ≤ a(n).
--    + a tiene infinitos picos si, para todo k, existe
--      un n > k tal que n es un pico.
--
-- Supongamos que a no tiene infinitos picos. Hay que demostrar
-- que existe una subsucesión monótona de a.
--
-- Como a no tiene infinitos picos, entonces existe un k tal
-- que ningún n > k es un pico. Es decir,
--    ∀ n > k, ∃ m > n, a(n) < a(m).                            (1)
--
-- Por (1), se puede elegir para cada n > k un índice τ(n) tal
-- que
--    τ(n) > n                                                  (2)
--    a(n) < a(τ(n))                                            (3)
-- (Para n ≤ k, τ(n) no está determinado, pero no se va a usar.)
--
-- Definimos la función ρ que coincide con τ para n > k y que,
-- para n ≤ k, vale n + 1:
--    ρ(n) = n + 1   si n ≤ k,                                  (4)
--    ρ(n) = τ(n)    si n > k.                                  (5)
-- Entonces, por (2), (4) y (5), para todo n,
--    n < ρ(n).                                                 (6)
--
-- Definimos la sucesión de índices σ por iteración de ρ a
-- partir de k+1:
--    σ(n) = ρⁿ(k+1).                                           (7)
--
-- Veamos que, para todo n,
--    k < σ(n).                                                 (8)
-- Se demuestra por inducción sobre n.
-- + Caso n = 0. Se tiene
--      k < k + 1
--        = ρ⁰(k+1)    [por definición de ρ⁰]
--        = σ(0)        [por (7)]
--   Luego k < σ(0).
-- + Caso n+1. Por hipótesis de inducción,
--      k < σ(n).                                               (9)
--   Entonces,
--      k < σ(n)                 [por (9)]
--        < ρ(σ(n))             [por (6)]
--        = ρ(ρⁿ(k+1))         [por (7)]
--        = ρⁿ⁺¹(k+1)           [por definición de ρⁿ⁺¹]
--        = σ(n+1)               [por (7)]
--   Luego k < σ(n+1).
--
-- Definimos
--    b = a ∘ σ.                                               (10)
-- Veamos que b es una subsucesión de a y que es monótona.
--
-- b es una subsucesión de a. Por (6), (7) y el Reto 33 (que
-- afirma que la órbita de una función que crece más que la
-- identidad es una función de extracción) se tiene que σ es una
-- extracción. Además, como b = a ∘ σ, entonces b es una
-- subsucesión de a.
--
-- b es monótona. Como b está definida sobre los naturales, para
-- ver que es monótona basta demostrar que, para todo n,
--    b(n) ≤ b(n+1).
--
-- Sea n ∈ ℕ. Entonces,
--    k < σ(n)          [por (8)]
--      = ρⁿ(k+1)      [por (7)]
-- Luego,
--    k < ρⁿ(k+1)                                              (11)
-- Entonces,
--    b(n) = a(σ(n))            [por (10)]
--         = a(ρⁿ(k+1))        [por (7)]
--         ≤ a(τ(ρⁿ(k+1)))     [por (3) y (11)]
--         = a(ρ(ρⁿ(k+1)))    [por (5) y (11)]
--         = a(ρⁿ⁺¹(k+1))      [por definición de ρⁿ⁺¹]
--         = a(σ(n+1))          [por (7)]
--         = b(n+1).            [por (10)]

-- Demostraciones en Lean 4
-- ========================

module

import Mathlib.Tactic
import RetosLean4.Defs -- IsAPeak, UnBddPeaks, IsExtraction, Subseq
import RetosLean4.Reto_33 -- isExtraction_of_Iterate

variable {X : Type*} [LinearOrder X]
variable {a : ℕ → X}

-- 1ª demostración
-- ===============

example
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
  set ρ : ℕ → ℕ := fun n => if n ≤ k
                            then n + 1
                            else τ n
  have ρ_gt : ∀ n, n < ρ n := by grind
  set σ : ℕ → ℕ := fun n ↦ ρ^[n] (k+1)
  have σ_eq : ∀ n, σ n = ρ^[n] (k+1) := by grind
  have hσ : ∀ n, k < σ n := by
    intro n
    -- n : ℕ
    -- ⊢ k < σ n
    induction' n with n hn
    · -- ⊢ k < σ 0
      calc k
           < k + 1           := by norm_num
         _ = ρ^[0] (k + 1)   := by norm_num
         _ = σ 0             := (σ_eq 0).symm
    · -- hn : k < σ n
      -- ⊢ k < σ (n + 1)
      calc k
           < σ n             := hn
         _ < ρ (σ n)         := ρ_gt (σ n)
         _ = ρ (ρ^[n] (k+1)) := by rw [σ_eq n]
         _ = ρ^[n+1] (k+1)   := by rw [Function.iterate_succ_apply']
         _ = σ (n+1)         := (σ_eq (n+1)).symm
  set b := a ∘ σ with hb
  use b
  -- ⊢ Subseq b a ∧ Monotone b
  constructor
  · -- ⊢ Subseq b a
    use σ
    -- ⊢ IsExtraction σ ∧ b = a ∘ σ
    constructor
    · -- ⊢ IsExtraction σ
      exact isExtraction_of_Iterate ρ ρ_gt (k+1)
    · -- ⊢ b = a ∘ σ
      exact hb
  · -- ⊢ Monotone b
    apply monotone_nat_of_le_succ
    -- ⊢ ∀ (n : ℕ), b n ≤ b (n + 1)
    intro n
    -- n : ℕ
    -- ⊢ b n ≤ b (n + 1)
    have h1 : k < ρ^[n] (k+1) := by
      calc k
           < σ n         := hσ n
         _ = ρ^[n] (k+1) := σ_eq n
    calc b n
         = (a ∘ σ) n           := by rw [hb]
       _ = a (σ n)             := Function.comp_apply
       _ = a (ρ^[n] (k+1))     := by rw [σ_eq n]
       _ ≤ a (τ (ρ^[n] (k+1))) := le_of_lt (hτ _ h1)
       _ = a (ρ (ρ^[n] (k+1))) := by grind
       _ = a (ρ^[n+1] (k+1))   := by rw [Function.iterate_succ_apply']
       _ = a (σ (n+1))         := by rw [σ_eq (n+1)]
       _ = (a ∘ σ) (n+1)       := Function.comp_apply
       _ = b (n+1)             := by rw [hb]

-- 2ª demostración
-- ===============

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
  set ρ : ℕ → ℕ := fun n => if n ≤ k
                            then n + 1
                            else τ n
  have ρ_gt : ∀ n, n < ρ n := by
    intro n
    -- n : ℕ
    -- ⊢ n < ρ n
    by_cases hn : n ≤ k
    · -- hn : n ≤ k
      -- ⊢ n < ρ n
      have h : ρ n = n + 1 := ite_eq_left hn
      rw [h]
      -- ⊢ n < n + 1
      exact Nat.lt_succ_self n
    · -- hn : ¬n ≤ k
      -- ⊢ n < ρ n
      have h : ρ n = τ n := ite_eq_right hn
      rw [h]
      -- ⊢ n < τ n
      exact τ_gt n (not_le.mp hn)
  set σ : ℕ → ℕ := fun n ↦ ρ^[n] (k+1)
  have σ_eq : ∀ n, σ n = ρ^[n] (k+1) := fun n => rfl
  have hσ : ∀ n, k < σ n := by
    intro n
    -- n : ℕ
    -- ⊢ k < σ n
    induction' n with n hn
    · -- ⊢ k < σ 0
      calc k
           < k + 1           := by norm_num
         _ = ρ^[0] (k + 1)   := by norm_num
         _ = σ 0             := (σ_eq 0).symm
    · -- hn : k < σ n
      -- ⊢ k < σ (n + 1)
      calc k
           < σ n             := hn
         _ < ρ (σ n)         := ρ_gt (σ n)
         _ = ρ (ρ^[n] (k+1)) := by rw [σ_eq n]
         _ = ρ^[n+1] (k+1)   := by rw [Function.iterate_succ_apply']
         _ = σ (n+1)         := (σ_eq (n+1)).symm
  set b := a ∘ σ with hb
  use b
  -- ⊢ Subseq b a ∧ Monotone b
  constructor
  · -- ⊢ Subseq b a
    use σ
    -- ⊢ IsExtraction σ ∧ b = a ∘ σ
    constructor
    · -- ⊢ IsExtraction σ
      exact isExtraction_of_Iterate ρ ρ_gt (k+1)
    · -- ⊢ b = a ∘ σ
      exact hb
  · -- ⊢ Monotone b
    apply monotone_nat_of_le_succ
    -- ⊢ ∀ (n : ℕ), b n ≤ b (n + 1)
    intro n
    -- n : ℕ
    -- ⊢ b n ≤ b (n + 1)
    have h1 : k < ρ^[n] (k+1) := by
      calc k
           < σ n          := hσ n
         _ = ρ^[n] (k+1)  := σ_eq n
    have h2 : ρ (ρ^[n] (k+1)) = τ (ρ^[n] (k+1)) :=
      ite_eq_right (not_le.mpr h1)
    calc b n
         = (a ∘ σ) n           := by rw [hb]
       _ = a (σ n)             := Function.comp_apply
       _ = a (ρ^[n] (k+1))     := by rw [σ_eq n]
       _ ≤ a (τ (ρ^[n] (k+1))) := le_of_lt (hτ _ h1)
       _ = a (ρ (ρ^[n] (k+1))) := by rw [h2]
       _ = a (ρ^[n+1] (k+1))   := by rw [Function.iterate_succ_apply']
       _ = a (σ (n+1))         := by rw [σ_eq (n+1)]
       _ = (a ∘ σ) (n+1)       := Function.comp_apply
       _ = b (n+1)             := by rw [hb]
