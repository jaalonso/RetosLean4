-- Reto_42.lean
-- Si los picos de una sucesión no están acotados, entonces tiene
--   una subsucesión antítona.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 13-noviembre-2026
-- ---------------------------------------------------------------

-- ---------------------------------------------------------------
-- Demostrar que si los picos de una sucesión no están acotados,
-- entonces tiene una subsucesión antítona.
-- ---------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Recordemos las definiciones:
--    + a(n) es un pico si, para todo m > n, a(m) ≤ a(n).
--    + a tiene infinitos picos si, para todo k, existe
--      un n > k tal que n es un pico.
--
-- Supongamos que a no tiene infinitos picos. Hay que demostrar
-- que existe una subsucesión creciente de a.
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
-- Veamos que b es una subsucesión de a y que es creciente.
--
-- b es una subsucesión de a. Por (6), (7) y el Reto 33 (que
-- afirma que la órbita de una función que crece más que la
-- identidad es una función de extracción) se tiene que σ es una
-- extracción. Además, como b = a ∘ σ, entonces b es una
-- subsucesión de a.
--
-- b es creciente. Como b está definida sobre los naturales, para
-- ver que es creciente basta demostrar que, para todo n,
--    b(n) ≤ b(n+1).
--
-- Sea n ∈ ℕ. Entonces,
--    k < σ(n)          [por (8)]
--      = ρⁿ(k+1)      [por (7)]
-- Luego,
--    k < ρⁿ(k+1)                                              (11)
-- Entonces,
--    b(n) = a(σ(n))            [por (10)]
--         = a(ρⁿ(k+1))         [por (7)]
--         ≤ a(τ(ρⁿ(k+1)))      [por (3) y (11)]
--         = a(ρ(ρⁿ(k+1)))      [por (5) y (11)]
--         = a(ρⁿ⁺¹(k+1))       [por definición de ρⁿ⁺¹]
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
  (ha : UnBddPeaks a)
  : ∃ b, Subseq b a ∧ Antitone b :=
by
  unfold UnBddPeaks at ha
  -- ha : ∀ (k : ℕ), ∃ n > k, IsAPeak a n
  choose! τ τ_gt τ_peak using ha
  -- τ : ℕ → ℕ
  -- τ_gt : ∀ k, τ k > k
  -- τ_peak : ∀ k, IsAPeak a (τ k)
  set σ : ℕ → ℕ := fun n ↦ τ^[n+1] 0
  have σ_succ : ∀ n, σ (n+1) = τ (σ n) := by
    intro n
    -- n : ℕ
    -- ⊢ σ (n + 1) = τ (σ n)
    calc σ (n + 1)
         = τ^[(n + 1) + 1] 0 := rfl
       _ = τ (τ^[n + 1] 0)   := Function.iterate_succ_apply' τ (n+1) 0
       _ = τ (σ n)           := rfl
  have σ_peak : ∀ n, IsAPeak a (σ n) := by
    intro n
    -- n : ℕ
    -- ⊢ IsAPeak a (σ n)
    cases n with
    | zero =>
      -- ⊢ IsAPeak a (σ 0)
      exact τ_peak 0
    | succ n =>
      -- n : ℕ
      -- ⊢ IsAPeak a (σ (n + 1))
      rw [σ_succ]
      -- ⊢ IsAPeak a (τ (σ n))
      exact τ_peak (σ n)
  have σ_mono : IsExtraction σ := by
    apply strictMono_nat_of_lt_succ
    -- ⊢ ∀ (n : ℕ), σ n < σ (n + 1)
    intro n
    -- n : ℕ
    -- ⊢ σ n < σ (n + 1)
    rw [σ_succ]
    -- ⊢ σ n < τ (σ n)
    exact τ_gt (σ n)
  set b := a ∘ σ with hb
  use b
  -- ⊢ Subseq b a ∧ Antitone b
  constructor
  · -- ⊢ Subseq b a
    use σ
  · -- ⊢ Antitone b
    apply antitone_nat_of_succ_le
    -- ⊢ ∀ (n : ℕ), b (n + 1) ≤ b n
    intro n
    -- n : ℕ
    -- ⊢ b (n + 1) ≤ b n
    calc b (n + 1)
         = (a ∘ σ) (n + 1) := rfl
       _ = a (σ (n + 1))   := rfl
       _ = a (τ (σ n))     := congrArg a (σ_succ n)
       _ ≤ a (σ n)         := σ_peak n (τ (σ n)) (τ_gt (σ n))
       _ = (a ∘ σ) n       := rfl
       _ = b n             := rfl


-- 2ª demostración
-- ===============

example
  (ha : UnBddPeaks a)
  : ∃ b, Subseq b a ∧ Antitone b :=
by
  unfold UnBddPeaks at ha
  -- ha : ∀ (k : ℕ), ∃ n > k, IsAPeak a n
  choose! τ τ_gt τ_peak using ha
  -- τ : ℕ → ℕ
  -- τ_gt : ∀ k, τ k > k
  -- τ_peak : ∀ k, IsAPeak a (τ k)
  set σ : ℕ → ℕ := fun n ↦ τ^[n+1] 0
  have σ_succ : ∀ n, σ (n+1) = τ (σ n) :=
    fun n => Function.iterate_succ_apply' τ (n+1) 0
  have σ_peak : ∀ n, IsAPeak a (σ n) := by
    intro n
    -- ⊢ IsAPeak a (σ n)
    cases n with
    | zero =>
      -- ⊢ IsAPeak a (σ 0)
      exact τ_peak 0
    | succ n =>
      -- n : ℕ
      -- ⊢ IsAPeak a (σ (n + 1))
      rw [σ_succ]
      -- ⊢ IsAPeak a (τ (σ n))
      exact τ_peak (σ n)
  have σ_mono : IsExtraction σ := by
    apply strictMono_nat_of_lt_succ
    -- ⊢ ∀ (n : ℕ), σ n < σ (n + 1)
    intro n
    -- n : ℕ
    -- ⊢ σ n < σ (n + 1)
    rw [σ_succ]
    -- ⊢ σ n < τ (σ n)
    exact τ_gt (σ n)
  refine ⟨a ∘ σ, ⟨σ, σ_mono, rfl⟩, ?_⟩
  -- ⊢ Antitone (a ∘ σ)
  apply antitone_nat_of_succ_le
  -- ⊢ ∀ (n : ℕ), (a ∘ σ) (n + 1) ≤ (a ∘ σ) n
  intro n
  -- n : ℕ
  -- ⊢ (a ∘ σ) (n + 1) ≤ (a ∘ σ) n
  exact σ_peak n (σ (n+1)) (σ_mono (Nat.lt_succ_self n))
