-- Reto_42.lean
-- Si una sucesión tiene infinitos picos, entonces tiene
--   una subsucesión decreciente.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 15-noviembre-2026
-- ---------------------------------------------------------------

-- ---------------------------------------------------------------
-- Demostrar que si una sucesión tiene infinitos picos,
-- entonces tiene una subsucesión decreciente.
-- ---------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Recordemos las definiciones:
-- + a(n) es un pico si, para todo m > n, a(m) ≤ a(n).
-- + a tiene infinitos picos si, para todo k, existe
--   un n > k tal que a(n) es un pico.
--
-- Supongamos que a tiene infinitos picos. Hay que demostrar
-- que existe una subsucesión decreciente de a.
--
-- Como a tiene infinitos picos, para cada k se puede elegir un
-- índice τ(k) tal que
--    τ(k) > k                                                  (1)
--    a(τ(k)) es un pico                                        (2)
--
-- Definimos la sucesión de índices σ por iteración de τ a
-- partir de 0:
--    σ(n) = τⁿ⁺¹(0).                                           (3)
--
-- De la definición de σ se obtiene que, para todo n,
--    σ(n+1) = τⁿ⁺²(0)         [por (3)]
--           = τ(τⁿ⁺¹(0))      [por definición de τⁿ⁺²]
--           = τ(σ(n))         [por (3)]
-- Luego,
--    σ(n+1) = τ(σ(n)).                                         (4)
--
-- Veamos que, para todo n,
--    a(σ(n)) es un pico.                                       (5)
-- Se demuestra por casos sobre n.
-- + Caso n = 0. Se tiene
--      σ(0) = τ¹(0)    [por (3)]
--           = τ(0)     [por definición de τ¹]
--   y a(τ(0)) es un pico por (2).
-- + Caso n+1. Se tiene
--      σ(n+1) = τ(σ(n))   [por (4)]
--   y a(τ(σ(n))) es un pico por (2).
--
-- Veamos que, para todo n,
--    σ(n) < σ(n+1).                                            (6)
-- En efecto,
--    σ(n) < τ(σ(n))    [por (1)]
--         = σ(n+1)     [por (4)]
-- Por (6), como σ está definida sobre los naturales, σ es
-- estrictamente creciente; es decir, σ es una extracción.
--
-- Definimos
--    b = a ∘ σ.                                               (7)
-- Veamos que b es una subsucesión de a y que es decreciente.
--
-- b es una subsucesión de a. Como σ es una extracción y
-- b = a ∘ σ, entonces b es una subsucesión de a.
--
-- b es decreciente. Como b está definida sobre los naturales, para
-- ver que es decreciente basta demostrar que, para todo n,
--    b(n+1) ≤ b(n).
--
-- Sea n ∈ ℕ. Entonces,
--    b(n+1) = a(σ(n+1))   [por (7)]
--           = a(τ(σ(n)))  [por (4)]
--           ≤ a(σ(n))     [por (5) y (1)]
--           = b(n)        [por (7)]

-- Demostraciones en Lean 4
-- ========================

module

import Mathlib.Tactic
import RetosLean4.Defs -- IsAPeak, HasInfinitePeaks, IsExtraction, Subseq

variable {X : Type*} [LinearOrder X]
variable {a : ℕ → X}

-- 1ª demostración
-- ===============

example
  (ha : HasInfinitePeaks a)
  : ∃ b, Subseq b a ∧ Antitone b :=
by
  unfold HasInfinitePeaks at ha
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
  (ha : HasInfinitePeaks a)
  : ∃ b, Subseq b a ∧ Antitone b :=
by
  unfold HasInfinitePeaks at ha
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
