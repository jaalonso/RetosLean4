-- Reto_34.lean
-- Si P se cumple para números arbitrariamente grandes, existe una
--   extracción a lo largo de la cual P siempre se cumple.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 5-noviembre-2026
-- ---------------------------------------------------------------

-- ---------------------------------------------------------------
-- Sea P : ℕ → Prop una propiedad de los números naturales que p
-- se cumple para números arbitrariamente grandes; es decir,
--    ∀ N, ∃ n > N, P(n)
--
-- Demuestrar que existe una función de extracción (es decir, una
-- función φ : ℕ → ℕ estrictamente creciente) a lo largo de la
-- cual P siempre se cumple; es decir,
--    ∀ n, P(φ(n))
--
-- Para ello, completar la siguiente teoría en Lean 4:
--    import Mathlib.Basic.Real.Basic
--
--    open Function
--
--    def IsExtraction (φ : ℕ → ℕ) : Prop :=
--      StrictMono φ
--
--    lemma isExtraction_of_Iterate -- Reto 33
--      (φ : ℕ → ℕ)
--      (hφ : ∀ n, n < φ n)
--      (n₀ : ℕ)
--      : IsExtraction (fun n ↦ φ^[n] n₀) :=
--    by
--      apply strictMono_nat_of_lt_succ
--      -- ⊢ ∀ (n : ℕ), φ^[n] n₀ < φ^[n + 1] n₀
--      intro n
--      -- n : ℕ
--      -- ⊢ φ^[n] n₀ < φ^[n + 1] n₀
--      simpa [Function.iterate_succ_apply'] using hφ (φ^[n] n₀)
--
--    variable (P : ℕ → Prop)
--
--    example
--      (h : ∀ N, ∃ n > N, P n)
--      : ∃ φ : ℕ → ℕ, IsExtraction φ ∧ ∀ n, P (φ n) :=
--    by sorry
-- ---------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Por hipótesis, para cada N existe un n > N que cumple
-- P. Eligiendo uno de esos n para cada N, obtenemos una función
--    τ : ℕ → ℕ
-- con dos propiedades:
--    ∀ n, τ(n) > n                                            (1)
--    ∀ n, P(τ(n))                                             (2)
--
-- Definimos
--    φ(n) = τⁿ(τ(0)),
-- donde τⁿ denota la composición de τ consigo misma n veces; es
-- decir,
--    φ(0) = τ(0),
--    φ(1) = τ(τ(0)),
--    φ(2) = τ(τ(τ(0))),
-- y así sucesivamente. (Se parte de τ(0) y no de 0 porque P(0)
-- podría no cumplirse.)
--
-- Veamos que φ cumple lo pedido.
--
-- (a) φ es una función de extracción, por el lema del Reto 33
-- (aplicado a τ, con valor inicial τ(0)) y (1).
--
-- (b) P(φ(n)) se cumple para todo n. Sea n un natural cualquiera.
-- Entonces,
--    φ(n) = τ(τⁿ(0))                                           (3)
-- ya que
--    φ(n) = τⁿ(τ(0))
--         = τⁿ⁺¹(0)
--         = τ(τⁿ(0))
-- Por (2), se tiene
--    P(τ(τⁿ(0)))                                               (4)
-- Luego, por (4) y (3), se tiene
--    P(φ(n)).

-- Demostraciones en Lean 4
-- ========================

module

import Mathlib.Basic.Real.Basic
public import RetosLean4.Defs -- IsExtraction
public import RetosLean4.Reto_33 -- isExtraction_of_Iterate

open Function

variable (P : ℕ → Prop)

/-
def IsExtraction (φ : ℕ → ℕ) : Prop :=
  StrictMono φ

lemma isExtraction_of_Iterate -- Reto 33
  (φ : ℕ → ℕ)
  (hφ : ∀ n, n < φ n)
  (n₀ : ℕ)
  : IsExtraction (fun n ↦ φ^[n] n₀) :=
by
  apply strictMono_nat_of_lt_succ
  -- ⊢ ∀ (n : ℕ), φ^[n] n₀ < φ^[n + 1] n₀
  intro n
  -- n : ℕ
  -- ⊢ φ^[n] n₀ < φ^[n + 1] n₀
  simpa [Function.iterate_succ_apply'] using hφ (φ^[n] n₀)
-/

-- 1ª demostración
-- ===============

example
  (h : ∀ N, ∃ n > N, P n)
  : ∃ φ : ℕ → ℕ, IsExtraction φ ∧ ∀ n, P (φ n) :=
by
  choose τ hτBnd hτP using h
  -- τ : ℕ → ℕ
  -- hτBnd : ∀ (N : ℕ), τ N > N
  -- hτP : ∀ (N : ℕ), P (τ N)
  let φ := fun n ↦ τ^[n] (τ 0)
  use φ
  -- ⊢ IsExtraction φ ∧ ∀ (n : ℕ), P (φ n)
  constructor
  · -- ⊢ IsExtraction φ
    apply isExtraction_of_Iterate τ hτBnd (τ 0)
  · -- ⊢ ∀ (n : ℕ), P (φ n)
    intro n
    -- n : ℕ
    -- ⊢ P (φ n)
    have h1 : φ n = τ (τ^[n] 0) := by
      calc φ n
           = τ^[n] (τ 0) := rfl
         _ = τ^[n + 1] 0 := (iterate_succ_apply τ n 0).symm
         _ = τ (τ^[n] 0) := iterate_succ_apply' τ n 0
    rw [h1]
    -- ⊢ P (τ (τ^[n] 0))
    exact hτP (τ^[n] 0)

-- 2ª demostración
-- ===============

public theorem exists_extraction_of_frequently
  (h : ∀ N, ∃ n > N, P n)
  : ∃ φ : ℕ → ℕ, IsExtraction φ ∧ ∀ n, P (φ n) :=
by
  choose τ hτBnd hτP using h
  -- τ : ℕ → ℕ
  -- hτBnd : ∀ (N : ℕ), τ N > N
  -- hτP : ∀ (N : ℕ), P (τ N)
  refine ⟨fun n ↦ τ^[n] (τ 0), isExtraction_of_Iterate τ hτBnd (τ 0), ?_⟩
  -- ⊢ ∀ (n : ℕ), P ((fun n => τ^[n] (τ 0)) n)
  intro n
  -- n : ℕ
  -- ⊢ ⊢ P ((fun n => τ^[n] (τ 0)) n)
  show P (τ^[n + 1] 0)
  rw [Function.iterate_succ_apply']
  -- ⊢ P (τ (τ^[n] 0))
  exact hτP (τ^[n] 0)
