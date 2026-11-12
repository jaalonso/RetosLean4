-- Reto_33.lean
-- La órbita de una función que crece más que la identidad es una extracción.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 3-noviembre-2026
-- ---------------------------------------------------------------

-- ---------------------------------------------------------------
-- Sea φ : ℕ → ℕ una función que crece más que la identidad; es
-- decir, tal que n < φ(n) para todo n. Demostrar que, para
-- cualquier punto inicial n₀ ∈ ℕ, su órbita por φ
--    n₀, φ(n₀), φ²(n₀), φ³(n₀), ...
-- es una función de extracción (es decir, es estrictamente
-- creciente).
--
-- Para ello, completar la siguiente teoría en Lean 4, donde
-- (φ^[n] n₀) representa la iterada φⁿ(n₀):
--    import Mathlib.Basic.Real.Basic
--
--    variable (φ : ℕ → ℕ)
--
--    def IsExtraction (φ : ℕ → ℕ) : Prop :=
--      StrictMono φ
--
--    lemma isExtraction_of_lt_succ -- Reto 32
--      (hφ : ∀ n, φ n < φ (n + 1))
--      : IsExtraction φ :=
--    strictMono_nat_of_lt_succ hφ
--
--    example
--      (hφ : ∀ n, n < φ n)
--      (n₀ : ℕ)
--      : IsExtraction (fun n ↦ φ^[n] n₀) :=
--    by sorry
-- ---------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Por el criterio del sucesor (Reto 32), basta probar que
--    ∀ n ∈ ℕ, φⁿ(n₀) < φⁿ⁺¹(n₀)                               (1)
--
-- Sea n ∈ ℕ. Entonces,
--    φⁿ(n₀) < φ(φⁿ(n₀))   [por la hipótesis, aplicada a φⁿ(n₀)]
--           = φⁿ⁺¹(n₀)    [por definición de iterada]
-- que es (1).

-- Demostraciones en Lean 4
-- ========================

module

import Mathlib.Basic.Real.Basic
public import RetosLean4.Defs -- IsExtraction
public import RetosLean4.Reto_32 -- isExtraction_of_lt_succ

variable (φ : ℕ → ℕ)

/-
def IsExtraction (φ : ℕ → ℕ) : Prop :=
  StrictMono φ

lemma isExtraction_of_lt_succ -- Reto 32
  (hφ : ∀ n, φ n < φ (n + 1))
  : IsExtraction φ :=
strictMono_nat_of_lt_succ hφ
-/

-- 1ª demostración
-- ===============

example
  (hφ : ∀ n, n < φ n)
  (n₀ : ℕ)
  : IsExtraction (fun n ↦ φ^[n] n₀) :=
by
  apply isExtraction_of_lt_succ
  -- ⊢ ∀ (n : ℕ), φ^[n] n₀ < φ^[n + 1] n₀
  intro n
  -- n : ℕ
  -- ⊢ φ^[n] n₀ < φ^[n + 1] n₀
  calc φ^[n] n₀
       < φ (φ^[n] n₀) := hφ (φ^[n] n₀)
     _ = φ^[n + 1] n₀ := (Function.iterate_succ_apply' φ n n₀).symm

-- 2ª demostración
-- ===============

example
  (hφ : ∀ n, n < φ n)
  (n₀ : ℕ)
  : IsExtraction (fun n ↦ φ^[n] n₀) :=
by
  apply isExtraction_of_lt_succ
  -- ⊢ ∀ (n : ℕ), φ^[n] n₀ < φ^[n + 1] n₀
  intro n
  -- n : ℕ
  -- ⊢ φ^[n] n₀ < φ^[n + 1] n₀
  rw [Function.iterate_succ_apply']
  -- ⊢ φ^[n] n₀ < φ (φ^[n] n₀)
  exact hφ (φ^[n] n₀)

-- 3ª demostración
-- ===============

public theorem isExtraction_of_Iterate
  (hφ : ∀ n, n < φ n)
  (n₀ : ℕ)
  : IsExtraction (fun n ↦ φ^[n] n₀) :=
by
  apply isExtraction_of_lt_succ
  -- ⊢ ∀ (n : ℕ), φ^[n] n₀ < φ^[n + 1] n₀
  intro n
  -- n : ℕ
  -- ⊢ φ^[n] n₀ < φ^[n + 1] n₀
  simpa [Function.iterate_succ_apply'] using hφ (φ^[n] n₀)
