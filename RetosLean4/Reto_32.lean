-- Reto_32.lean
-- Criterio del sucesor para funciones de extracción.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 3-noviembre-2026
-- ---------------------------------------------------------------

-- ---------------------------------------------------------------
-- Una función φ : ℕ → ℕ es una función de extracción si es
-- estrictamente creciente; es decir, si
--    ∀ i j ∈ ℕ, i < j → φ(i) < φ(j)
--
-- Demostrar que si
--    ∀ n, φ(n) < φ (n+1),
-- entonces φ es una función de extracción.
-- ---------------------------------------------------------------

-- Demostraciones en lenguaje natural
-- ==================================

-- Sea φ : ℕ → ℕ tal que
--    ∀ n ∈ ℕ, φ(n) < φ(n+1)                                    (1)
-- Hay que demostrar que φ es una función de extracción: es decir,
--    ∀ i j ∈ ℕ, i < j → φ(i) < φ(j)
--
-- 1ª demostración (inducción sobre j)
-- ===================================
--
-- Sean i, j ∈ ℕ con i < j. Probamos por inducción sobre j que
-- φ(i) < φ(j).
--
-- Caso j = 0. La hipótesis i < 0 es imposible, ya que ningún
-- natural es menor que 0. Por tanto, el resultado se cumple
-- trivialmente.
--
-- Paso j = n + 1. Supongamos como hipótesis de inducción que,
--    i < n → φ(i) < φ(n)                                      (ih)
-- y tenemos que demostrar que
--    i < n+1 → φ(i) < φ(n+1)
-- Para ello, sea
--    i < n+1                                                   (2)
-- y tenemos que demostrar que
--    φ(i) < φ(n+1)
-- Lo haremos distinguiendo dos casos, ya que de (2) se sigue que
--    i < n ∨ i = n
-- Caso i < n. Entonces,
--    φ(i) < φ(n)    [por ih, ya que i < n]
--         < φ(n+1)  [por (1)]
-- Caso i = n. Entonces,
--    φ(i) = φ(n)    [porque i = n]
--         < φ(n+1)  [por (1)]
--
-- 2ª demostración (inducción sobre la desigualdad)
-- ================================================
--
-- Sean i, j ∈ ℕ con i < j, o, equivalentemente, i + 1 ≤ j.
-- Probamos por inducción sobre j, a partir de j = i + 1, que
-- φ(i) < φ(j).
--
-- Caso base j = i + 1. Hay que probar φ(i) < φ(i+1), que es (1)
-- para n = i.
--
-- Paso inductivo. Sea m ≥ i + 1 y supongamos que
--    φ(i) < φ(m)                                             (ih)
-- Entonces,
--    φ(i) < φ(m)    [por ih]
--         < φ(m+1)  [por (1)]
--
-- 3ª demostración (lema de Mathlib)
-- =================================
--
-- Basta aplicar el lema strictMono_nat_of_lt_succ de Mathlib, que
-- afirma que una función f : ℕ → α, con α un preorden, es
-- estrictamente creciente si f(n) < f(n+1) para todo n. Como φ
-- cumple (1), es estrictamente creciente, y por definición, una
-- función de extracción.

-- Demostraciones en Lean 4
-- ========================

module

import Mathlib.Basic.Real.Basic
public import RetosLean4.Defs -- IsExtraction

/-
def IsExtraction (φ : ℕ → ℕ) : Prop :=
  StrictMono φ
-/

variable (φ : ℕ → ℕ)

-- 1ª demostración
-- ===============

example
  (hφ : ∀ n, φ n < φ (n + 1))
  : IsExtraction φ :=
by
  intro i j hij
  -- i j : ℕ
  -- hij : i < j
  -- ⊢ φ i < φ j
  induction j with
  | zero =>
    -- hij : i < 0
    -- ⊢ φ i < φ 0
    exact absurd hij (Nat.not_lt_zero i)
  | succ n ih =>
    -- n : ℕ
    -- ih : i < n → φ i < φ n
    -- hij : i < n + 1
    -- ⊢ φ i < φ (n + 1)
    rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hij) with h1 | h2
    · -- h1 : i < n
      calc φ i
           < φ n       := ih h1
         _ < φ (n + 1) := hφ n
    · -- h2 : i = n
      calc φ i
           = φ n := by rw [h2]
         _ < φ (n + 1) := hφ n

-- 2ª demostración
-- ===============

example
  (hφ : ∀ n, φ n < φ (n + 1))
  : IsExtraction φ :=
by
  intro i j hij
  -- i j : ℕ
  -- hij : i < j
  -- ⊢ φ i < φ j
  have h : i + 1 ≤ j := hij
  clear hij
  induction j, h using Nat.le_induction with
  | base =>
    -- ⊢ φ i < φ (i + 1)
    exact hφ i
  | succ m _ ih =>
    -- m : ℕ
    -- ih : φ i < φ m
    -- ⊢ φ i < φ (m + 1)
    calc φ i
         < φ m        := ih
       _ < φ (m + 1)  := hφ m

-- 3ª demostración
-- ===============

public theorem isExtraction_of_lt_succ
  (hφ : ∀ n, φ n < φ (n + 1))
  : IsExtraction φ :=
strictMono_nat_of_lt_succ hφ
