-- Reto_29.lean
-- Suma de sucesiones de Cauchy.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 28-octubre-2026
-- ---------------------------------------------------------------

-- ---------------------------------------------------------------
-- Demostrar que si aₙ y bₙ son sucesiones de Cauchy, entonces su
-- suma aₙ + bₙ también lo es.
-- ---------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Sea ε ∈ ℝ tal que
--    ε > 0                                                     (1)
-- Tenemos que demostrar que existe un N ∈ ℕ tal que
--    ∀ n ≥ N, ∀ m ≥ N, |(a + b)(m) - (a + b)(n)| < ε           (2)
--
-- Por (1), se tiene que
--    ε/2 > 0                                                   (3)
-- y, puesto que aₙ es de Cauchy, existe un N₁ tal que
--    ∀ n ≥ N1, ∀ m ≥ N₁, |a m - a n| < ε / 2                   (4)
-- y, puesto que bₙ es de Cauchy, existe un N₂ tal que
--    ∀ n ≥ N2, ∀ m ≥ N₂, |b m - b n| < ε / 2                   (5)
-- Sean
--    N = máx(N₁, N₂)                                           (6)
-- Veamos que con N se verifica (2). Para ello, sean n y m
-- tales que
--   n ≥ N                                                      (7)
--   m ≥ N                                                      (8)
-- Por (7), (8) y (6), se tiene que
--   n ≥ N₁ y m ≥ N₁
-- y, por (4), se tiene que
--   |a m - a n| < ε/2                                          (9)
-- Por (7), (8) y (6), también se tiene que
--   n ≥ N₂ y m ≥ N₂
-- y, por (5), se tiene que
--   |b m - b n| < ε/2                                         (10)
-- Finalmente,
--    |(a + b) m - (a + b) n|
--    = |(a m - a n) + (b m - b n)|
--    ≤ |a m - a n| + |b m - b n|    [por la desigualdad triangular]
--    < ε/2 + ε/2                    [por (9) y (10)]
--    = ε

-- Demostraciones en Lean 4
-- ========================

module

import Mathlib.Basic.Real.Basic
import Mathlib.Tactic
public import RetosLean4.Defs -- IsCauchy

variable {a b : ℕ → ℝ}

-- 1ª demostración
-- ===============

example
  (ha : IsCauchy a)
  (hb : IsCauchy b)
  : IsCauchy (a + b) :=
by
  intro ε hε
  -- ε : ℝ
  -- hε : 0 < ε
  -- ⊢ ∃ N, ∀ n ≥ N, ∀ m ≥ N, |(a + b) m - (a + b) n| < ε
  obtain ⟨N1, hN1⟩ := ha (ε/2) (by positivity)
  -- N1 : ℕ
  -- hN1 : ∀ n ≥ N1, ∀ m ≥ N1, |a m - a n| < ε / 2
  obtain ⟨N2, hN2⟩ := hb (ε/2) (by positivity)
  -- N2 : ℕ
  -- hN2 : ∀ n ≥ N2, ∀ m ≥ N2, |b m - b n| < ε / 2
  set N := max N1 N2
  use N
  -- ⊢ ∀ n ≥ N, ∀ m ≥ N, |(a + b) m - (a + b) n| < ε
  intro n hn m hm
  -- n : ℕ
  -- hn : n ≥ N
  -- m : ℕ
  -- hm : m ≥ N
  -- ⊢ |(a + b) m - (a + b) n| < ε
  calc |(a + b) m - (a + b) n|
       = |(a m + b m) - (a n + b n)| := rfl
     _ = |(a m - a n) + (b m - b n)| := by congr; ring
     _ ≤ |a m - a n| + |b m - b n|   := abs_add_le _ _
     _ < ε/2 + ε/2                   := by grind
     _ = ε                           := by grind

-- 2ª demostración
-- ===============

example
  (ha : IsCauchy a)
  (hb : IsCauchy b)
  : IsCauchy (a + b) :=
by
  intro ε hε
  -- ε : ℝ
  -- hε : 0 < ε
  -- ⊢ ∃ N, ∀ n ≥ N, ∀ m ≥ N, |(a + b) m - (a + b) n| < ε
  obtain ⟨N1, hN1⟩ := ha (ε/2) (by positivity)
  -- N1 : ℕ
  -- hN1 : ∀ n ≥ N1, ∀ m ≥ N1, |a m - a n| < ε / 2
  obtain ⟨N2, hN2⟩ := hb (ε/2) (by positivity)
  -- N2 : ℕ
  -- hN2 : ∀ n ≥ N2, ∀ m ≥ N2, |b m - b n| < ε / 2
  set N := max N1 N2
  use N
  -- ⊢ ∀ n ≥ N, ∀ m ≥ N, |(a + b) m - (a + b) n| < ε
  intro n hn m hm
  -- n : ℕ
  -- hn : n ≥ N
  -- m : ℕ
  -- hm : m ≥ N
  -- ⊢ |(a + b) m - (a + b) n| < ε
  have h1 : |a m - a n| < ε/2 := by
    apply hN1
    · -- ⊢ m ≥ N1
      exact le_of_max_le_left hn
    · -- ⊢ m ≥ N1
      exact le_of_max_le_left hm
  have h2 : |b m - b n| < ε/2 := by
    apply hN2
    · -- ⊢ n ≥ N2
      exact le_of_max_le_right hn
    · -- ⊢ m ≥ N2
      exact le_of_max_le_right hm
  calc |(a + b) m - (a + b) n|
       = |(a m + b m) - (a n + b n)| := rfl
     _ = |(a m - a n) + (b m - b n)| := by congr; ring
     _ ≤ |a m - a n| + |b m - b n|   := abs_add_le _ _
     _ < ε/2 + ε/2                   := by gcongr
     _ = ε                           := by ring

-- 3ª demostración
-- ===============

public theorem isCauchy_add
  (ha : IsCauchy a)
  (hb : IsCauchy b)
  : IsCauchy (a + b) :=
by
  intro ε hε
  -- ε : ℝ
  -- hε : 0 < ε
  -- ⊢ ∃ N, ∀ n ≥ N, ∀ m ≥ N, |(a + b) m - (a + b) n| < ε
  obtain ⟨N1, hN1⟩ := ha (ε/2) (half_pos hε)
  -- N1 : ℕ
  -- hN1 : ∀ n ≥ N1, ∀ m ≥ N1, |a m - a n| < ε / 2
  obtain ⟨N2, hN2⟩ := hb (ε/2) (half_pos hε)
  -- N2 : ℕ
  -- hN2 : ∀ n ≥ N2, ∀ m ≥ N2, |b m - b n| < ε / 2
  set N := max N1 N2
  use N
  -- ⊢ ∀ n ≥ N, ∀ m ≥ N, |(a + b) m - (a + b) n| < ε
  intro n hn m hm
  -- n : ℕ
  -- hn : n ≥ N
  -- m : ℕ
  -- hm : m ≥ N
  -- ⊢ |(a + b) m - (a + b) n| < ε
  have h1 : |a m - a n| < ε/2 :=
    hN1 n (le_of_max_le_left hn) m (le_of_max_le_left hm)
  have h2 : |b m - b n| < ε/2 :=
    hN2 n (le_of_max_le_right hn) m (le_of_max_le_right hm)
  calc |(a + b) m - (a + b) n|
       = |(a m + b m) - (a n + b n)| :=
           rfl
     _ = |(a m - a n) + (b m - b n)| :=
           congrArg abs (add_sub_add_comm (a m) (b m) (a n) (b n))
     _ ≤ |a m - a n| + |b m - b n| :=
           abs_add_le (a m - a n) (b m - b n)
     _ < ε/2 + ε/2 :=
           add_lt_add h1 h2
     _ = ε :=
           add_halves ε
