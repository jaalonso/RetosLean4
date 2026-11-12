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
--    ∀ p ≥ N, ∀ q ≥ N, |(a + b) p - (a + b) q| < ε             (2)
--
-- Por (1), se tiene que
--    ε/2 > 0                                                   (3)
-- y, puesto que aₙ es de Cauchy, existe un N₁ tal que
--    ∀ p ≥ N₁, ∀ q ≥ N₁, |a p - a q| < ε/2                     (4)
-- y, puesto que bₙ es de Cauchy, existe un N₂ tal que
--    ∀ p ≥ N₂, ∀ q ≥ N₂, |b p - b q| < ε/2                     (5)
-- Sean
--    N = máx(N₁, N₂)                                           (6)
-- Veamos que con N se verifica (2). Para ello, sean p y q
-- tales que
--   p ≥ N                                                      (7)
--   q ≥ N                                                      (8)
-- Por (7), (8) y (6), se tiene que
--   p ≥ N₁ y q ≥ N₁
-- y, por (4), se tiene que
--   |a p - a q| < ε/2                                          (9)
-- Por (7), (8) y (6), también se tiene que
--   p ≥ N₂ y q ≥ N₂
-- y, por (5), se tiene que
--   |b p - b q| < ε/2                                         (10)
-- Finalmente,
--    |(a + b) p - (a + b) q|
--    = |(a p - a q) + (b p - b q)|
--    ≤ |a p - a q| + |b p - b q|    [por la desigualdad triangular]
--    < ε/2 + ε/2                    [por (9) y (10)]
--    = ε

-- Demostraciones en Lean 4
-- ========================

import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

def IsCauchy (a : ℕ → ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ p ≥ N, ∀ q ≥ N, |a p - a q| < ε

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
  -- hε : ε > 0
  -- ⊢ ∃ N, ∀ p ≥ N, ∀ q ≥ N, |(a + b) p - (a + b) q| < ε
  obtain ⟨N1, hN1⟩ := ha (ε/2) (by positivity)
  -- N1 : ℕ
  -- hN1 : ∀ p ≥ N1, ∀ q ≥ N1, |a p - a q| < ε / 2
  obtain ⟨N2, hN2⟩ := hb (ε/2) (by positivity)
  -- N2 : ℕ
  -- hN2 : ∀ p ≥ N2, ∀ q ≥ N2, |b p - b q| < ε / 2
  set N := max N1 N2
  use N
  -- ⊢ ∀ p ≥ N, ∀ q ≥ N, |(a + b) p - (a + b) q| < ε
  intro p hp q hq
  -- p : ℕ
  -- hp : p ≥ N
  -- q : ℕ
  -- hq : q ≥ N
  -- ⊢ |(a + b) p - (a + b) q| < ε
  calc |(a + b) p - (a + b) q|
       = |(a p + b p) - (a q + b q)| := rfl
     _ = |(a p - a q) + (b p - b q)| := by congr; ring
     _ ≤ |a p - a q| + |b p - b q|   := abs_add_le _ _
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
  -- hε : ε > 0
  -- ⊢ ∃ N, ∀ p ≥ N, ∀ q ≥ N, |(a + b) p - (a + b) q| < ε
  obtain ⟨N1, hN1⟩ := ha (ε/2) (by positivity)
  -- N1 : ℕ
  -- hN1 : ∀ p ≥ N1, ∀ q ≥ N1, |a p - a q| < ε / 2
  obtain ⟨N2, hN2⟩ := hb (ε/2) (by positivity)
  -- N2 : ℕ
  -- hN2 : ∀ p ≥ N2, ∀ q ≥ N2, |b p - b q| < ε / 2
  set N := max N1 N2
  use N
  -- ⊢ ∀ p ≥ N, ∀ q ≥ N, |(a + b) p - (a + b) q| < ε
  intro p hp q hq
  -- p : ℕ
  -- hp : p ≥ N
  -- q : ℕ
  -- hq : q ≥ N
  -- ⊢ |(a + b) p - (a + b) q| < ε
  have h1 : |a p - a q| < ε/2 := by
    apply hN1
    · -- ⊢ p ≥ N1
      exact le_of_max_le_left hp
    · -- ⊢ q ≥ N1
      exact le_of_max_le_left hq
  have h2 : |b p - b q| < ε/2 := by
    apply hN2
    · -- ⊢ p ≥ N2
      exact le_of_max_le_right hp
    · -- ⊢ q ≥ N2
      exact le_of_max_le_right hq
  calc |(a + b) p - (a + b) q|
       = |(a p + b p) - (a q + b q)| := rfl
     _ = |(a p - a q) + (b p - b q)| := by congr; ring
     _ ≤ |a p - a q| + |b p - b q|   := abs_add_le _ _
     _ < ε/2 + ε/2                   := by gcongr
     _ = ε                           := by ring

-- 3ª demostración
-- ===============

example
  (ha : IsCauchy a)
  (hb : IsCauchy b)
  : IsCauchy (a + b) :=
by
  intro ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ N, ∀ p ≥ N, ∀ q ≥ N, |(a + b) p - (a + b) q| < ε
  obtain ⟨N1, hN1⟩ := ha (ε/2) (half_pos hε)
  -- N1 : ℕ
  -- hN1 : ∀ p ≥ N1, ∀ q ≥ N1, |a p - a q| < ε / 2
  obtain ⟨N2, hN2⟩ := hb (ε/2) (half_pos hε)
  -- N2 : ℕ
  -- hN2 : ∀ p ≥ N2, ∀ q ≥ N2, |b p - b q| < ε / 2
  set N := max N1 N2
  use N
  -- ⊢ ∀ p ≥ N, ∀ q ≥ N, |(a + b) p - (a + b) q| < ε
  intro p hp q hq
  -- p : ℕ
  -- hp : p ≥ N
  -- q : ℕ
  -- hq : q ≥ N
  -- ⊢ |(a + b) p - (a + b) q| < ε
  have h1 : |a p - a q| < ε/2 :=
    hN1 p (le_of_max_le_left hp) q (le_of_max_le_left hq)
  have h2 : |b p - b q| < ε/2 :=
    hN2 p (le_of_max_le_right hp) q (le_of_max_le_right hq)
  calc |(a + b) p - (a + b) q|
       = |(a p + b p) - (a q + b q)| :=
           rfl
     _ = |(a p - a q) + (b p - b q)| :=
           congrArg abs (add_sub_add_comm (a p) (b p) (a q) (b q))
     _ ≤ |a p - a q| + |b p - b q| :=
           abs_add_le (a p - a q) (b p - b q)
     _ < ε/2 + ε/2 :=
           add_lt_add h1 h2
     _ = ε :=
           add_halves ε
