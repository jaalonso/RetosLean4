-- Reto_35.lean
-- Existencia de huecos ordenados en sucesiones que no son de Cauchy.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 6-noviembre-2026
-- ---------------------------------------------------------------

-- ---------------------------------------------------------------
-- Demostrar que si a es una sucesión que no es de Cauchy,
-- entonces existe ε > 0 tal que
--    ∀ N ∈ ℕ, ∃ n ≥ N, ∃ m ≥ n, ε ≤ |a(m) - a(n)|
-- ---------------------------------------------------------------

-- Demostraciones en lenguaje natural
-- ==================================

-- Puesto que a no es de Cauchy, se tiene que
--    ¬(∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ m ≥ N, |a(m) - a(n)| < ε)
-- Interiorizando la negación, existe un ε tal que
--    ε > 0                                                    (1)
--    ∀ N, ∃ n ≥ N, ∃ m ≥ N, ε ≤ |a(m) - a(n)|                 (2)
-- Veamos que se verifica
--    ∀ N ∈ ℕ, ∃ n ≥ N, ∃ m ≥ n, ε ≤ |a(m) - a(n)|             (3)
-- Para ello, sea N ∈ ℕ. Por (2), existen n, m tales que
--    n ≥ N                                                    (4)
--    m ≥ N                                                    (5)
--    ε ≤ |a(m) - a(n)|                                        (6)
-- Lo probaremos distinguiendo casos según n ≤ m.
--
-- Caso 1: Supongamos que
--    n ≤ m                                                    (7)
-- entonces (3) se cumple para n y m por (4), (7) y (6).
--
-- Caso 2: Supongamos que
--    m ≤ n                                                    (8)
-- Entonces, por (6) y la conmutatividad del valor absoluto
-- (|x - y| = |y - x|), se tiene que
--    ε ≤ |a(n) - a(m)|                                        (9)
-- y (3) se cumple para m y n por (5), (8) y (9).

-- Demostraciones en Lean 4
-- ========================

module

import Mathlib.Tactic
public import RetosLean4.Defs -- IsCauchy

variable {X : Type*} [CommRing X] [LinearOrder X]
variable {a : ℕ → X}

-- 1ª demostración
-- ===============

example
  (hC : ¬ IsCauchy a)
  : ∃ ε : X, 0 < ε ∧ ∀ (N : ℕ), ∃ n ≥ N, ∃ m ≥ n, ε ≤ |a m - a n| :=
by
  unfold IsCauchy at hC
  -- hC : ¬∀ (ε : X), 0 < ε → ∃ N, ∀ n ≥ N, ∀ m ≥ N, |a m - a n| < ε
  push Not at hC
  -- hC : ∃ ε, 0 < ε ∧ ∀ (N : ℕ), ∃ n ≥ N, ∃ m ≥ N, ε ≤ |a m - a n|
  obtain ⟨ε, hε1, hε2⟩ := hC
  -- ε : X
  -- hε1 : 0 < ε
  -- hε2 : ∀ (N : ℕ), ∃ n ≥ N, ∃ m ≥ N, ε ≤ |a m - a n|
  have hε3 : ∀ (N : ℕ), ∃ n ≥ N, ∃ m ≥ n, ε ≤ |a m - a n| := by
    intro N
    -- N : ℕ
    -- ⊢ ∃ n ≥ N, ∃ m ≥ n, ε ≤ |a m - a n|
    obtain ⟨n, hn, m, hm, h⟩ := hε2 N
    -- n : ℕ
    -- hn : n ≥ N
    -- m : ℕ
    -- hm : m ≥ N
    -- h : ε ≤ |a m - a n|
    rcases le_total n m with hnm1 | hmn2
    · -- hnm1 : n ≤ m
      exact ⟨n, hn, m, hnm1, h⟩
    · -- hmn2 : m ≤ n
      have h' : ε ≤ |a n - a m| := by rwa [abs_sub_comm]
      exact ⟨m, hm, n, hmn2, h'⟩
  exact ⟨ε, hε1, hε3⟩

-- 2ª demostración
-- ===============

public lemma exists_ordered_gap_of_not_isCauchy
  (hC : ¬ IsCauchy a)
  : ∃ ε : X, 0 < ε ∧ ∀ (N : ℕ), ∃ n ≥ N, ∃ m ≥ n, ε ≤ |a m - a n| :=
by
  unfold IsCauchy at hC
  -- hC : ¬∀ (ε : X), 0 < ε → ∃ N, ∀ n ≥ N, ∀ m ≥ N, |a m - a n| < ε
  push Not at hC
  -- hC : ∃ ε, 0 < ε ∧ ∀ (N : ℕ), ∃ n ≥ N, ∃ m ≥ N, ε ≤ |a m - a n|
  obtain ⟨ε, hε1, hε2⟩ := hC
  -- ε : X
  -- hε1 : 0 < ε
  -- hε2 : ∀ (N : ℕ), ∃ n ≥ N, ∃ m ≥ N, ε ≤ |a m - a n|
  refine ⟨ε, hε1, fun N => ?_⟩
  -- N : ℕ
  -- ⊢ ∃ n ≥ N, ∃ m ≥ n, ε ≤ |a m - a n|
  obtain ⟨n, hn, m, hm, h⟩ := hε2 N
  -- n : ℕ
  -- hn : n ≥ N
  -- m : ℕ
  -- hm : m ≥ N
  -- h : ε ≤ |a m - a n|
  rcases le_total n m with hnm1 | hmn2
  · -- hnm1 : n ≤ m
    exact ⟨n, hn, m, hnm1, h⟩
  · -- hmn2 : m ≤ n
    exact ⟨m, hm, n, hmn2, by rwa [abs_sub_comm]⟩
