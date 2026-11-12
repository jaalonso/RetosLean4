-- Reto_39.lean
-- Las sucesiones antítonas y acotadas inferiormente son de Cauchy.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 12-noviembre-2026
-- ---------------------------------------------------------------

-- ---------------------------------------------------------------
-- Demostrar que las sucesiones antítonas y acotadas inferiormente
-- son sucesiones de Cauchy.
-- ---------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Sea a antítona y acotada inferiormente. Entonces existe un M
-- tal que
--    ∀ n, M ≤ a(n)                                              (1)
-- Consideremos la sucesión -a. Veamos que es monótona y acotada
-- superiormente:
-- + Monótona: si m ≤ n, entonces a(n) ≤ a(m) por ser a antítona
--   y, por tanto, -a(m) ≤ -a(n).
-- + Acotada superiormente: por (1), -a(n) ≤ -M para todo n.
--
-- Por el Reto 37, -a es de Cauchy. Por el Reto 38, -(-a) también
-- lo es. Como -(-a) = a, se concluye que a es de Cauchy.

-- Demostraciones en Lean 4
-- ========================

module

import Mathlib.Tactic
import RetosLean4.Defs -- IsCauchy, SeqBddBelow
import RetosLean4.Reto_37 -- isCauchy_of_mono_bddAbove
import RetosLean4.Reto_38 -- isCauchy_neg

variable {X : Type*} [Field X]
                     [LinearOrder X]
                     [IsStrictOrderedRing X]
                     [Archimedean X]
variable {a : ℕ → X}

-- 1ª demostración
-- ===============

example
  (ha1 : Antitone a)
  (ha2 : SeqBddBelow a)
  : IsCauchy a :=
by
  obtain ⟨M, hM⟩ := ha2
  -- M : X
  -- hM : ∀ (n : ℕ), M ≤ a n
  have hb1 : Monotone (-a) := Antitone.neg ha1
  have hb2 : SeqBddAbove (-a) := by
    refine ⟨-M, fun n => ?_⟩
    -- n : ℕ
    -- ⊢ (-a) n ≤ -M
    simpa using hM n
  have hb3 : IsCauchy (-a) := isCauchy_of_mono_bddAbove hb1 hb2
  have hb4 : IsCauchy (-(-a)) := isCauchy_neg hb3
  simpa using hb4

-- 2ª demostración
-- ===============

example
  (ha1 : Antitone a)
  (ha2 : SeqBddBelow a)
  : IsCauchy a :=
by
  obtain ⟨M, hM⟩ := ha2
  -- M : X
  -- hM : ∀ (n : ℕ), M ≤ a n
  have hb1 : Monotone (-a) := by
    intro m n h
    -- m n : ℕ
    -- h : m ≤ n
    -- ⊢ (-a) m ≤ (-a) n
    have h' : a n ≤ a m := ha1 h
    calc (-a) m
         = -(a m) := rfl
       _ ≤ -(a n) := neg_le_neg_iff.mpr h'
       _ = (-a) n := rfl
  have hb2 : SeqBddAbove (-a) := by
    refine ⟨-M, fun n => ?_⟩
    -- n : ℕ
    -- ⊢ (-a) n ≤ -M
    calc (-a) n
         = -(a n) := rfl
       _ ≤ -M     := neg_le_neg_iff.mpr (hM n)
  have hb3 : IsCauchy (-a) := isCauchy_of_mono_bddAbove hb1 hb2
  have hb4 : IsCauchy (-(-a)) := isCauchy_neg hb3
  have h5 : (-(-a)) = a := neg_neg a
  rw [h5] at hb4
  -- hb4 : IsCauchy a
  exact hb4
