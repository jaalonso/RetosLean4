-- Reto_22.lean
-- Subsucesiones con límites distintos implican no convergencia.
-- Sevilla, 5-octubre-2026
-- ---------------------------------------------------------------

-- ---------------------------------------------------------------
-- El reto de esta semana consiste en demostrar en Lean 4 que si
-- una sucesión tiene dos subsucesiones con límites distintos,
-- entonces la sucesión no es convergente. Para ello, completar la
-- siguiente teoría:
--    -- a converge a L
--    def LimSuc (a : ℕ → ℝ) (L : ℝ) : Prop :=
--      ∀ ε > 0, ∃ k : ℕ, ∀ n ≥ k, |a n - L| < ε
--
--    -- La sucesión a es convergente
--    def SucConvergente (a : ℕ → ℝ) : Prop :=
--      ∃ L, LimSuc a L
--
--    -- φ es una función de extracción.
--    def extraccion (φ : ℕ → ℕ) : Prop :=
--      StrictMono φ
--
--    -- b es una subsucesión de a.
--    def subsucesion (b a : ℕ → ℝ) : Prop :=
--      ∃ φ, extraccion φ ∧ b = a ∘ φ
--
--    variable {a b₁ b₂ : ℕ → ℝ}
--    variable {L L₁ L₂ M : ℝ}
--
--    example
--      (hb₁ : subsucesion b₁ a)
--      (hL₁ : LimSuc b₁ L₁)
--      (hb₂ : subsucesion b₂ a)
--      (hL₂ : LimSuc b₂ L₂)
--      (h : L₁ ≠ L₂)
--      : ¬SucConvergente a :=
--    by sorry
-- ---------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- La demostración se hará usando dos lemas demostrados en retos
-- anteriores:
-- + El lema limite_subsucesion (del Reto 21): toda subsucesión de
--   una sucesión convergente converge al mismo límite que la
--   sucesión.
-- + El lema unicidad_limite (del Reto 9): si una sucesión aₙ
--   converge tanto a L como a M, entonces L = M.
--
-- Para la demostración del reto, supongamos que la sucesión a es
-- convergente. Entonces, por el lema limite_subsucesion se tiene
-- que b₁ converge a L y, por el lema unicidad_limite se tiene que
--    L₁ = L
-- Análogamente se tiene que
--    L₂ = L
-- Por tanto L₁ = L₂ en contradicción con la hipótesis L₁ ≠ L₂.

-- Demostraciones en Lean 4
-- ========================

import Mathlib.Tactic
import RetosLean4.Defs -- LimSuc, SucConvergente, extraccion, subsucesion
import RetosLean4.Reto_9 -- unicidad_limite
import RetosLean4.Reto_21 -- limite_subsucesion

variable {a b₁ b₂ : ℕ → ℝ}
variable {L L₁ L₂ M : ℝ}

-- 1ª demostración
-- ===============

example
  (hb₁ : subsucesion b₁ a)
  (hL₁ : LimSuc b₁ L₁)
  (hb₂ : subsucesion b₂ a)
  (hL₂ : LimSuc b₂ L₂)
  (h : L₁ ≠ L₂)
  : ¬SucConvergente a :=
by
  intro h1
  -- h1 : SucConvergente a
  -- ⊢ False
  obtain ⟨L, hL⟩ := h1
  -- L : ℝ
  -- hL : LimSuc a L
  apply h
  -- ⊢ L₁ = L₂
  have h2 : LimSuc b₁ L := limite_subsucesion hb₁ hL
  have h3 : LimSuc b₂ L := limite_subsucesion hb₂ hL
  calc L₁ = L  := unicidad_limite hL₁ h2
       _  = L₂ := unicidad_limite h3 hL₂

-- 2ª demostración
-- ===============

example
  (hb₁ : subsucesion b₁ a)
  (hL₁ : LimSuc b₁ L₁)
  (hb₂ : subsucesion b₂ a)
  (hL₂ : LimSuc b₂ L₂)
  (h : L₁ ≠ L₂)
  : ¬SucConvergente a :=
by
  rintro ⟨L, hL⟩
  -- L : ℝ
  -- hL : LimSuc a L
  -- ⊢ False
  exact h (Eq.trans
           (unicidad_limite hL₁ (limite_subsucesion hb₁ hL))
           (unicidad_limite (limite_subsucesion hb₂ hL) hL₂))

-- 3ª demostración
-- ===============

theorem CS_no_convergencia
  (hb₁ : subsucesion b₁ a)
  (hL₁ : LimSuc b₁ L₁)
  (hb₂ : subsucesion b₂ a)
  (hL₂ : LimSuc b₂ L₂)
  (h : L₁ ≠ L₂)
  : ¬SucConvergente a :=
by
  rintro ⟨L, hL⟩
  -- L : ℝ
  -- hL : LimSuc a L
  -- ⊢ False
  exact h ((unicidad_limite hL₁ (limite_subsucesion hb₁ hL)).trans
           (unicidad_limite (limite_subsucesion hb₂ hL) hL₂))
