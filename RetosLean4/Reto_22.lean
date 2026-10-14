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
--    def SeqLim (a : ℕ → ℝ) (L : ℝ) : Prop :=
--      ∀ ε > 0, ∃ k : ℕ, ∀ n ≥ k, |a n - L| < ε
--
--    -- La sucesión a es convergente
--    def SeqConv (a : ℕ → ℝ) : Prop :=
--      ∃ L, SeqLim a L
--
--    -- φ es una función de extracción.
--    def IsExtraction (φ : ℕ → ℕ) : Prop :=
--      StrictMono φ
--
--    -- b es una subsucesión de a.
--    def Subseq (b a : ℕ → ℝ) : Prop :=
--      ∃ φ, IsExtraction φ ∧ b = a ∘ φ
--
--    variable {a b₁ b₂ : ℕ → ℝ}
--    variable {L L₁ L₂ : ℝ}
--
--    example
--      (hb₁ : Subseq b₁ a)
--      (hL₁ : SeqLim b₁ L₁)
--      (hb₂ : Subseq b₂ a)
--      (hL₂ : SeqLim b₂ L₂)
--      (h : L₁ ≠ L₂)
--      : ¬SeqConv a :=
--    by sorry
-- ---------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- La demostración se hará usando dos lemas demostrados en retos
-- anteriores:
-- + El lema seqLim_of_subseq (del Reto 21): toda subsucesión de
--   una sucesión convergente converge al mismo límite que la
--   sucesión.
-- + El lema seqLim_unique (del Reto 9): si una sucesión aₙ
--   converge tanto a L como a M, entonces L = M.
--
-- Para la demostración del reto, supongamos que la sucesión a es
-- convergente. Entonces, por el lema seqLim_of_subseq se tiene
-- que b₁ converge a L y, por el lema seqLim_unique se tiene que
--    L₁ = L
-- Análogamente se tiene que
--    L₂ = L
-- Por tanto L₁ = L₂ en contradicción con la hipótesis L₁ ≠ L₂.

-- Demostraciones en Lean 4
-- ========================

import Mathlib.Tactic
import RetosLean4.Defs -- SeqLim, SeqConv, IsExtraction, Subseq
import RetosLean4.Reto_9 -- seqLim_unique
import RetosLean4.Reto_21 -- seqLim_of_subseq

variable {a b₁ b₂ : ℕ → ℝ}
variable {L L₁ L₂ : ℝ}

-- 1ª demostración
-- ===============

example
  (hb₁ : Subseq b₁ a)
  (hL₁ : SeqLim b₁ L₁)
  (hb₂ : Subseq b₂ a)
  (hL₂ : SeqLim b₂ L₂)
  (h : L₁ ≠ L₂)
  : ¬SeqConv a :=
by
  intro h1
  -- h1 : SeqConv a
  -- ⊢ False
  obtain ⟨L, hL⟩ := h1
  -- L : ℝ
  -- hL : SeqLim a L
  apply h
  -- ⊢ L₁ = L₂
  have h2 : SeqLim b₁ L := seqLim_of_subseq hb₁ hL
  have h3 : SeqLim b₂ L := seqLim_of_subseq hb₂ hL
  calc L₁ = L  := seqLim_unique hL₁ h2
       _  = L₂ := seqLim_unique h3 hL₂

-- 2ª demostración
-- ===============

example
  (hb₁ : Subseq b₁ a)
  (hL₁ : SeqLim b₁ L₁)
  (hb₂ : Subseq b₂ a)
  (hL₂ : SeqLim b₂ L₂)
  (h : L₁ ≠ L₂)
  : ¬SeqConv a :=
by
  rintro ⟨L, hL⟩
  -- L : ℝ
  -- hL : SeqLim a L
  -- ⊢ False
  exact h (Eq.trans
           (seqLim_unique hL₁ (seqLim_of_subseq hb₁ hL))
           (seqLim_unique (seqLim_of_subseq hb₂ hL) hL₂))

-- 3ª demostración
-- ===============

theorem not_seqConv_of_subseq_seqLim_ne
  (hb₁ : Subseq b₁ a)
  (hL₁ : SeqLim b₁ L₁)
  (hb₂ : Subseq b₂ a)
  (hL₂ : SeqLim b₂ L₂)
  (h : L₁ ≠ L₂)
  : ¬SeqConv a :=
by
  rintro ⟨L, hL⟩
  -- L : ℝ
  -- hL : SeqLim a L
  -- ⊢ False
  exact h ((seqLim_unique hL₁ (seqLim_of_subseq hb₁ hL)).trans
           (seqLim_unique (seqLim_of_subseq hb₂ hL) hL₂))
