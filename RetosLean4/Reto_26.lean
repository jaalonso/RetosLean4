-- Reto_26.lean (Limite_cero_por_acotada.lean)
-- Producto de una sucesión de límite cero por una acotada.
-- Sevilla, 25-octubre-2026
-- ---------------------------------------------------------------

-- ---------------------------------------------------------------
-- Demostrar que si la sucesión aₙ converge a 0 y la sucesión
-- bₙ está acotada (no necesariamente es convergente), entonces la
-- sucesión aₙ·bₙ converge a 0.
--
-- Para ello, completar la siguiente teoría
--    import Mathlib.Basic.Real.Basic
--    import Mathlib.Tactic
--
--    def SeqLim (a : ℕ → ℝ) (L : ℝ) : Prop :=
--      ∀ ε > 0, ∃ k : ℕ, ∀ n ≥ k, |a n - L| < ε
--
--    def SeqBdd (a : ℕ → ℝ) : Prop :=
--      ∃ M > 0, ∀ n, |a n| ≤ M
--
--    variable (a b : ℕ → ℝ)
--
--    example
--      (ha : SeqLim a 0)
--      (hb : SeqBdd b)
--      : SeqLim (a * b) 0 :=
--    by sorry
-- ---------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Sea ε ∈ ℝ tal que
--    ε > 0                                                     (1)
-- Tenemos que demostrar que existe un k ∈ ℕ tal que
--    ∀ n ≥ k, |aₙ·bₙ - 0| < ε                                  (2)
-- Por estar bₙ acotada, existe M ∈ ℝ tal que,
--    M > 0                                                     (3)
--    ∀ n, |bₙ| ≤ M.                                            (4)
-- Por (1) y (3),
--    ε/M > 0
-- y, como aₙ converge a 0, existe k ∈ ℕ tal que,
--    ∀ n ≥ k, |aₙ| < ε/M.                                      (5)
-- Veamos que con ese k se cumple (2). Para ello, sea n ∈ ℕ tal
-- que
--    n ≥ k                                                     (6)
-- Entonces
--    |aₙ·bₙ - 0| = |aₙ·bₙ|
--                = |aₙ|·|bₙ|
--                ≤ |aₙ|·M      [por (4)]
--                < (ε/M)·M     [por (5), (6) y (3)]
--                = ε
-- Por tanto, aₙ·bₙ converge a 0.

-- Demostraciones con Lean4
-- ========================

module

import Mathlib.Basic.Real.Basic
import Mathlib.Tactic
public import RetosLean4.Defs -- SeqLim, SeqBdd

/-
def SeqLim (a : ℕ → ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ k : ℕ, ∀ n ≥ k, |a n - L| < ε

def SeqBdd (a : ℕ → ℝ) : Prop :=
  ∃ M > 0, ∀ n, |a n| ≤ M
-/

variable (a b : ℕ → ℝ)

-- 1ª demostración
-- ===============

example
  (ha : SeqLim a 0)
  (hb : SeqBdd b)
  : SeqLim (a * b) 0 :=
by
  intro ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ k, ∀ n ≥ k, |(a * b) n - 0| < ε
  obtain ⟨M, hM, hbM⟩ := hb
  -- M : ℝ
  -- hM : M > 0
  -- hbM : ∀ (n : ℕ), |b n| ≤ M
  obtain ⟨k, hk⟩ := ha (ε / M) (by positivity)
  -- k : ℕ
  -- hk : ∀ n ≥ k, |a n - 0| < ε / M
  use k
  -- ⊢ ∀ n ≥ k, |(a * b) n - 0| < ε
  intro n hn
  -- n : ℕ
  -- hn : n ≥ k
  -- ⊢ |(a * b) n - 0| < ε
  have h1 : |a n| < ε / M := by grind
  calc |(a * b) n - 0|
       = |(a * b) n|    := by grind
     _ = |a n * b n|    := by rfl
     _ = |a n| * |b n|  := by grind
     _ ≤ |a n| * M      := by bound
     _ < ε / M * M      := by bound
     _ = ε              := by grind

-- 2ª demostración
-- ===============

example
  (ha : SeqLim a 0)
  (hb : SeqBdd b)
  : SeqLim (a * b) 0 :=
by
  intro ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ k, ∀ n ≥ k, |(a * b) n - 0| < ε
  obtain ⟨M, hM, hbM⟩ := hb
  -- M : ℝ
  -- hM : M > 0
  -- hbM : ∀ (n : ℕ), |b n| ≤ M
  obtain ⟨k, hk⟩ := ha (ε / M) (by positivity)
  -- k : ℕ
  -- hk : ∀ n ≥ k, |a n - 0| < ε / M
  use k
  -- ⊢ ∀ n ≥ k, |(a * b) n - 0| < ε
  intro n hn
  -- n : ℕ
  -- hn : n ≥ k
  -- ⊢ |(a * b) n - 0| < ε
  have h1 : |a n| < ε / M := by
    calc |a n|
         = |a n - 0| := by rw [sub_zero]
       _ < ε / M     := hk n hn
  calc |(a * b) n - 0|
       = |(a * b) n|    := by rw [sub_zero]
     _ = |a n * b n|    := by rw [Pi.mul_apply]
     _ = |a n| * |b n|  := by rw [abs_mul]
     _ ≤ |a n| * M      := by bound
     _ < ε / M * M      := by bound
     _ = ε              := by field_simp

-- 3ª demostración
-- ===============

example
  (ha : SeqLim a 0)
  (hb : SeqBdd b)
  : SeqLim (a * b) 0 :=
by
  intro ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ k, ∀ n ≥ k, |(a * b) n - 0| < ε
  obtain ⟨M, hM, hbM⟩ := hb
  -- M : ℝ
  -- hM : M > 0
  -- hbM : ∀ (n : ℕ), |b n| ≤ M
  obtain ⟨k, hk⟩ := ha (ε / M) (div_pos hε hM)
  -- k : ℕ
  -- hk : ∀ n ≥ k, |a n - 0| < ε / M
  use k
  -- ⊢ ∀ n ≥ k, |(a * b) n - 0| < ε
  intro n hn
  -- n : ℕ
  -- hn : n ≥ k
  -- ⊢ |(a * b) n - 0| < ε
  have h1 : |a n| < ε / M := by
    calc |a n|
         = |a n - 0| := by rw [sub_zero]
       _ < ε / M     := hk n hn
  calc |(a * b) n - 0|
       = |(a * b) n|    := by congr; exact sub_zero ((a * b) n)
     _ = |a n * b n|    := by congr
     _ = |a n| * |b n|  := abs_mul (a n) (b n)
     _ ≤ |a n| * M      := by rel [hbM n]
     _ < ε / M * M      := by rel [h1]
     _ = ε              := div_mul_cancel₀ ε hM.ne'

-- 4ª demostración
-- ===============

example
  (ha : SeqLim a 0)
  (hb : SeqBdd b)
  : SeqLim (a * b) 0 :=
by
  intro ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ k, ∀ n ≥ k, |(a * b) n - 0| < ε
  obtain ⟨M, hM, hbM⟩ := hb
  -- M : ℝ
  -- hM : M > 0
  -- hbM : ∀ (n : ℕ), |b n| ≤ M
  obtain ⟨k, hk⟩ := ha (ε / M) (div_pos hε hM)
  -- k : ℕ
  -- hk : ∀ n ≥ k, |a n - 0| < ε / M
  use k
  -- ⊢ ∀ n ≥ k, |(a * b) n - 0| < ε
  intro n hn
  -- n : ℕ
  -- hn : n ≥ k
  -- ⊢ |(a * b) n - 0| < ε
  have h1 : |a n| < ε / M := by
    calc |a n|
         = |a n - 0| := congrArg abs (sub_zero (a n)).symm
       _ < ε / M     := hk n hn
  calc |(a * b) n - 0|
       = |(a * b) n|    := congrArg abs (sub_zero ((a * b) n))
     _ = |a n * b n|    := congrArg abs (Pi.mul_apply a b n)
     _ = |a n| * |b n|  := abs_mul (a n) (b n)
     _ ≤ |a n| * M      := mul_le_mul_of_nonneg_left (hbM n) (abs_nonneg (a n))
     _ < ε / M * M      := mul_lt_mul_of_pos_right h1 hM
     _ = ε              := div_mul_cancel₀ ε hM.ne'
