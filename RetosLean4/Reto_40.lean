-- Reto_40.lean
-- La sucesión 1/n es de Cauchy, pero no es monótona ni antítona.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 13-noviembre-2026
-- ---------------------------------------------------------------

-- ---------------------------------------------------------------
-- Demostrar que la sucesión 1/n es de Cauchy, pero no es monótona
-- ni antítona (teniendo en cuenta que, en Lean, 1/0 = 0).
-- ---------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Sea a la sucesión definida por a(n) = 1/n, para todo n ∈ ℕ.
-- Hay que demostrar tres propiedades:
--    (1) a es de Cauchy,
--    (2) a no es monótona,
--    (3) a no es antítona.
--
-- Prueba de (1). Por el reto 1, la sucesión a converge a 0, luego
-- es convergente. Por el reto 19, toda sucesión convergente es de
-- Cauchy. Por tanto, a es de Cauchy.
--
-- Prueba de (2). Para ver que a no es monótona basta ver que
-- 1 ≤ 2 pero
--    a(2) = 1/2 < 1 = 1/1 = a(1).
--
-- Prueba de (3). Para ver que a no es antítona basta ver que
-- 0 ≤ 1 pero
--    a(0) = 1/0 = 0 < 1 = 1/1 = a(1)
-- (en donde hemos usado que, en Lean, la división por cero está
-- definida y 1/0 = 0).

-- Demostraciones en Lean 4
-- ========================

module

import Mathlib.Tactic
import RetosLean4.Defs -- IsCauchy
import RetosLean4.Reto_19 -- isCauchy_of_SeqConv
import RetosLean4.Reto_1 -- seqLim_zero_of_eq_one_div

variable {a : ℕ → ℝ}

-- 1ª demostración
-- ===============

example
  (ha : ∀ n, a n = 1 / n)
  : IsCauchy a ∧ ¬ Monotone a ∧ ¬ Antitone a :=
by
  split_ands
  · -- ⊢ IsCauchy a
    apply isCauchy_of_SeqConv
    -- ⊢ SeqConv a
    use 0
    -- ⊢ SeqLim a 0
    apply seqLim_zero_of_eq_one_div a ha
  · -- ⊢ ¬Monotone a
    unfold Monotone
    -- ⊢ ¬∀ ⦃a_1 b : ℕ⦄, a_1 ≤ b → a a_1 ≤ a b
    push Not
    -- ⊢ ∃ a_1 b, a_1 ≤ b ∧ a b < a a_1
    use 1, 2
    -- ⊢ 1 ≤ 2 ∧ a 2 < a 1
    constructor
    · -- ⊢ 1 ≤ 2
      norm_num
    · -- a 2 < a 1
      calc a 2
           = 1 / (2 : ℝ) := by norm_num [ha]
         _ < 1 / (1 : ℝ) := by norm_num
         _ = a 1         := by norm_num [ha]
  · -- ⊢ ¬Antitone a
    unfold Antitone
    -- ⊢ ¬∀ ⦃a_1 b : ℕ⦄, a_1 ≤ b → a b ≤ a a_1
    push Not
    -- ⊢ ∃ a_1 b, a_1 ≤ b ∧ a a_1 < a b
    use 0, 1
    -- ⊢ 0 ≤ 1 ∧ a 0 < a 1
    constructor
    · -- ⊢ 0 ≤ 1
      norm_num
    · -- ⊢ a 0 < a 1
      calc a 0
           = 1 / 0 := by simp [ha]
         _ = 0     := by simp
         _ < 1 / 1 := by norm_num
         _ = a 1   := by simp [ha]

-- 2ª demostración
-- ===============

example
  (ha : ∀ n, a n = 1 / n)
  : IsCauchy a ∧ ¬ Monotone a ∧ ¬ Antitone a :=
by
  split_ands
  · -- ⊢ IsCauchy a
    exact isCauchy_of_SeqConv ⟨0, seqLim_zero_of_eq_one_div a ha⟩
  · -- ⊢ ¬Monotone a
    unfold Monotone
    -- ⊢ ¬∀ ⦃a_1 b : ℕ⦄, a_1 ≤ b → a a_1 ≤ a b
    push Not
    -- ⊢ ∃ a_1 b, a_1 ≤ b ∧ a b < a a_1
    exact ⟨1, 2, by norm_num, by norm_num [ha]⟩
  · -- ⊢ ¬Antitone a
    unfold Antitone
    -- ⊢ ¬∀ ⦃a_1 b : ℕ⦄, a_1 ≤ b → a b ≤ a a_1
    push Not
    -- ⊢ ∃ a_1 b, a_1 ≤ b ∧ a a_1 < a b
    exact ⟨0, 1, by norm_num, by norm_num [ha]⟩

-- 3ª demostración
-- ===============

example
  (ha : ∀ n, a n = 1 / n)
  : IsCauchy a ∧ ¬ Monotone a ∧ ¬ Antitone a :=
by
  refine ⟨isCauchy_of_SeqConv ⟨0, seqLim_zero_of_eq_one_div a ha⟩, ?_, ?_⟩
  · -- ⊢ ¬Monotone a
    intro h
    -- h : Monotone a
    -- ⊢ False
    have ha12 : a 1 ≤ a 2 := h (show 1 ≤ 2 by norm_num)
    norm_num [ha] at ha12
  · -- ⊢ ¬Antitone a
    intro h
    -- h : Antitone a
    -- ⊢ False
    have ha10 : a 1 ≤ a 0 := h (show 0 ≤ 1 by norm_num)
    norm_num [ha] at ha10

-- 4ª demostración
-- ===============

example
  (ha : ∀ n, a n = 1 / n)
  : IsCauchy a ∧ ¬ Monotone a ∧ ¬ Antitone a :=
by
  have h0 : a 0 = 0 :=
    calc a 0
         = 1 / ((0 : ℕ) : ℝ) := ha 0
       _ = 1 / 0             := by rw [Nat.cast_zero]
       _ = 0                 := div_zero 1
  have h1 : a 1 = 1 :=
    calc a 1
         = 1 / ((1 : ℕ) : ℝ) := ha 1
       _ = 1 / 1             := by rw [Nat.cast_one]
       _ = 1                 := div_one 1
  have h2 : a 2 = 1 / 2 :=
    calc a 2
         = 1 / ((2 : ℕ) : ℝ) := ha 2
       _ = 1 / 2             := by rw [Nat.cast_ofNat]
  split_ands
  · -- ⊢ IsCauchy a
    apply isCauchy_of_SeqConv
    -- ⊢ SeqConv a
    use 0
    -- ⊢ SeqLim a 0
    apply seqLim_zero_of_eq_one_div a ha
  · -- ⊢ ¬Monotone a
    unfold Monotone
    -- ⊢ ¬∀ ⦃a_1 b : ℕ⦄, a_1 ≤ b → a a_1 ≤ a b
    push Not
    -- ⊢ ∃ a_1 b, a_1 ≤ b ∧ a b < a a_1
    use 1, 2
    -- ⊢ 1 ≤ 2 ∧ a 2 < a 1
    constructor
    · -- ⊢ 1 ≤ 2
      norm_num
    · -- a 2 < a 1
      calc a 2
           = 1 / 2       := h2
         _ < 1 / 1       := one_div_lt_one_div_of_lt zero_lt_one one_lt_two
         _ = 1           := div_one 1
         _ = a 1         := h1.symm
  · -- ⊢ ¬Antitone a
    unfold Antitone
    -- ⊢ ¬∀ ⦃a_1 b : ℕ⦄, a_1 ≤ b → a b ≤ a a_1
    push Not
    -- ⊢ ∃ a_1 b, a_1 ≤ b ∧ a a_1 < a b
    use 0, 1
    -- ⊢ 0 ≤ 1 ∧ a 0 < a 1
    constructor
    · -- ⊢ 0 ≤ 1
      norm_num
    · -- ⊢ a 0 < a 1
      calc a 0
           = 0   := h0
         _ < 1   := zero_lt_one
         _ = a 1 := h1.symm
