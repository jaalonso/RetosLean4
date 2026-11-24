-- Reto_43.lean
-- Teorema de Bolzano-Weierstrass: Toda sucesión acotada tiene una
--   subsucesión de Cauchy.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 23-noviembre-2026
-- ---------------------------------------------------------------

-- ---------------------------------------------------------------
-- Demostrar el teorema de Bolzano-Weierstrass: Toda sucesión
-- acotada tiene una subsucesión de Cauchy.
-- ---------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Sea a una sucesión acotada. Entonces, existe M > 0 tal que
--    ∀ n, |a(n)| ≤ M.
-- En particular,
--    ∀ n, -M ≤ a(n) ≤ M.                                       (1)
--
-- Se usarán los siguientes lemas demostrados en retos anteriores:
-- + L1 (en el Reto 37): Si una sucesión es creciente (en sentido
--   amplio) y está acotada superiormente, entonces es de Cauchy.
-- + L2 (en el Reto 39): Si una sucesión es decreciente (en sentido
--   amplio) y está acotada inferiormente, entonces es de Cauchy.
-- + L3 (en el Reto 41): Si a no tiene infinitos picos, entonces a
--   tiene una subsucesión creciente.
-- + L4 (en el Reto 42): Si a tiene infinitos picos, entonces a
--   tiene una subsucesión decreciente.
--
-- Previamente, se prueba que toda subsucesión de a está acotada por
-- -M y M; es decir, que
--    Si b es una subsucesión de a, entonces
--    ∀ n, -M ≤ b(n) ≤ M.                                       (2)
-- En efecto, como b es subsucesión de a, existe una función de
-- extracción φ tal que
--    b = a ∘ φ.
-- Sea n ∈ ℕ. Entonces, b(n) = a(φ(n)) y, por (1),
--    -M ≤ a(φ(n)) ≤ M.
-- Por tanto, -M ≤ b(n) ≤ M.
--
-- Se distinguen dos casos según que a tenga infinitos picos o no.
--
-- Caso 1: Supongamos que a tiene infinitos picos.
-- Por el lema L4, existe una subsucesión b de a que es
-- decreciente. Por (2), -M es una cota inferior de b. Por tanto,
-- por el lema L2, b es de Cauchy.
--
-- Caso 2: Supongamos que a no tiene infinitos picos.
-- Por el lema L3, existe una subsucesión b de a que es creciente.
-- Por (2), M es una cota superior de b. Por tanto, por el lema L1,
-- b es de Cauchy.
--
-- En ambos casos, a tiene una subsucesión de Cauchy.

-- Demostraciones en Lean 4
-- ========================

module

import Mathlib.Tactic
import RetosLean4.Defs    -- SeqBdd, Subseq, HasInfinitePeaks,
                          -- IsCauchy, SeqBddAbove, SeqBddBelow
import RetosLean4.Reto_37 -- IsCauchy_of_Monotone_of_SeqBddAbove
import RetosLean4.Reto_39 -- IsCauchy_of_Antitone_of_SeqBddBelow
import RetosLean4.Reto_41 -- MonotoneSubseq_of_NotHasInfinitePeaks
import RetosLean4.Reto_42 -- AntitoneSubseq_of_HasInfinitePeaks

variable {X : Type*} [Field X]
                     [LinearOrder X]
                     [IsStrictOrderedRing X]
                     [Archimedean X]
variable {a : ℕ → X}

-- 1ª demostración
-- ===============

example
  (ha : SeqBdd a)
  : ∃ b, Subseq b a ∧ IsCauchy b :=
by
  obtain ⟨M, -, hM⟩ := ha
  -- M : X
  -- hM : ∀ (n : ℕ), |a n| ≤ M
  by_cases hPeaks : HasInfinitePeaks a
  · -- hPeaks : HasInfinitePeaks a
    obtain ⟨b, hb1, hb2⟩ := AntitoneSubseq_of_HasInfinitePeaks hPeaks
    -- b : ℕ → X
    -- hb1 : Subseq b a
    -- hb2 : Antitone b
    use b
    -- ⊢ Subseq b a ∧ IsCauchy b
    constructor
    · -- ⊢ Subseq b a
      exact hb1
    · -- ⊢ IsCauchy b
      apply IsCauchy_of_Antitone_of_SeqBddBelow hb2
      -- ⊢ SeqBddBelow b
      use -M
      -- ⊢ ∀ (n : ℕ), -M ≤ b n
      obtain ⟨φ, -, rfl⟩ := hb1
      -- φ : ℕ → ℕ
      -- hb2 : Antitone (a ∘ φ)
      -- ⊢ ∀ (n : ℕ), -M ≤ (a ∘ φ) n
      intro n
      -- n : ℕ
      -- ⊢ -M ≤ (a ∘ φ) n
      exact (abs_le.1 (hM (φ n))).1
  · -- hPeaks : ¬HasInfinitePeaks a
    obtain ⟨b, hb1, hb2⟩ := MonotoneSubseq_of_NotHasInfinitePeaks hPeaks
    -- b : ℕ → X
    -- hb1 : Subseq b a
    -- hb2 : Monotone b
    use b
    -- ⊢ Subseq b a ∧ IsCauchy b
    constructor
    · -- ⊢ Subseq b a
      exact hb1
    · -- ⊢ IsCauchy b
      apply IsCauchy_of_Monotone_of_SeqBddAbove hb2
      -- ⊢ SeqBddAbove b
      use M
      -- ⊢ ∀ (n : ℕ), b n ≤ M
      obtain ⟨φ, -, rfl⟩ := hb1
      -- φ : ℕ → ℕ
      -- hb2 : Monotone (a ∘ φ)
      -- ⊢ ∀ (n : ℕ), (a ∘ φ) n ≤ M
      intro n
      -- n : ℕ
      -- ⊢ (a ∘ φ) n ≤ M
      exact (abs_le.1 (hM (φ n))).2

-- 2ª demostración
-- ===============

example
  (ha : SeqBdd a)
  : ∃ b, Subseq b a ∧ IsCauchy b :=
by
  obtain ⟨M, -, hM⟩ := ha
  -- M : X
  -- hM : ∀ (n : ℕ), |a n| ≤ M
  by_cases hPeaks : HasInfinitePeaks a
  · -- hPeaks : HasInfinitePeaks a
    obtain ⟨b, hb1, hb2⟩ := AntitoneSubseq_of_HasInfinitePeaks hPeaks
    -- b : ℕ → X
    -- hb1 : Subseq b a
    -- hb2 : Antitone b
    refine ⟨b, hb1, IsCauchy_of_Antitone_of_SeqBddBelow hb2 ⟨-M, ?_⟩⟩
    -- ⊢ ∀ (n : ℕ), -M ≤ b n
    obtain ⟨φ, -, rfl⟩ := hb1
    -- φ : ℕ → ℕ
    -- hb2 : Antitone (a ∘ φ)
    -- ⊢ ∀ (n : ℕ), -M ≤ (a ∘ φ) n
    exact fun n => (abs_le.1 (hM (φ n))).1
  · -- hPeaks : ¬HasInfinitePeaks a
    obtain ⟨b, hb1, hb2⟩ := MonotoneSubseq_of_NotHasInfinitePeaks hPeaks
    -- b : ℕ → X
    -- hb1 : Subseq b a
    -- hb2 : Monotone b
    refine ⟨b, hb1, IsCauchy_of_Monotone_of_SeqBddAbove hb2 ⟨M, ?_⟩⟩
    -- ⊢ ∀ (n : ℕ), b n ≤ M
    obtain ⟨φ, -, rfl⟩ := hb1
    -- φ : ℕ → ℕ
    -- hb2 : Monotone (a ∘ φ)
    -- ⊢ ∀ (n : ℕ), (a ∘ φ) n ≤ M
    exact fun n => (abs_le.1 (hM (φ n))).2

-- 3ª demostración
-- ===============

example
  (ha : SeqBdd a)
  : ∃ b, Subseq b a ∧ IsCauchy b :=
by
  obtain ⟨M, -, hM⟩ := ha
  -- M : X
  -- hM : ∀ (n : ℕ), |a n| ≤ M
  have h1 : ∀ b, Subseq b a → ∀ n, -M ≤ b n ∧ b n ≤ M := by
    rintro b ⟨φ, -, rfl⟩ n
    -- φ : ℕ → ℕ
    -- n : ℕ
    -- ⊢ -M ≤ (a ∘ φ) n ∧ (a ∘ φ) n ≤ M
    exact abs_le.1 (hM (φ n))
  by_cases hPeaks : HasInfinitePeaks a
  · -- hPeaks : HasInfinitePeaks a
    obtain ⟨b, hb1, hb2⟩ := AntitoneSubseq_of_HasInfinitePeaks hPeaks
    -- b : ℕ → X
    -- hb1 : Subseq b a
    -- hb2 : Antitone b
    exact ⟨b, hb1, IsCauchy_of_Antitone_of_SeqBddBelow hb2
      ⟨-M, fun n => (h1 b hb1 n).1⟩⟩
  · -- hPeaks : ¬HasInfinitePeaks a
    obtain ⟨b, hb1, hb2⟩ := MonotoneSubseq_of_NotHasInfinitePeaks hPeaks
    -- b : ℕ → X
    -- hb1 : Subseq b a
    -- hb2 : Monotone b
    exact ⟨b, hb1, IsCauchy_of_Monotone_of_SeqBddAbove hb2
      ⟨M, fun n => (h1 b hb1 n).2⟩⟩
