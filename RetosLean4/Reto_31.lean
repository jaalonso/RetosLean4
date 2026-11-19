-- Reto_31.lean
-- La sucesión identidad no tiene subsucesiones convergentes.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 30-octubre-2026
-- ---------------------------------------------------------------

-- ---------------------------------------------------------------
-- Sea aₙ la sucesión identidad; es decir, que para todo n, aₙ = n.
-- Demostrar que aₙ no tiene subsucesiones convergentes.
-- ---------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Supongamos que a tiene una subsucesión convergente
--    b = a ∘ φ                                                 (1)
-- con φ estrictamente creciente. Por ser b convergente, está
-- acotada (reto 17); sea M una cota, es decir,
--    ∀ n, |bₙ| ≤ M                                             (2)
-- Por la propiedad arquimediana, existe k tal que
--    M < k                                                     (3)
-- Entonces
--    M < k         [por (3)]
--      ≤ φ(k)      [porque φ es estrictamente creciente]
--      = a(φ(k))   [por ser a la sucesión identidad]
--      = bₖ        [por (1)]
--      ≤ |bₖ|      [porque x ≤ |x|]
--      ≤ M         [por (2)]
-- que es una contradicción.

-- Demostraciones en Lean 4
-- ========================

module

import Mathlib.Basic.Real.Basic
import Mathlib.Tactic
import RetosLean4.Defs -- SeqLim, SeqBdd, SeqConv, IsExtraction, Subseq
import RetosLean4.Reto_17 -- seqBdd_of_seqConv

variable (a : ℕ → ℝ)

-- 1ª demostración
-- ===============

example
  (ha : ∀ n, a n = n)
  : ¬ ∃ b, Subseq b a ∧ SeqConv b :=
by
  rintro ⟨b, hb1, hb2⟩
  -- b : ℕ → ℝ
  -- hb1 : Subseq b a
  -- hb2 : SeqConv b
  -- ⊢ False
  have h1 : SeqBdd b := seqBdd_of_seqConv b hb2
  obtain ⟨M, -, hM⟩ := h1
  -- M : ℝ
  -- hM : ∀ (n : ℕ), |b n| ≤ M
  obtain ⟨k, hk⟩ := exists_nat_gt M
  -- k : ℕ
  -- hk : M < ↑k
  obtain ⟨φ, hφ, hb⟩ := hb1
  -- hφ : IsExtraction φ
  -- hb : b = a ∘ φ
  apply lt_irrefl M
  -- ⊢ M < M
  calc M
       < (k : ℝ)   := by grind
     _ ≤ (φ k : ℝ) := by exact_mod_cast hφ.le_apply
     _ = a (φ k)   := by grind
     _ = b k       := (congrFun hb k).symm
     _ ≤ |b k|     := by grind
     _ ≤ M         := by grind

-- 2ª demostración
-- ===============

example
  (ha : ∀ n, a n = n)
  : ¬ ∃ b, Subseq b a ∧ SeqConv b :=
by
  rintro ⟨b, hb1, hb2⟩
  -- b : ℕ → ℝ
  -- hb1 : Subseq b a
  -- hb2 : SeqConv b
  -- ⊢ False
  have h1 : SeqBdd b := seqBdd_of_seqConv b hb2
  obtain ⟨M, -, hM⟩ := h1
  -- M : ℝ
  -- hM : ∀ (n : ℕ), |b n| ≤ M
  obtain ⟨k, hk⟩ := exists_nat_gt M
  -- k : ℕ
  -- hk : M < ↑k
  obtain ⟨φ, hφ, hb⟩ := hb1
  -- hφ : IsExtraction φ
  -- hb : b = a ∘ φ
  apply lt_irrefl M
  -- ⊢ M < M
  calc M
       < (k : ℝ)   := hk
     _ ≤ (φ k : ℝ) := by exact_mod_cast hφ.le_apply
     _ = a (φ k)   := (ha (φ k)).symm
     _ = b k       := (congrFun hb k).symm
     _ ≤ |b k|     := le_abs_self (b k)
     _ ≤ M         := hM k

-- 3ª demostración
-- ===============

example
  (ha : ∀ n, a n = n)
  : ¬ ∃ b, Subseq b a ∧ SeqConv b :=
by
  rintro ⟨_, ⟨φ, hφ, rfl⟩, hb2⟩
  -- φ : ℕ → ℕ
  -- hφ : IsExtraction φ
  -- hb2 : SeqConv (a ∘ φ)
  -- ⊢ False
  obtain ⟨M, -, hM⟩ := seqBdd_of_seqConv (a ∘ φ) hb2
  -- M : ℝ
  -- hM : ∀ (n : ℕ), |(a ∘ φ) n| ≤ M
  obtain ⟨k, hk⟩ := exists_nat_gt M
  -- k : ℕ
  -- hk : M < ↑k
  exact lt_irrefl M <| calc
    M < (k : ℝ)     := hk
    _ ≤ (φ k : ℝ)   := mod_cast hφ.le_apply
    _ = (a ∘ φ) k   := (ha (φ k)).symm
    _ ≤ |(a ∘ φ) k| := le_abs_self _
    _ ≤ M           := hM k

-- 4ª demostración
-- ===============

example
  (ha : ∀ n, a n = n)
  : ¬ ∃ b, Subseq b a ∧ SeqConv b :=
by
  rintro ⟨b, hb1, hb2⟩
  -- b : ℕ → ℝ
  -- hb1 : Subseq b a
  -- hb2 : SeqConv b
  -- ⊢ False
  have h1 : SeqBdd b := seqBdd_of_seqConv b hb2
  obtain ⟨M, -, hM⟩ := h1
  -- M : ℝ
  -- hM : ∀ (n : ℕ), |b n| ≤ M
  set k : ℕ := ⌈M⌉₊ + 1
  obtain ⟨φ, hφ, hb⟩ := hb1
  -- hφ : IsExtraction φ
  -- hb : b = a ∘ φ
  apply lt_irrefl M
  -- ⊢ M < M
  calc M
       ≤ ⌈M⌉₊      := Nat.le_ceil M
     _ < ⌈M⌉₊ + 1  := lt_add_one (⌈M⌉₊ : ℝ)
     _ = k         := (Nat.cast_add_one ⌈M⌉₊).symm
     _ ≤ (φ k : ℝ) := by exact_mod_cast hφ.le_apply
     _ = a (φ k)   := (ha (φ k)).symm
     _ = b k       := (congrFun hb k).symm
     _ ≤ |b k|     := le_abs_self (b k)
     _ ≤ M         := hM k
