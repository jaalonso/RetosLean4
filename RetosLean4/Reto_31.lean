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
-- import RetosLean4.Defs -- SeqLim, SeqBdd, SeqConv, IsExtraction, Subseq
-- import RetosLean4.Reto_17 -- seqBdd_of_seqConv

-- De retos anteriores
-- ===================

variable (a : ℕ → ℝ)

def SeqLim (a : ℕ → ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ k : ℕ, ∀ n ≥ k, |a n - L| < ε

def SeqConv (a : ℕ → ℝ) : Prop :=
  ∃ L, SeqLim a L

def SeqBdd (a : ℕ → ℝ) : Prop :=
  ∃ M > 0, ∀ n, |a n| ≤ M

def IsExtraction (φ : ℕ → ℕ) : Prop :=
  StrictMono φ

def Subseq (v u : ℕ → ℝ) : Prop :=
  ∃ φ, IsExtraction φ ∧ v = u ∘ φ

open Finset

lemma Challenge17_L1
  (h : SeqLim a L)
  : ∃ k, ∀ n ≥ k, |a n| < |L| + 1 :=
  (h 1 one_pos).imp fun _k hk n hn =>
    -- _k : ℕ
    -- hk : ∀ n ≥ _k, |a n - L| < 1
    -- n : ℕ
    -- hn : n ≥ _k
    -- ⊢ |a n| < |L| + 1
    calc |a n|
        = |L + (a n - L)| := congrArg abs (add_sub_cancel L (a n)).symm
      _ ≤ |L| + |a n - L| := abs_add_le L (a n - L)
      _ < |L| + 1         := add_lt_add_right (hk n hn) |L|

lemma Challenge17_L2
  (k : ℕ)
  : ∃ M, ∀ i < k, |a i| ≤ M :=
  ⟨∑ i ∈ range k, |a i|,
   fun _ hi => single_le_sum
                 (fun j _ => abs_nonneg (a j))
                 (mem_range.mpr hi)⟩

lemma seqBdd_of_seqConv
  (ha : SeqConv a) :
  SeqBdd a :=
by
  obtain ⟨L, hL⟩ := ha
  -- L : ℝ
  -- hL : SeqLim a L
  obtain ⟨k, hk⟩ := Challenge17_L1 a hL
  -- k : ℕ
  -- hk : ∀ n ≥ k, |a n| < |L| + 1
  obtain ⟨C, hC⟩ := Challenge17_L2 a k
  -- C : ℝ
  -- hC : ∀ i < k, |a i| ≤ C
  set M := max (|L| + 1) C
  -- hM : M = max (|L| + 1) C
  use M
  -- ⊢ M > 0 ∧ ∀ (n : ℕ), |a n| ≤ M
  constructor
  · -- ⊢ M > 0
    calc M
         ≥ |L| + 1 := le_max_left (|L| + 1) C
       _ ≥ 0 + 1   := add_le_add_left (abs_nonneg L) 1
       _ = 1       := zero_add 1
       _ > 0       := Real.zero_lt_one
  · intro n
    -- n : ℕ
    -- ⊢ |a n| ≤ M
    rcases lt_or_ge n k with hn1 | hn2
    · -- hn1 : n < k
      calc |a n|
           ≤ C := hC n hn1
         _ ≤ M := le_max_right _ C
    · -- hn2 : k ≤ n
      calc |a n|
           ≤ |L| + 1 := le_of_lt (hk n hn2)
         _ ≤ M       := le_max_left (|L| + 1) _

-- Soluciones del reto
-- ===================

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
