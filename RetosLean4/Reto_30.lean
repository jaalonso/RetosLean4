-- Reto_30.lean
-- Las sucesiones de Cauchy están acotadas.
-- Sevilla, 29-octubre-2026
-- -----------------------------------------------------------

-- -----------------------------------------------------------
-- Demostrar que si una sucesión aₙ es de Cauchy, entonces
-- aₙ está acotada; es decir, existe un M ∈ ℝ tal que para
-- todo n ∈ ℕ, |aₙ| ≤ M.
-- -----------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- La demostración se basa en los siguientes lemas:
-- + Lema 1: Si aₙ es de Cauchy, entonces existe un k ∈ ℕ tal
--   que
--      ∀ n ≥ k, |a n| < |a k| + 1.
-- + Lema 2: Para cada k ∈ ℕ, existe un M ∈ ℝ tal que
--      ∀ i < k, |a i| ≤ M.
--
-- En efecto, por el lema 1, existe un k ∈ ℕ tal que
--   ∀ n ≥ k, |aₙ| < |aₖ| + 1                                  (1)
-- Además, por el Lema 2, existe un C ∈ ℝ tal que
--   ∀ i < k, |aᵢ| ≤ C                                         (2)
-- Sea
--   M = máx(|aₖ| + 1, C)                                      (3)
-- Veamos en primer lugar que M > 0. En efecto,
--    M ≥ |aₖ| + 1  [por (3)]
--      ≥ 0 + 1
--      = 1
--      > 0
--
-- En segundo lugar, veamos que para todo n ∈ ℕ, |aₙ| ≤ M. Lo
-- haremos distinguiendo dos casos.
--
-- Caso 1: Supongamos que n < k. Entonces,
--    |aₙ| ≤ C    [por (2)]
--         ≤ M    [por (3)]
--
-- Caso 2: Supongamos que n ≥ k. Entonces,
--    |aₙ| ≤ |aₖ| + 1   [por (1)]
--         ≤ M          [por (3)]
--
-- Falta la demostración de los lemas. Para demostrar el
-- primer lema, puesto que aₙ es de Cauchy, existe un k ∈ ℕ tal
-- que
--    ∀ i ≥ k, ∀ j ≥ i, |aᵢ - aⱼ| < 1                         (4)
-- Veamos que k cumple la condición; es decir,
--    ∀ n ≥ k, |aₙ| < |aₖ| + 1
-- Para ello, sea n ∈ ℕ tal que
--    n ≥ k
-- Entonces, por (4) y por ser k ≥ k, se tiene
--    |aₙ - aₖ| < 1                                           (5)
-- y, por tanto,
--    |aₙ| = |aₖ + (aₙ - aₖ)|
--         ≤ |aₖ| + |aₙ - aₖ|   [por la desigualdad triangular]
--         < |aₖ| + 1           [por (5)]
--
-- Para demostrar el lema 2, sea
--    M = ∑ i ∈ range k, |aᵢ|                                 (6)
-- es decir,
--    M = |a₀| + |a₁| + ... + |aₖ₋₁|
-- Veamos que M es la cota buscada; es decir,
--    ∀ i < k, |aᵢ| ≤ M
-- Para ello, sea i ∈ ℕ tal que
--    i < k                                                   (7)
-- Entonces, puesto que
--    ∀ i ∈ range k, 0 ≤ |aᵢ|                                 (8)
-- y, por (7),
--    i ∈ range k                                             (9)
-- se tiene que
--    |aᵢ| ≤ ∑ i ∈ range k, |aᵢ|    [por (8) y (9)]
--         = M                      [por (6)]

-- Demostraciones en Lean 4
-- ========================

module

import Mathlib.Basic.Real.Basic
import Mathlib.Tactic
import RetosLean4.Defs -- IsCauchy, SeqBdd

open Finset

variable (a : ℕ → ℝ)

lemma cauchy_exists_bound_tail_terms
  (h : IsCauchy a)
  : ∃ k, ∀ n ≥ k, |a n| < |a k| + 1 :=
by
  obtain ⟨k, hk⟩ := h 1 one_pos
  -- k : ℕ
  -- hk : ∀ n ≥ k, ∀ m ≥ n, |a m - a n| < 1
  use k
  -- ⊢ ∀ n ≥ k, |a n| < |a k| + 1
  intro n hn
  -- n : ℕ
  -- hn : n ≥ k
  -- ⊢ |a n| < |a k| + 1
  have h1 : |a n - a k| < 1 := hk k (le_refl k) n hn
  calc |a n|
       = |a k + (a n - a k)| := congrArg abs (add_sub_cancel (a k) (a n)).symm
     _ ≤ |a k| + |a n - a k| := abs_add_le (a k) (a n - a k)
     _ < |a k| + 1           := add_lt_add_right h1 |a k|

lemma exists_bound_first_terms
  (k : ℕ)
  : ∃ M, ∀ i < k, |a i| ≤ M :=
  ⟨∑ i ∈ range k, |a i|,
   fun _ hi => single_le_sum
                 (fun j _ => abs_nonneg (a j))
                 (mem_range.mpr hi)⟩

example
  (ha : IsCauchy a)
  : SeqBdd a :=
by
  obtain ⟨k, hk⟩ := cauchy_exists_bound_tail_terms a ha
  -- k : ℕ
  -- hk : ∀ n ≥ k, |a n| < |a k| + 1
  obtain ⟨C, hC⟩ := exists_bound_first_terms a k
  -- C : ℝ
  -- hC : ∀ i < k, |a i| ≤ C
  set M := max (|a k| + 1) C
  use M
  -- ⊢ M > 0 ∧ ∀ (n : ℕ), |a n| ≤ M
  constructor
  · -- ⊢ M > 0
    calc M
         ≥ |a k| + 1 := le_max_left (|a k| + 1) C
       _ ≥ 0 + 1     := add_le_add_left (abs_nonneg (a k)) 1
       _ = 1         := zero_add 1
       _ > 0         := Real.zero_lt_one
  · intro n
    -- n : ℕ
    -- ⊢ |a n| ≤ M
    rcases lt_or_ge n k with hn1 | hn2
    · -- hn1 : n < k
      calc |a n|
           ≤ C := hC n hn1
         _ ≤ M := le_max_right (|a k| + 1) C
    · -- hn2 : k ≤ n
      calc |a n|
           ≤ |a k| + 1 := le_of_lt (hk n hn2)
         _ ≤ M         := le_max_left (|a k| + 1) _

-- Lemas usados
-- ============

-- variable (b c d : ℝ)
-- variable (m n : ℕ)
-- variable (s : Finset ℕ)
-- variable (f : ℕ → ℝ)
-- #check (abs_add_le b c : |b + c| ≤ |b| + |c|)
-- #check (abs_nonneg b : 0 ≤ |b|)
-- #check (add_le_add_left : b ≤ c → ∀ d, b + d ≤ c + d)
-- #check (add_lt_add_right : b < c → ∀ d, d + b < d + c)
-- #check (add_sub_cancel b c : b + (c - b) = c)
-- #check (le_max_left b c : b ≤ max b c)
-- #check (le_max_right b c : c ≤ max b c)
-- #check (lt_or_ge m n : m < n ∨ n ≤ m)
-- #check (mem_range : m ∈ range n ↔ m < n)
-- #check (Nat.le_refl n : n ≤ n)
-- #check (one_pos : 0 < 1)
-- #check (Real.zero_lt_one : (0 : ℝ) < 1)
-- #check (single_le_sum : (∀ i ∈ s, 0 ≤ a i) → ∀ i : ℕ, i ∈ s → a i ≤ ∑ x ∈ s, a x)
-- #check (zero_add b : 0 + b = b)
