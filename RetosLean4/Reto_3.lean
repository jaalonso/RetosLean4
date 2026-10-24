-- Reto_3.lean
-- Soluciones de 3º reto (24 de mayo de 2026).
-- Si aₙ converge a L, entonces 2aₙ converge a 2L.
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Demostrar que si aₙ converge a L, entonces 2aₙ converge a 2L.
-- ---------------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Sea bₙ la sucesión definida por
--    bₙ = 2aₙ                                                        (1)
-- Tenemos que demostrar que para cada ε > 0, existe un k ∈ ℕ tal que
--    ∀ n ≥ k, |bₙ - 2L| < ε                                          (2)
-- Puesto que aₙ converge a L, existe un k ∈ ℕ tal que
--    ∀ n ≥ k, |aₙ - L| < ε/2                                         (3)
-- Veamos que k también cumple (2). En efecto, sea n ≥ k. Entonces
--    |bₙ - 2L| = |2aₙ - 2L|     [por (1)]
--              = 2|aₙ - L|
--              < 2ε/2           [por (3)]
--              = ε

-- Demostraciones en Lean 4
-- ========================

module

import Mathlib.Basic.Real.Basic
import Mathlib.Tactic
import RetosLean4.Defs -- SeqLim

variable (a b : ℕ → ℝ)
variable (L : ℝ)

-- 1ª demostración
-- ===============

example
  (ha : SeqLim a L)
  (hb : ∀ n, b n = 2 * a n)
  : SeqLim b (2 * L) :=
by
  intro ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ k, ∀ n ≥ k, |b n - 2 * L| < ε
  obtain ⟨k, hk⟩ := ha (ε / 2) (by grind)
  -- k : ℕ
  -- hk : ∀ n ≥ k, |a n - L| < ε / 2
  use k
  -- ⊢ ∀ n ≥ k, |b n - 2 * L| < ε
  intro n hn
  -- n : ℕ
  -- hn : n ≥ k
  -- ⊢ |b n - 2 * L| < ε
  grind

-- 2ª demostración
-- ===============

example
  (ha : SeqLim a L)
  (hb : ∀ n, b n = 2 * a n)
  : SeqLim b (2 * L) :=
by
  intro ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ k, ∀ n ≥ k, |b n - 2 * L| < ε
  obtain  ⟨k, hk⟩ := ha (ε / 2) (by grind)
  -- k : ℕ
  -- hk : ∀ n ≥ k, |a n - L| < ε / 2
  use k
  -- ⊢ ∀ n ≥ k, |b n - 2 * L| < ε
  intro n hn
  -- n : ℕ
  -- hn : n ≥ k
  -- ⊢ |b n - 2 * L| < ε
  calc |b n - 2 * L|
       = |2 * a n - 2 * L| := by grind
     _ = |2 * (a n - L)|   := by grind
     _ = 2 * |a n - L|     := by grind
     _ < 2 * ε / 2         := by grind
     _ = ε                 := by grind

-- 3ª demostración
-- ===============

example
  (ha : SeqLim a L)
  (hb : ∀ n, b n = 2 * a n)
  : SeqLim b (2 * L) :=
by
  intro ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ k, ∀ n ≥ k, |b n - 2 * L| < ε
  obtain  ⟨k, hk⟩ := ha (ε / 2) (half_pos hε)
  -- k : ℕ
  -- hk : ∀ n ≥ k, |a n - L| < ε / 2
  use k
  -- ⊢ ∀ n ≥ k, |b n - 2 * L| < ε
  intro n hn
  -- n : ℕ
  -- hn : n ≥ k
  -- ⊢ |b n - 2 * L| < ε
  calc |b n - 2 * L|
       = |2 * a n - 2 * L| := by rw [hb n]
     _ = |2 * (a n - L)|   := by simp only [mul_sub]
     _ = |2| * |a n - L|   := by simp only [abs_mul]
     _ = 2 * |a n - L|     := by simp only [abs_two]
     _ < 2 * (ε / 2)       := by simp only [mul_lt_mul_of_pos_left, hk n hn, two_pos]
     _ = ε                 := by rw [mul_div_cancel₀ ε two_ne_zero]

-- 4ª demostración
-- ===============

example
  (ha : SeqLim a L)
  (hb : ∀ n, b n = 2 * a n)
  : SeqLim b (2 * L) :=
by
  intro ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ k, ∀ n ≥ k, |b n - 2 * L| < ε
  obtain  ⟨k, hk⟩ := ha (ε / 2) (half_pos hε)
  -- k : ℕ
  -- hk : ∀ n ≥ k, |a n - L| < ε / 2
  use k
  -- ⊢ ∀ n ≥ k, |b n - 2 * L| < ε
  intro n hn
  -- n : ℕ
  -- hn : n ≥ k
  -- ⊢ |b n - 2 * L| < ε
  calc |b n - 2 * L|
       = |2 * a n - 2 * L| := congrArg (|· - 2 * L|) (hb n)
     _ = |2 * (a n - L)|   := congrArg abs (mul_sub 2 (a n) L).symm
     _ = |2| * |a n - L|   := abs_mul 2 (a n - L)
     _ = 2 * |a n - L|     := congrArg (· * |a n - L|) abs_two
     _ < 2 * (ε / 2)       := mul_lt_mul_of_pos_left (hk n hn) two_pos
     _ = ε                 := mul_div_cancel₀ ε two_ne_zero

-- Lemas usados
-- ============

/-
variable (x y z : ℝ)

#check (abs_lt :|x| < y ↔ -y < x ∧ x < y)
#check (abs_mul x y : |x * y| = |x| * |y|)
#check (abs_of_pos : 0 < x → |x| = x)
#check (abs_two : |(2 : ℝ)| = 2)
#check (half_pos : 0 < x → 0 < x / 2)
#check (mul_div_cancel₀ x : y ≠ 0 → y * (x / y) = x)
#check (mul_lt_mul_of_pos_left : x < y → 0 < z → z * x < z * y)
#check (mul_sub x y z : x * (y - z) = x * y - x * z)
#check (two_ne_zero : 2 ≠ 0)
#check (zero_lt_two : 0 < 2)
-/

-- Soluciones colaborativas
-- ========================

-- Solución C1
-- ===========

example
  (ha : SeqLim a L)
  (hb : ∀ n, b n = 2 * a n)
  : SeqLim b (2 * L) :=
by
  have ha' : Filter.Tendsto a Filter.atTop (nhds L) := by
    rw [Metric.tendsto_atTop]
    -- ⊢ ∀ ε > 0, ∃ N, ∀ n ≥ N, dist (a n) L < ε
    intro ε hε
    -- ε : ℝ
    -- hε : ε > 0
    -- ⊢ ∃ N, ∀ n ≥ N, dist (a n) L < ε
    obtain ⟨N, hN⟩ := ha ε hε
    -- N : ℕ
    -- hN : ∀ n ≥ N, |a n - L| < ε
    refine ⟨N, fun n hn => ?_⟩
    -- n : ℕ
    -- hn : n ≥ N
    -- ⊢ dist (a n) L < ε
    rw [Real.dist_eq]
    -- ⊢ |a n - L| < ε
    exact hN n hn
  have hb' : Filter.Tendsto b Filter.atTop (nhds (2 * L)) := by
    have e : b = fun n => 2 * a n := funext hb
    rw [e]
    -- ⊢ Filter.Tendsto (fun n => 2 * a n) Filter.atTop (nhds (2 * L))
    exact ha'.const_mul 2
  intro ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ k, ∀ n ≥ k, |b n - 2 * L| < ε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hb' ε hε
  -- N : ℕ
  -- hN : ∀ n ≥ N, dist (b n) (2 * L) < ε
  refine ⟨N, fun n hn => ?_⟩
  -- n : ℕ
  -- hn : n ≥ N
  -- ⊢ |b n - 2 * L| < ε
  have h : dist (b n) (2 * L) < ε := hN n hn
  rw [Real.dist_eq] at h
  -- h : |b n - 2 * L| < ε
  exact h
