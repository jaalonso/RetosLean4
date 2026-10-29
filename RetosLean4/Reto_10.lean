-- Reto_10.lean
-- Soluciones del 10º reto (13 de julio de 2026).
-- Si aₙ → L con L ≠ 0, entonces |aₙ| ≥ |L|/2 eventualmente.
-- Sevilla, 18-julio-2026
-- -----------------------------------------------------------

-- -----------------------------------------------------------
-- Demostrar que si una sucesión converge a un límite no
-- nulo, entonces sus términos están eventualmente acotados
-- inferiormente por la mitad del valor absoluto del límite;
-- es decir, si una sucesión aₙ converge a L con L ≠ 0,
-- entonces existe k tal que para todo n ≥ k se tiene que
-- |aₙ| ≥ |L|/2.
-- -----------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Puesto que L ≠ 0, se tiene que
--    |L| / 2 > 0
-- y, como a converge a L, existe un k tal que
--    ∀ n ≥ k, |aₙ - L| < |L| / 2                                    (1)
-- Veamos que
--    ∀ n ≥ k, |aₙ| ≥ |L|/2.
-- En efecto, sea n ≥ k. Entonces, por (1),
--    |aₙ - L| < |L| / 2                                             (2)
-- Además,
--    |L| = |aₙ + (L - aₙ)|
--        ≤ |aₙ| + |L - aₙ|
--        = |aₙ| + |-(aₙ - L)|
--        = |aₙ| + |aₙ - L|
--        ≤ |aₙ| + |L| / 2      [por (2)]
-- Luego,
--    |L| ≤ |aₙ| + |L| / 2
-- y, por tanto,
--    |aₙ| ≥ |L|/2

-- Demostraciones con Lean4
-- ========================

module

import Mathlib.Basic.Real.Basic
import Mathlib.Tactic
public import RetosLean4.Defs -- SeqLim

variable {a : ℕ → ℝ}
variable {L : ℝ}

-- 1ª demostración
-- ===============

example
  (ha : SeqLim a L)
  (hL : L ≠ 0)
  : ∃ k, ∀ n ≥ k, |a n| ≥ |L| / 2 :=
by
  obtain ⟨k, hk⟩ := ha (|L| / 2) (by grind)
  -- k : ℕ
  -- hk : ∀ n ≥ k, |a n - L| < |L| / 2
  use k
  -- ⊢ ∀ n ≥ k, |L| / 2 ≤ |a n|
  intro n hn
  -- n : ℕ
  -- hn : n ≥ k
  -- ⊢ |L| / 2 ≤ |a n|
  grind

-- 2ª demostración
-- ===============

example
  (ha : SeqLim a L)
  (hL : L ≠ 0)
  : ∃ k, ∀ n ≥ k,  |a n| ≥ |L| / 2 :=
by
  obtain ⟨k, hk⟩ := ha (|L| / 2) (by grind)
  -- k : ℕ
  -- hk : ∀ n ≥ k, |a n - L| < |L| / 2
  use k
  -- ⊢ ∀ n ≥ k, |L| / 2 ≤ |a n|
  intro n hn
  -- n : ℕ
  -- hn : n ≥ k
  -- ⊢ |L| / 2 ≤ |a n|
  have h3 : |a n - L| < |L| / 2 := hk n hn
  have h4 : |L| ≤ |a n| + |L| / 2 := by
    calc |L|
         = |a n + (L - a n)|    := by grind
       _ ≤ |a n| + |L - a n|    := by grind
       _ = |a n| + |-(a n - L)| := by grind
       _ = |a n| + |a n - L|    := by grind
       _ ≤ |a n| + |L| / 2      := by grind
  grind

-- 3ª demostración
-- ===============

example
  (ha : SeqLim a L)
  (hL : L ≠ 0)
  : ∃ k, ∀ n ≥ k, |a n| ≥ |L| / 2 :=
by
  obtain ⟨k, hk⟩ := ha (|L| / 2) (by positivity)
  -- k : ℕ
  -- hk : ∀ n ≥ k, |a n - L| < |L| / 2
  use k
  -- ⊢ ∀ n ≥ k, |L| / 2 ≤ |a n|
  intro n hn
  -- n : ℕ
  -- hn : n ≥ k
  -- ⊢ |L| / 2 ≤ |a n|
  have h3 : |a n - L| < |L| / 2 := hk n hn
  have h4 : |L| ≤ |a n| + |L| / 2 := by
    calc |L|
         = |a n + (L - a n)|    := by ring_nf
       _ ≤ |a n| + |L - a n|    := abs_add_le (a n) (L - a n)
       _ = |a n| + |-(a n - L)| := by ring_nf
       _ = |a n| + |a n - L|    := by congr 1 ; exact abs_neg (a n - L)
       _ ≤ |a n| + |L| / 2      := by gcongr
  linarith [h4]

-- 4ª demostración
-- ===============

example
  (ha : SeqLim a L)
  (hL : L ≠ 0)
  : ∃ k, ∀ n ≥ k, |a n| ≥ |L| / 2 :=
by
  have h1 : 0 < |L| := abs_pos.mpr hL
  have h2 : 0 < |L| / 2 := half_pos h1
  obtain ⟨k, hk⟩ := ha (|L| / 2) h2
  -- k : ℕ
  -- hk : ∀ n ≥ k, |a n - L| < |L| / 2
  use k
  -- ⊢ ∀ n ≥ k, |L| / 2 ≤ |a n|
  intro n hn
  -- n : ℕ
  -- hn : n ≥ k
  -- ⊢ |L| / 2 ≤ |a n|
  have h3 : |a n - L| < |L| / 2 := hk n hn
  have h4 : |L| ≤ |a n| + |L| / 2 := by calc
    |L| = |a n + (L - a n)|    := by ring_nf
      _ ≤ |a n| + |L - a n|    := abs_add_le (a n) (L - a n)
      _ = |a n| + |-(a n - L)| := congrArg (|a n| + |·|) (neg_sub (a n) L).symm
      _ = |a n| + |a n - L|    := congrArg (|a n| + ·) (abs_neg (a n - L))
      _ ≤ |a n| + |L| / 2      := add_le_add_right (le_of_lt h3) |a n|
  calc |L| / 2
       = |L| - |L| / 2 := (sub_half |L|).symm
     _ ≤ |a n|         := tsub_le_iff_right.mpr h4

-- 5ª demostración
-- ===============

public theorem exists_half_abs_le_abs_of_seqLim_of_ne_zero
  (ha : SeqLim a L)
  (hL : L ≠ 0)
  : ∃ k, ∀ n ≥ k, |a n| ≥ |L| / 2 :=
by
  obtain ⟨k, hk⟩ := ha (|L| / 2) (by grind)
  -- k : ℕ
  -- hk : ∀ n ≥ k, |a n - L| < |L| / 2
  refine ⟨k, fun _ _ => by grind⟩

-- Soluciones colaborativas
-- ========================

-- Solución SC1
-- ============

open Filter Topology

example
  (ha : SeqLim a L)
  (hL : L ≠ 0)
  : ∃ k, ∀ n ≥ k, |a n| ≥ |L| / 2 :=
by
  have h1 : Tendsto a atTop (𝓝 L) := by
    rw [Metric.tendsto_atTop]
    -- ⊢ ∀ ε > 0, ∃ N, ∀ n ≥ N, dist (a n) L < ε
    intro ε hε
    -- ε : ℝ
    -- hε : ε > 0
    -- ⊢ ∃ N, ∀ n ≥ N, dist (a n) L < ε
    obtain ⟨k, hk⟩ := ha ε hε
    -- k : ℕ
    -- hk : ∀ n ≥ k, |a n - L| < ε
    -- exact ⟨k, fun n hn => by simpa [Real.dist_eq] using hk n hn⟩
    use k
    -- ⊢ ∀ n ≥ k, dist (a n) L < ε
    intro n hn
    -- n : ℕ
    -- hn : n ≥ k
    -- ⊢ dist (a n) L < ε
    simp [Real.dist_eq]
    -- ⊢ |a n - L| < ε
    exact hk n hn
  have h2 : Tendsto (fun n => |a n|) atTop (𝓝 |L|) := h1.abs
  have h3 : |L| / 2 < |L| := half_lt_self (abs_pos.mpr hL)
  obtain ⟨k, hk⟩ := eventually_atTop.mp (h2.eventually (lt_mem_nhds h3))
  -- k : ℕ
  -- hk : ∀ (b : ℕ), k ≤ b → |L| / 2 < |a b|
  exact ⟨k, fun n hn => (hk n hn).le⟩
