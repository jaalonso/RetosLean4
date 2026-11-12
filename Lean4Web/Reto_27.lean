-- Reto_27.lean
-- Si aₙ → L y M es una cota inferior de aₙ, entonces M ≤ L.
-- Sevilla, 21-septiembre-2026
-- ---------------------------------------------------------------

-- ---------------------------------------------------------------
-- Demostrar que si la sucesión aₙ converge a L y M es una cota
-- inferior de aₙ (es decir, M ≤ aₙ para todo n), entonces M ≤ L.
-- ---------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Lo demostramos por contradicción. Supongamos que
--    M > L                                                    (1)
-- y llegaremos a la contradicción M > M.
--
-- De (1), se tiene
--    M - L > 0
-- y, usando esta cantidad en la convergencia de aₙ, se obtiene
-- un k tal que
--    ∀ n ≥ k, |aₙ - L| < M - L                                (2)
-- En particular, para n = k (que satisface k ≥ k), de (2) se
-- obtiene
--    |aₖ - L| < M - L                                         (3)
-- Además,
--    aₖ - L ≤ |aₖ - L|                                        (4)
-- ya que x ≤ |x| para todo número real x.
--
-- Finalmente,
--    M = L + (M - L)
--      > L + |aₖ - L|  [por (3)]
--      ≥ L + (aₖ - L)  [por (4)]
--      = aₖ
--      ≥ M             [porque M es cota inferior de aₙ]
-- Por tanto, M > M, que es una contradicción.

-- Demostraciones en Lean 4
-- ========================

module

import Mathlib.Basic.Real.Basic
import Mathlib.Tactic
import RetosLean4.Defs -- SeqLim

variable {a : ℕ → ℝ}
variable {L M : ℝ}

-- 1ª solución
-- ===========

example
  (ha : SeqLim a L)
  (hM : ∀ n, M ≤ a n)
  : M ≤ L :=
by
  by_contra hL
  -- hL : ¬M ≤ L
  -- ⊢ False
  apply lt_irrefl M
  -- ⊢ M < M
  obtain ⟨k, hk⟩ := ha (M - L) (by grind)
  -- k : ℕ
  -- hk : ∀ n ≥ k, |a n - L| < M - L
  calc M
       > a k := by grind
     _ ≥ M   := hM k

-- 2ª solución
-- ===========

example
  (ha : SeqLim a L)
  (hM : ∀ n, M ≤ a n)
  : M ≤ L :=
by
  by_contra hL
  -- hL : ¬M ≤ L
  -- ⊢ False
  apply lt_irrefl M
  -- ⊢ M < M
  have h1 : M > L := not_le.mp hL
  have h2 : M - L > 0 := sub_pos.mpr h1
  obtain ⟨k, hk⟩ := ha (M - L) h2
  -- k : ℕ
  -- hk : ∀ n ≥ k, |a n - L| < M - L
  calc M
       = L + (M - L)    := by grind
     _ > L + |a k - L|  := by grind
     _ ≥ L + (a k - L)  := by grind
     _ = a k            := by grind
     _ ≥ M              := hM k

-- 3ª solución
-- ===========

example
  (ha : SeqLim a L)
  (hM : ∀ n, M ≤ a n)
  : M ≤ L :=
by
  by_contra hL
  -- hL : ¬M ≤ L
  -- ⊢ False
  apply lt_irrefl M
  -- ⊢ M < M
  have h1 : M - L > 0 := sub_pos.mpr (not_le.mp hL)
  obtain ⟨k, hk⟩ := ha (M - L) h1
  -- k : ℕ
  -- hk : ∀ n ≥ k, |a n - L| < M - L
  have h2 : |a k - L| < M - L := hk k (le_refl k)
  have h3 : a k - L ≤ |a k - L| := le_abs_self (a k - L)
  calc M
       = L + (M - L)    := by ring
     _ > L + |a k - L|  := add_lt_add_right h2 L
     _ ≥ L + (a k - L)  := by gcongr
     _ = a k            := by ring
     _ ≥ M              := hM k

-- 4ª solución
-- ===========

example
  (ha : SeqLim a L)
  (hM : ∀ n, M ≤ a n)
  : M ≤ L :=
by
  by_contra hL
  -- hL : ¬M ≤ L
  -- ⊢ False
  apply lt_irrefl M
  -- ⊢ M < M
  obtain ⟨k, hk⟩ := ha (M - L) (sub_pos.mpr (not_le.mp hL))
  -- k : ℕ
  -- hk : ∀ n ≥ k, |a n - L| < M - L
  have h1 : |a k - L| < M - L := hk k (le_refl k)
  have h2 : a k - L ≤ |a k - L| := le_abs_self (a k - L)
  calc M
       = L + (M - L)    := (add_sub_cancel L M).symm
     _ > L + |a k - L|  := add_lt_add_right h1 L
     _ ≥ L + (a k - L)  := (add_le_add_iff_left L).mpr h2
     _ = a k            := add_sub_cancel L (a k)
     _ ≥ M              := hM k
