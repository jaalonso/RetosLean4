-- Reto_9.lean
-- Soluciones del 9º reto (6 de julio de 2026).
-- Unicidad del límite.
-- -----------------------------------------------------------

-- -----------------------------------------------------------
-- Demostrar que si una sucesión aₙ converge tanto a L como a
-- M, entonces L = M.
-- -----------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Tenemos que demostrar que si aₙ es una sucesión y L y M son
-- límites de aₙ, entonces L = M. Lo haremos por
-- contradicción. Para ello, supongamos que
--    L ≠ M
-- Sea
--    ε = |L - M|                                          (1)
-- Entonces,
--    ε/2 > 0                                              (2)
-- y, teniendo en cuenta que aₙ converge a L y a M, existen
-- k₁ y k₂ tales que
--    ∀ n ≥ k₁, |aₙ - L| < ε/2                             (3)
--    ∀ n ≥ k₂, |aₙ - M| < ε/2                             (4)
-- Sea,
--    k = máx(k₁, k₂)                                      (5)
-- Entonces,
--    k ≥ k₁                                               (6)
--    k ≥ k₂                                               (7)
-- De (3) y (6), se tiene
--    |aₖ - L| < ε/2                                       (8)
-- De (4) y (7), se tiene
--    |aₖ - M| < ε/2                                       (9)
--
-- Tenemos que demostrar una contradicción, para lo que basta
-- probar que ε < ε. Se prueba mediante la siguiente cadena
--    ε = |L - M|                 [por (1)]
--      = |(L - M) + (aₖ - aₖ)|
--      = |(L - aₖ) + (aₖ - M)|
--      ≤ |L - aₖ| + |aₖ - M|
--      = |aₖ - L| + |aₖ - M|
--      < ε/2 + ε/2               [por (8) y (9)]
--      = ε

-- Demostraciones con Lean4
-- ========================

module

public import RetosLean4.Defs -- SeqLim
import Mathlib.Tactic

variable {a : ℕ → ℝ}
variable {L M : ℝ}

-- 1ª demostración
-- ===============

example
  (hL : SeqLim a L)
  (hM : SeqLim a M)
  : L = M :=
by
  by_contra h
  -- h : ¬L = M
  -- ⊢ False
  let ε := |L - M|
  apply lt_irrefl ε
  -- ⊢ ε < ε
  obtain ⟨k1, hk1⟩ := hL (ε/2) (by grind)
  -- k1 : ℕ
  -- hk1 : ∀ n ≥ k1, |a n - L| < ε / 2
  obtain ⟨k2, hk2⟩ := hM (ε/2) (by grind)
  -- k2 : ℕ
  -- hk2 : ∀ n ≥ k2, |a n - M| < ε / 2
  let k := max k1 k2
  calc ε = |L - M|                 := rfl
       _ = |(L - M) + (a k - a k)| := by grind
       _ = |(L - a k) + (a k - M)| := by grind
       _ ≤ |L - a k| + |a k - M|   := by grind
       _ = |a k - L| + |a k - M|   := by grind
       _ < ε/2 + ε/2               := by grind
       _ = ε                       := by grind

-- 2ª demostración
-- ===============

example
  (hL : SeqLim a L)
  (hM : SeqLim a M)
  : L = M :=
by
  by_contra h
  -- h : ¬L = M
  -- ⊢ False
  let ε := |L - M|
  apply lt_irrefl ε
  -- ⊢ ε < ε
  obtain ⟨k1, hk1⟩ := hL (ε/2) (by grind)
  -- k1 : ℕ
  -- hk1 : ∀ n ≥ k1, |a n - L| < ε / 2
  obtain ⟨k2, hk2⟩ := hM (ε/2) (by grind)
  -- k2 : ℕ
  -- hk2 : ∀ n ≥ k2, |a n - M| < ε / 2
  let k := max k1 k2
  calc ε = |(L - a k) + (a k - M)| := by grind
       _ < ε                       := by grind

-- 3ª demostración
-- ===============

example
  (hL : SeqLim a L)
  (hM : SeqLim a M)
  : L = M :=
by
  by_contra h
  -- h : ¬L = M
  -- ⊢ False
  let ε := |L - M|
  apply lt_irrefl ε
  -- ⊢ ε < ε
  have h1 : 0 < ε/2 := half_pos (abs_sub_pos.mpr h)
  obtain ⟨k1, hk1⟩ := hL (ε/2) h1
  -- k1 : ℕ
  -- hk1 : ∀ n ≥ k1, |a n - L| < ε / 2
  obtain ⟨k2, hk2⟩ := hM (ε/2) h1
  -- k2 : ℕ
  -- hk2 : ∀ n ≥ k2, |a n - M| < ε / 2
  let k := max k1 k2
  have h2 : k ≥ k1 := le_max_left k1 k2
  have h3 : k ≥ k2 := le_max_right k1 k2
  have h4 : |a k - L| < ε/2 := hk1 k h2
  have h5 : |a k - M| < ε/2 := hk2 k h3
  calc ε = |L - M|                 := rfl
       _ = |(L - M) + (a k - a k)| := by ring_nf
       _ = |(L - a k) + (a k - M)| := by ring_nf
       _ ≤ |L - a k| + |a k - M|   := abs_add_le (L - a k) (a k - M)
       _ = |a k - L| + |a k - M|   := by congr 1 ; exact abs_sub_comm L (a k)
       _ < ε/2 + ε/2               := add_lt_add h4 h5
       _ = ε                       := by ring

-- 4ª demostración
-- ===============

public theorem seqLim_unique
  (hL : SeqLim a L)
  (hM : SeqLim a M)
  : L = M :=
by
  by_contra h
  -- h : ¬L = M
  -- ⊢ False
  let ε := |L - M|
  apply lt_irrefl ε
  -- ⊢ ε < ε
  have h1 : 0 < ε/2 := half_pos (abs_sub_pos.mpr h)
  obtain ⟨k1, hk1⟩ := hL (ε/2) h1
  -- k1 : ℕ
  -- hk1 : ∀ n ≥ k1, |a n - L| < ε / 2
  obtain ⟨k2, hk2⟩ := hM (ε/2) h1
  -- k2 : ℕ
  -- hk2 : ∀ n ≥ k2, |a n - M| < ε / 2
  let k := max k1 k2
  have h2 : k ≥ k1 := le_max_left k1 k2
  have h3 : k ≥ k2 := le_max_right k1 k2
  have h4 : |a k - L| < ε/2 := hk1 k h2
  have h5 : |a k - M| < ε/2 := hk2 k h3
  calc ε = |L - M|                 := rfl
       _ = |(L - M) + 0|           := congrArg abs (add_zero (L - M)).symm
       _ = |(L - M) + (a k - a k)| := congrArg (|(L - M) + ·|) (sub_self (a k)).symm
       _ = |(L - a k) + (a k - M)| := congrArg abs (by ring)
       _ ≤ |L - a k| + |a k - M|   := abs_add_le (L - a k) (a k - M)
       _ = |a k - L| + |a k - M|   := congrArg (· + |a k - M|) (abs_sub_comm L (a k))
       _ < ε/2 + ε/2               := add_lt_add h4 h5
       _ = ε                       := add_halves ε

-- Soluciones colaborativas
-- ========================

-- Solución SC1
-- ============

open Filter Topology

example
  (hL : SeqLim a L)
  (hM : SeqLim a M)
  : L = M :=
by
  have h1 : ∀ {x : ℝ}, SeqLim a x → Tendsto a atTop (𝓝 x) := by
    intro x hx
    -- x : ℝ
    -- hx : SeqLim a x
    -- ⊢ Tendsto a atTop (𝓝 x)
    rw [Metric.tendsto_atTop]
    -- ⊢ ∀ ε > 0, ∃ N, ∀ n ≥ N, dist (a n) x < ε
    intro ε hε
    -- ε : ℝ
    -- hε : ε > 0
    -- ⊢ ∃ N, ∀ n ≥ N, dist (a n) x < ε
    obtain ⟨k, hk⟩ := hx ε hε
    -- k : ℕ
    -- hk : ∀ n ≥ k, |a n - x| < ε
    exact ⟨k, fun n hn => by simpa [Real.dist_eq] using hk n hn⟩
  exact tendsto_nhds_unique (h1 hL) (h1 hM)
