-- Reto_28.lean
-- La sucesión aₙ = n no está acotada.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 28-octubre-2026
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------
-- Demostrar que la sucesión aₙ = n no está acotada.
--
-- Para ello, completar la siguiente teoría
--    import Mathlib.Basic.Real.Basic
--    import Mathlib.Tactic
--
--    def SeqBdd (a : ℕ → ℝ) : Prop :=
--      ∃ M > 0, ∀ n, |a n| ≤ M
--
--    variable {a : ℕ → ℝ}
--
--    example
--      (ha : ∀ n, a n = n)
--      : ¬ SeqBdd a :=
--    by sorry
-- ---------------------------------------------------------------

-- Demostraciones en lenguaje natural
-- ==================================

-- 1ª demostración en lenguaje natural (LN1)
-- =========================================

-- Supongamos que existe M ∈ ℝ tal que
--    ∀ n, |aₙ| ≤ M.                                           (1)
-- Por la propiedad arquimediana, existe un k ∈ ℕ tal que
--    M < k                                                    (2)
-- y recordemos que
--    ∀ n, aₙ = n.                                             (3)
-- Entonces
--    M < k         [por (2)]
--      = aₖ        [por (3)]
--      ≤ |aₖ|
--      ≤ M         [por (1)]
-- Por tanto, M < M que es una contradicción.

-- 2ª demostración en lenguaje natural (LN2)
-- =========================================

-- Supongamos que existe M ∈ ℝ tal que
--    ∀ n, |aₙ| ≤ M.                                           (1)
-- Sea
--    k = ⌈M⌉ + 1                                              (2)
-- y recordemos que
--    ∀ n, aₙ = n.                                             (3)
-- Entonces
--    M ≤ ⌈M⌉
--      < ⌈M⌉ + 1
--      = k         [por (2)]
--      = aₖ        [por (3)]
--      ≤ |aₖ|
--      ≤ M         [por (1)]
-- Por tanto, M < M que es una contradicción.

-- Demostraciones en Lean 4
-- ========================

module

import Mathlib.Basic.Real.Basic
import Mathlib.Tactic
import RetosLean4.Defs -- SeqBdd

variable {a : ℕ → ℝ}

-- 1ª demostración (correspondiente a LN1)
-- =======================================

example
  (ha : ∀ n, a n = n)
  : ¬ SeqBdd a :=
by
  rintro ⟨M, -, hM⟩
  -- M : ℝ
  -- hM : ∀ (n : ℕ), |a n| ≤ M
  -- ⊢ False
  obtain ⟨k, hk⟩ := exists_nat_gt M
  -- k : ℕ
  -- hk : M < ↑k
  apply lt_irrefl M
  -- ⊢ M < M
  calc M
       < k         := hk
     _ = a k       := by simp [ha]
     _ ≤ |a k|     := le_abs_self _
     _ ≤ M         := hM k

-- 2ª demostración (correspondiente a LN2)
-- =======================================

example
  (ha : ∀ n, a n = n)
  : ¬ SeqBdd a :=
by
  rintro ⟨M, -, hM⟩
  -- M : ℝ
  -- hM : ∀ (n : ℕ), |a n| ≤ M
  -- ⊢ False
  set k : ℕ := ⌈M⌉₊ + 1 with hk
  apply lt_irrefl M
  -- ⊢ M < M
  calc M
       ≤ ⌈M⌉₊      := Nat.le_ceil M
     _ < k         := by simp [hk]
     _ = a k       := by simp [ha]
     _ ≤ |a k|     := le_abs_self (a k)
     _ ≤ M         := hM k

-- 3ª demostración (correspondiente a LN2)
-- =======================================

example
  (ha : ∀ n, a n = n)
  : ¬ SeqBdd a :=
by
  rintro ⟨M, -, hM⟩
  -- M : ℝ
  -- hM : ∀ (n : ℕ), |a n| ≤ M
  -- ⊢ False
  set k : ℕ := ⌈M⌉₊ + 1 with hk
  apply lt_irrefl M
  -- ⊢ M < M
  calc M
       ≤ ⌈M⌉₊      := Nat.le_ceil M
     _ < ⌈M⌉₊ + 1  := lt_add_one _
     _ = k         := by rw [hk, Nat.cast_add_one]
     _ = a k       := by rw [ha k]
     _ ≤ |a k|     := le_abs_self (a k)
     _ ≤ M         := hM k

-- 4ª demostración (correspondiente a LN2)
-- =======================================

example
  (ha : ∀ n, a n = n)
  : ¬ SeqBdd a :=
by
  rintro ⟨M, -, hM⟩
  -- M : ℝ
  -- hM : ∀ (n : ℕ), |a n| ≤ M
  -- ⊢ False
  set k : ℕ := ⌈M⌉₊ + 1
  apply lt_irrefl M
  -- ⊢ M < M
  calc M
       ≤ ⌈M⌉₊      := Nat.le_ceil M
     _ < ⌈M⌉₊ + 1  := lt_add_one (⌈M⌉₊ : ℝ)
     _ = k         := (Nat.cast_add_one ⌈M⌉₊).symm
     _ = a k       := (ha k).symm
     _ ≤ |a k|     := le_abs_self (a k)
     _ ≤ M         := hM k
