-- Reto_36.lean
-- Las sucesiones monótonas y acotadas superiormente son de Cauchy.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 6-noviembre-2026
-- ---------------------------------------------------------------

-- ---------------------------------------------------------------
-- Demostrar que si a es una sucesión monótona y acotada
-- superiormente, entonces a es de Cauchy.
--
-- Para ello, completar la siguiente teoría en Lean 4:
--    import Mathlib.Basic.Real.Basic
--    import Mathlib.Tactic
--
--    def IsCauchy {X : Type*} [AddGroup X] [Lattice X] (a : ℕ → X) : Prop :=
--      ∀ (ε : X), 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ n, |a m - a n| < ε
--
--    def SeqBddAbove {X : Type*} [LE X] (a : ℕ → X) : Prop :=
--      ∃ M : X, ∀ n, a n ≤ M
--
--    variable {X : Type*} [Field X]
--                         [LinearOrder X]
--                         [IsStrictOrderedRing X]
--                         [Archimedean X]
--    variable {a : ℕ → X}
--
--    example
--      [Archimedean X]
--      (h1 : Monotone a)
--      (h2 : SeqBddAbove a)
--      : IsCauchy a :=
--    by sorry
-- ---------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Lo demostraremos por reducción al absurdo. Supongamos que a no
-- es de Cauchy y que está acotada superiormente, y lleguemos a
-- una contradicción.
--
-- Por estar a acotada superiormente, existe un M tal que
--    ∀ n, a(n) ≤ M                                             (1)
-- Por el lema del crecimiento lineal de los huecos de las
-- sucesiones monótonas que no son de Cauchy (del Reto 35),
-- existen ε y σ tales que
--    0 < ε
--    ∀ k, k · ε ≤ a(σᵏ(0)) - a(0)                              (2)
-- Por la propiedad arquimediana, existe k ∈ ℕ tal que
--    M - a(0) < k · ε                                          (3)
-- Para obtener una contradicción, demostraremos que
--    M < M
-- En efecto,
--    M = (M - a(0)) + a(0)          [por álgebra]
--      < k · ε + a(0)               [por (3)]
--      ≤ (a(σᵏ(0)) - a(0)) + a(0)   [por (2)]
--      = a(σᵏ(0))                   [por álgebra]
--      ≤ M                          [por (1)]
--
-- Variante. En lugar de la propiedad arquimediana se puede usar la
-- función suelo: basta tomar
--    k = ⌊(M - a(0)) / ε⌋ + 1
-- ya que entonces (M - a(0)) / ε < k y, por tanto, se cumple (3).

-- Demostraciones en Lean 4
-- ========================

module

import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic
public import RetosLean4.Defs -- IsCauchy, SeqBddAbove
public import RetosLean4.Reto_35 -- exists_linear_growth

variable {X : Type*} [Field X]
                     [LinearOrder X]
                     [IsStrictOrderedRing X]
                     [Archimedean X]
variable {a : ℕ → X}

-- 1ª demostración
-- ===============

example
  (h1 : Monotone a)
  (h2 : SeqBddAbove a)
  : IsCauchy a :=
by
  by_contra hC
  -- hC : ¬IsCauchy a
  -- ⊢ False
  obtain ⟨M, hM⟩ := h2
  -- M : X
  -- hM : ∀ (n : ℕ), a n ≤ M
  obtain ⟨ε, σ, hε, hσ⟩ :=
    exists_linear_growth h1 hC
  -- ε : X
  -- σ : ℕ → ℕ
  -- hε : 0 < ε
  -- hσ : ∀ (k : ℕ), ↑k * ε ≤ a (σ^[k] 0) - a 0
  obtain ⟨k, hk⟩ := exists_lt_nsmul hε (M - a 0)
  -- k : ℕ
  -- hk : M - a 0 < k • ε
  rw [nsmul_eq_mul] at hk
  -- hk : M - a 0 < ↑k * ε
  linarith [hσ k, hM (σ^[k] 0)]

-- 2ª demostración
-- ===============

example
  (h1 : Monotone a)
  (h2 : SeqBddAbove a)
  : IsCauchy a :=
by
  by_contra hC
  -- hC : ¬IsCauchy a
  -- ⊢ False
  obtain ⟨M, hM⟩ := h2
  -- M : X
  -- hM : ∀ (n : ℕ), a n ≤ M
  obtain ⟨ε, σ, hε, hσ⟩ :=
    exists_linear_growth h1 hC
  -- ε : X
  -- σ : ℕ → ℕ
  -- hε : 0 < ε
  -- hσ : ∀ (k : ℕ), ↑k * ε ≤ a (σ^[k] 0) - a 0
  obtain ⟨k, hk⟩ := exists_lt_nsmul hε (M - a 0)
  -- k : ℕ
  -- hk : M - a 0 < k • ε
  rw [nsmul_eq_mul] at hk
  -- hk : M - a 0 < ↑k * ε
  apply lt_irrefl M
  -- ⊢ M < M
  calc M
       = (M - a 0) + a 0 :=
           (sub_add_cancel M (a 0)).symm
     _ < k * ε + a 0 :=
           by linarith
     _ ≤ (a (σ^[k] 0) - a 0) + a 0 :=
           by linarith [hσ k]
     _ = a (σ^[k] 0) :=
           sub_add_cancel (a (σ^[k] 0)) (a 0)
     _ ≤ M :=
           hM (σ^[k] 0)

-- 3ª demostración
-- ===============

public theorem isCauchy_of_mono_bddAbove
  (h1 : Monotone a)
  (h2 : SeqBddAbove a)
  : IsCauchy a :=
by
  by_contra hC
  -- hC : ¬IsCauchy a
  -- ⊢ False
  obtain ⟨M, hM⟩ := h2
  -- M : X
  -- hM : ∀ (n : ℕ), a n ≤ M
  obtain ⟨ε, σ, hε, hσ⟩ :=
    exists_linear_growth h1 hC
  -- ε : X
  -- σ : ℕ → ℕ
  -- hε : 0 < ε
  -- hσ : ∀ (k : ℕ), ↑k * ε ≤ a (σ^[k] 0) - a 0
  obtain ⟨k, hk⟩ := exists_nat_gt ((M - a 0) / ε)
  -- k : ℕ
  -- hk : (M - a 0) / ε < ↑k
  have h3 : M - a 0 < k * ε := (div_lt_iff₀ hε).mp hk
  apply lt_irrefl M
  -- ⊢ M < M
  calc M
       = (M - a 0) + a 0 :=
           (sub_add_cancel M (a 0)).symm
     _ < k * ε + a 0 :=
           by linarith
     _ ≤ (a (σ^[k] 0) - a 0) + a 0 :=
           by linarith [hσ k]
     _ = a (σ^[k] 0) :=
           sub_add_cancel (a (σ^[k] 0)) (a 0)
     _ ≤ M :=
           hM (σ^[k] 0)

-- 4ª demostración
-- ===============

example
  [FloorSemiring X]
  (h1 : Monotone a)
  (h2 : SeqBddAbove a)
  : IsCauchy a :=
by
  by_contra hC
  -- hC : ¬IsCauchy a
  -- ⊢ False
  obtain ⟨M, hM⟩ := h2
  -- M : X
  -- hM : ∀ (n : ℕ), a n ≤ M
  obtain ⟨ε, σ, hε, hσ⟩ :=
    exists_linear_growth h1 hC
  -- ε : X
  -- σ : ℕ → ℕ
  -- hε : 0 < ε
  -- hσ : ∀ (k : ℕ), ↑k * ε ≤ a (σ^[k] 0) - a 0
  set k := ⌊(M - a 0) / ε⌋₊ + 1
  have h3 : (M - a 0) / ε < k := Nat.lt_succ_floor ((M - a 0) / ε)
  have h4 : M - a 0 < k * ε := (div_lt_iff₀ hε).mp h3
  apply lt_irrefl M
  -- ⊢ M < M
  calc M
       = (M - a 0) + a 0 :=
           (sub_add_cancel M (a 0)).symm
     _ < k * ε + a 0 :=
           by linarith
     _ ≤ (a (σ^[k] 0) - a 0) + a 0 :=
           by linarith [hσ k]
     _ = a (σ^[k] 0) :=
           sub_add_cancel (a (σ^[k] 0)) (a 0)
     _ ≤ M :=
           hM (σ^[k] 0)
