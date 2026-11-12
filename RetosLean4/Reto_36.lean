- Reto_36.lean
-- Crecimiento de los huecos de las sucesiones monótonas que no son de Cauchy.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 6-noviembre-2026
-- ---------------------------------------------------------------

-- ---------------------------------------------------------------
-- Demostrar que si a es una sucesión monótona que no es de Cauchy,
-- entonces existen ε > 0 y σ : ℕ → ℕ tales que, para todo k ∈ ℕ,
--    k · ε ≤ a(σᵏ(0)) - a(0),
-- donde σᵏ denota la k-ésima iterada de σ.
-- ---------------------------------------------------------------

-- Demostraciones en lenguaje natural
-- ==================================

-- Sea a monótona y que no es de Cauchy. Por el lema del Reto 35,
-- existe un ε tal que
--    ε > 0                                                    (1)
--    ∀ N, ∃ n ≥ N, ∃ m ≥ n, ε ≤ |a(m) - a(n)|
-- Como para cada N existen tales n y m, podemos elegir uno para cada N
-- (axioma de elección). Es decir, existen funciones τ y σ de ℕ en ℕ
-- tales que, para todo k,
--    τ(k) ≥ k                                                 (2)
--    σ(k) ≥ τ(k)                                              (3)
--    ε ≤ |a(σ(k)) - a(τ(k))|                                  (4)
-- donde τ(k) es el n y σ(k) es el m elegidos para N = k.
--
-- Veamos que ε y σ cumplen la conclusión del ejercicio. En
-- primer lugar, se tiene que ε > 0 (por (1)). Solo falta
-- demostrar que
--    ∀ k, k · ε ≤ a(σᵏ(0)) - a(0)
-- y lo probaremos por inducción sobre k.
--
-- Caso base (k = 0).
--    0 · ε = 0
--          ≤ 0
--          = a(0) - a(0)
--          = a(σ⁰(0)) - a(0)
--
-- Paso inductivo. Supongamos que se cumple, para k,
--    k · ε ≤ a(σᵏ(0)) - a(0).                                 (HI)
-- Queremos probar que
--    (k + 1) · ε ≤ a(σᵏ⁺¹(0)) - a(0).
-- Para abreviar, sea
--    m = σᵏ(0).
-- Entonces
--    (k + 1) · ε
--    = k · ε + ε
--        [por álgebra]
--    ≤ (a(m) - a(0)) + |a(σ(m)) - a(τ(m))|
--        [por HI y (4)]
--    = (a(m) - a(0)) + (a(σ(m)) - a(τ(m)))
--        [por (3) y por ser a monótona]
--    = (a(m) - a(τ(m))) + (a(σ(m)) - a(0))
--        [por álgebra]
--    ≤ 0 + (a(σ(m)) - a(0))
--        [por (2) y por ser a monótona]
--    = a(σ(m)) - a(0)
--        [por álgebra]
--    = a(σᵏ⁺¹(0)) - a(0)
--        [porque σ(m) = σ(σᵏ(0)) = σᵏ⁺¹(0)]

-- Demostraciones en Lean 4
-- ========================

module

import Mathlib.Tactic
public import RetosLean4.Defs -- IsCauchy
public import RetosLean4.Reto_35 -- exists_ordered_gap_of_not_isCauchy

variable {X : Type*} [CommRing X]
                     [LinearOrder X]
                     [IsStrictOrderedRing X]
variable {a : ℕ → X}

-- 1ª demostración
-- ===============

example
  (ha : Monotone a)
  (hC : ¬ IsCauchy a)
  : ∃ (ε : X) (σ : ℕ → ℕ), 0 < ε ∧ ∀ k : ℕ, k * ε ≤ a (σ^[k] 0) - a 0 :=
by
  obtain ⟨ε, hε1, hε2⟩ := exists_ordered_gap_of_not_isCauchy hC
  -- ε : X
  -- hε1 : 0 < ε
  -- hε2 : ∀ (N : ℕ), ∃ n ≥ N, ∃ m ≥ n, ε ≤ |a m - a n|
  choose τ hτ σ hσ hgap using hε2
  -- τ : ℕ → ℕ
  -- hτ : ∀ (N : ℕ), τ N ≥ N
  -- σ : ℕ → ℕ
  -- hσ : ∀ (N : ℕ), σ N ≥ τ N
  -- hgap : ∀ (N : ℕ), ε ≤ |a (σ N) - a (τ N)|
  refine ⟨ε, σ, hε1, fun k => ?_⟩
  -- ⊢ ↑k * ε ≤ a (σ^[k] 0) - a 0
  induction k with
  | zero =>
    -- ⊢ ↑0 * ε ≤ a (σ^[0] 0) - a 0
    norm_num
  | succ k ih =>
    -- k : ℕ
    -- ih : ↑k * ε ≤ a (σ^[k] 0) - a 0
    -- ⊢ ↑(k + 1) * ε ≤ a (σ^[k + 1] 0) - a 0
    push_cast
    -- ⊢ (↑k + 1) * ε ≤ a (σ^[k + 1] 0) - a 0
    set m := σ^[k] 0
    have h1 : ε ≤ a (σ m) - a (τ m) :=
      (hgap m).trans_eq (abs_of_nonneg (sub_nonneg.mpr (ha (hσ m))))
    have h2 : a m ≤ a (τ m) := ha (hτ m)
    rw [Function.iterate_succ_apply']
    -- ⊢ (↑k + 1) * ε ≤ a (σ (σ^[k] 0)) - a 0
    linarith

-- 2ª demostración
-- ===============

example
  (ha : Monotone a)
  (hC : ¬ IsCauchy a)
  : ∃ (ε : X) (σ : ℕ → ℕ), 0 < ε ∧ ∀ k : ℕ, k * ε ≤ a (σ^[k] 0) - a 0 :=
by
  obtain ⟨ε, hε1, hε2⟩ := exists_ordered_gap_of_not_isCauchy hC
  -- ε : X
  -- hε1 : 0 < ε
  -- hε2 : ∀ (N : ℕ), ∃ n ≥ N, ∃ m ≥ n, ε ≤ |a m - a n|
  choose τ hτ σ hσ hgap using hε2
  -- τ : ℕ → ℕ
  -- hτ : ∀ (N : ℕ), τ N ≥ N
  -- σ : ℕ → ℕ
  -- hσ : ∀ (N : ℕ), σ N ≥ τ N
  -- hgap : ∀ (N : ℕ), ε ≤ |a (σ N) - a (τ N)|
  refine ⟨ε, σ, hε1, fun k => ?_⟩
  -- ⊢ ↑k * ε ≤ a (σ^[k] 0) - a 0
  induction k with
  | zero =>
    -- ⊢ ↑0 * ε ≤ a (σ^[0] 0) - a 0
    push_cast
    -- ⊢ 0 * ε ≤ a (σ^[0] 0) - a 0
    calc 0 * ε
         = 0                  := zero_mul ε
       _ ≤ 0                  := le_refl 0
       _ = a 0 - a 0          := (sub_self (a 0)).symm
       _ = a (σ^[0] 0) - a 0  := rfl
  | succ k ih =>
    -- k : ℕ
    -- ih : ↑k * ε ≤ a (σ^[k] 0) - a 0
    -- ⊢ ↑(k + 1) * ε ≤ a (σ^[k + 1] 0) - a 0
    push_cast
    -- ⊢ (↑k + 1) * ε ≤ a (σ^[k + 1] 0) - a 0
    set m := σ^[k] 0
    calc (k + 1) * ε
         = k * ε + ε :=
             by ring
       _ ≤ (a m - a 0) + |a (σ m) - a (τ m)| :=
             add_le_add ih (hgap m)
       _ = (a m - a 0) + (a (σ m) - a (τ m)) :=
             by rw [abs_of_nonneg (sub_nonneg.mpr (ha (hσ m)))]
       _ = (a m - a (τ m)) + (a (σ m) - a 0) :=
             by ring
       _ ≤ 0 + (a (σ m) - a 0) :=
             add_le_add_left (sub_nonpos.mpr (ha (hτ m)))
                             (a (σ m) - a 0)
       _ = a (σ m) - a 0 :=
             zero_add (a (σ m) - a 0)
       _ = a (σ^[k + 1] 0) - a 0 :=
             by rw [Function.iterate_succ_apply']

-- 3ª demostración
-- ===============

public theorem exists_linear_growth
  (ha : Monotone a)
  (hC : ¬ IsCauchy a)
  : ∃ (ε : X) (σ : ℕ → ℕ), 0 < ε ∧ ∀ k : ℕ, k * ε ≤ a (σ^[k] 0) - a 0 :=
by
  obtain ⟨ε, hε1, hε2⟩ := exists_ordered_gap_of_not_isCauchy hC
  -- ε : X
  -- hε1 : 0 < ε
  -- hε2 : ∀ (N : ℕ), ∃ n ≥ N, ∃ m ≥ n, ε ≤ |a m - a n|
  choose τ hτ σ hσ hgap using hε2
  -- τ : ℕ → ℕ
  -- hτ : ∀ (N : ℕ), τ N ≥ N
  -- σ : ℕ → ℕ
  -- hσ : ∀ (N : ℕ), σ N ≥ τ N
  -- hgap : ∀ (N : ℕ), ε ≤ |a (σ N) - a (τ N)|
  refine ⟨ε, σ, hε1, fun k => ?_⟩
  -- ⊢ ↑k * ε ≤ a (σ^[k] 0) - a 0
  induction k with
  | zero =>
    -- ⊢ ↑0 * ε ≤ a (σ^[0] 0) - a 0
    norm_num
  | succ k ih =>
    -- k : ℕ
    -- ih : ↑k * ε ≤ a (σ^[k] 0) - a 0
    -- ⊢ ↑(k + 1) * ε ≤ a (σ^[k + 1] 0) - a 0
    push_cast
    -- ⊢ (↑k + 1) * ε ≤ a (σ^[k + 1] 0) - a 0
    set m := σ^[k] 0
    calc (k + 1) * ε
        = k * ε + ε :=
            by ring
      _ ≤ (a m - a 0) + |a (σ m) - a (τ m)| :=
            add_le_add ih (hgap m)
      _ = (a m - a 0) + (a (σ m) - a (τ m)) :=
            by rw [abs_of_nonneg (sub_nonneg.mpr (ha (hσ m)))]
      _ ≤ a (σ m) - a 0 :=
            by linarith [ha (hτ m)]
      _ = a (σ^[k + 1] 0) - a 0 :=
            by rw [Function.iterate_succ_apply']
