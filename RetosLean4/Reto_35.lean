-- Reto_35.lean
-- Crecimiento de los huecos de las sucesiones monótonas que no son de Cauchy.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 6-noviembre-2026
-- ---------------------------------------------------------------

-- ---------------------------------------------------------------
-- Demostrar que si a es una sucesión monótona que no es de Cauchy,
-- entonces existen ε > 0 y σ : ℕ → ℕ tales que, para todo k ∈ ℕ,
--    k · ε ≤ a(σᵏ(0)) − a(0),
-- donde σᵏ denota la k-ésima iterada de σ.
-- ---------------------------------------------------------------

-- Demostraciones en lenguaje natural
-- ==================================

-- Puesto que a no es de Cauchy, existe un ε tal que
--    ε > 0                                                    (1)
--    ∀ N, ∃ n ≥ N, ∃ m ≥ n, ε ≤ |a(m) - a(n)|
-- y, por tanto, existen τ y σ (funciones de ℕ en ℕ) tales que
--    ∀ k, τ(k) ≥ k                                            (2)
--    ∀ k, σ(k) ≥ τ(k)                                         (3)
--    ∀ k, ε ≤ |a(σ(k)) - a(τ(k))|                             (4)
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
--    k · ε ≤ a(σᵏ(0)) − a(0).                                 (HI)
-- Queremos probar que
--    (k + 1) · ε ≤ a(σᵏ⁺¹(0)) − a(0).
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

import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic
public import RetosLean4.Defs -- IsCauchy

variable {X : Type*} [CommRing X]
                     [LinearOrder X]
                     [IsStrictOrderedRing X]
variable {a : ℕ → X}

lemma isCauchy_iff_isCauchy2 :
  IsCauchy a ↔ IsCauchy2 a :=
by
  constructor
  · -- ⊢ IsCauchy a → IsCauchy2 a
    intro h1 ε hε
    -- h1 : IsCauchy a
    -- ε : X
    -- hε : 0 < ε
    -- ⊢ ∃ N, ∀ n ≥ N, ∀ m ≥ n, |a m - a n| < ε
    obtain ⟨N, hN⟩ := h1 ε hε
    -- N : ℕ
    -- hN : ∀ n ≥ N, ∀ m ≥ N, |a m - a n| < ε
    use N
    -- ⊢ ∀ n ≥ N, ∀ m ≥ n, |a m - a n| < ε
    intro n hn m hm
    -- n : ℕ
    -- hn : n ≥ N
    -- m : ℕ
    -- hm : m ≥ n
    -- ⊢ |a m - a n| < ε
    exact hN n hn m (le_trans hn hm)
  · -- ⊢ IsCauchy2 a → IsCauchy a
    intro h2 ε hε
    -- h2 : IsCauchy2 a
    -- ε : X
    -- hε : 0 < ε
    -- ⊢ ∃ N, ∀ n ≥ N, ∀ m ≥ N, |a m - a n| < ε
    sorry


-- 1ª demostración
-- ===============

example
  (ha : Monotone a)
  (hC : ¬ IsCauchy a)
  : ∃ (ε : X) (σ : ℕ → ℕ), 0 < ε ∧ ∀ k : ℕ, k * ε ≤ a (σ^[k] 0) - a 0 :=
by
  unfold IsCauchy at hC
  -- hC : ¬∀ (ε : X), 0 < ε → ∃ N, ∀ n ≥ N, ∀ m ≥ N, |a m - a n| < ε
  push Not at hC
  -- hC : ∃ ε, 0 < ε ∧ ∀ (N : ℕ), ∃ n ≥ N, ∃ m ≥ N, ε ≤ |a m - a n|
  obtain ⟨ε, hε1, hε2⟩ := hC
  -- ε : X
  -- hε1 : 0 < ε
  -- hε2 : ∀ (N : ℕ), ∃ n ≥ N, ∃ m ≥ N, ε ≤ |a m - a n|
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
  unfold IsCauchy at hC
  -- hC : ¬∀ (ε : X), 0 < ε → ∃ N, ∀ n ≥ N, ∀ m ≥ n, |a m - a n| < ε
  push Not at hC
  -- hC : ∃ ε, 0 < ε ∧ ∀ (N : ℕ), ∃ n ≥ N, ∃ m ≥ n, ε ≤ |a m - a n|
  obtain ⟨ε, hε1, hε2⟩ := hC
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
             by rw [abs_of_nonneg (sub_nonneg.mpr (ha (hσ _)))]
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
  unfold IsCauchy at hC
  -- hC : ¬∀ (ε : X), 0 < ε → ∃ N, ∀ n ≥ N, ∀ m ≥ n, |a m - a n| < ε
  push Not at hC
  -- hC : ∃ ε, 0 < ε ∧ ∀ (N : ℕ), ∃ n ≥ N, ∃ m ≥ n, ε ≤ |a m - a n|
  obtain ⟨ε, hε1, hε2⟩ := hC
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
            by rw [abs_of_nonneg (sub_nonneg.mpr (ha (hσ _)))]
      _ ≤ a (σ m) - a 0 :=
            by linarith [ha (hτ m)]
      _ = a (σ^[k + 1] 0) - a 0 :=
            by rw [Function.iterate_succ_apply']
