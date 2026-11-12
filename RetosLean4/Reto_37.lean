-- Reto_37.lean
-- Si una sucesión es de Cauchy, entonces su opuesta también lo es.
-- José A. Alonso Jiménez <https://jaalonso.github.io>
-- Sevilla, 11-noviembre-2026
-- ---------------------------------------------------------------

-- ---------------------------------------------------------------
-- Demostrar que si una sucesión es de Cauchy, entonces su opuesta
-- también lo es.
-- ---------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Supongamos que la sucesión a es de Cauchy. Tenemos que
-- demostrar que -a también lo es. Para ello, sea ε > 0. Tenemos
-- que demostrar que existe un k ∈ ℕ tal que
--    ∀ n ≥ k, ∀ m ≥ n, |(-a)(m) - (-a)(n)| < ε                 (1)
--
-- Puesto que a es de Cauchy, existe un k ∈ ℕ tal que
--    ∀ n ≥ k, ∀ m ≥ n, |a(m) - a(n)| < ε                       (2)
-- Veamos que con el mismo k se verifica la condición (1). Para
-- ello, sean n y m tales que
--    n ≥ k                                                     (3)
--    m ≥ n                                                     (4)
-- Entonces
--    |(-a)(m) - (-a)(n)| = |(-a(m)) - (-a(n))|
--                        = |-(a(m) - a(n))|
--                        = |a(m) - a(n)|
--                        < ε                  [por (2), (3) y (4)]

-- Demostraciones en Lean 4
-- ========================

module

public import Mathlib.Tactic
public import RetosLean4.Defs -- IsCauchy

variable {X : Type*} [NormedField X] [Lattice X]
variable {a : ℕ → X}

-- 1ª demostración
-- ===============

example
  (ha : IsCauchy a)
  : IsCauchy (-a) :=
by
  intro ε hε
  -- ε : X
  -- hε : 0 < ε
  -- ⊢ ∃ k, ∀ n ≥ k, ∀ m ≥ n, |(-a) m - (-a) n| < ε
  obtain ⟨k, hk⟩ := ha ε hε
  -- k : ℕ
  -- hk : ∀ n ≥ k, ∀ m ≥ n, |a m - a n| < ε
  use k
  -- ⊢ ∀ n ≥ k, ∀ m ≥ n, |(-a) m - (-a) n| < ε
  intro n hn m hm
  -- n : ℕ
  -- hn : n ≥ k
  -- m : ℕ
  -- hm : m ≥ n
  -- ⊢ |(-a) m - (-a) n| < ε
  calc |(-a) m - (-a) n|
       = |(- a m) - (- a n)| := rfl
     _ = |-(a m - a n)|      := by ring_nf
     _ = |a m - a n|         := abs_neg _
     _ < ε                   := hk n hn m hm

-- 2ª demostración
-- ===============

public theorem isCauchy_neg
  (ha : IsCauchy a)
  : IsCauchy (-a) :=
by
  intro ε hε
  -- ε : X
  -- hε : 0 < ε
  -- ⊢ ∃ k, ∀ n ≥ k, ∀ m ≥ n, |(-a) m - (-a) n| < ε
  obtain ⟨k, hk⟩ := ha ε hε
  -- k : ℕ
  -- hk : ∀ n ≥ k, ∀ m ≥ n, |a m - a n| < ε
  refine ⟨k, fun n hn m hm => ?_⟩
  -- n : ℕ
  -- hn : n ≥ k
  -- m : ℕ
  -- hm : m ≥ n
  -- ⊢ |(-a) m - (-a) n| < ε
  calc |(-a) m - (-a) n|
       = |(- a m) - (- a n)| := rfl
     _ = |-(a m - a n)|      := congrArg abs (neg_sub' (a m) (a n)).symm
     _ = |a m - a n|         := abs_neg (a m - a n)
     _ < ε                   := hk n hn m hm

-- 3ª demostración
-- ===============

example
  (ha : IsCauchy a)
  : IsCauchy (-a) :=
by
  intro ε hε
  -- ε : X
  -- hε : 0 < ε
  -- ⊢ ∃ k, ∀ n ≥ k, ∀ m ≥ n, |(-a) m - (-a) n| < ε
  obtain ⟨k, hk⟩ := ha ε hε
  -- k : ℕ
  -- hk : ∀ n ≥ k, ∀ m ≥ n, |a m - a n| < ε
  refine ⟨k, fun n hn m hm ↦ ?_⟩
  -- n : ℕ
  -- hn : n ≥ k
  -- m : ℕ
  -- hm : m ≥ n
  -- ⊢ |(-a) m - (-a) n| < ε
  rw [Pi.neg_apply, Pi.neg_apply, neg_sub_neg, abs_sub_comm]
  exact hk n hn m hm
