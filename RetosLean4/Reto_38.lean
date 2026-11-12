-- Reto_38.lean
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
-- que demostrar que existe un N ∈ ℕ tal que
--    ∀ n ≥ N, ∀ m ≥ N, |(-a)(m) - (-a)(n)| < ε                 (1)
--
-- Puesto que a es de Cauchy, existe un N ∈ ℕ tal que
--    ∀ n ≥ N, ∀ m ≥ N, |a(m) - a(n)| < ε                       (2)
-- Veamos que con el mismo N se verifica la condición (1). Para
-- ello, sean n y m tales que
--    n ≥ N                                                     (3)
--    m ≥ N                                                     (4)
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
  -- ⊢ ∃ N, ∀ n ≥ N, ∀ m ≥ N, |(-a) m - (-a) n| < ε
  obtain ⟨N, hN⟩ := ha ε hε
  -- N : ℕ
  -- hN : ∀ n ≥ N, ∀ m ≥ N, |a m - a n| < ε
  use N
  -- ⊢ ∀ n ≥ N, ∀ m ≥ N, |(-a) m - (-a) n| < ε
  intro n hn m hm
  -- n : ℕ
  -- hn : n ≥ N
  -- m : ℕ
  -- hm : m ≥ N
  -- ⊢ |(-a) m - (-a) n| < ε
  calc |(-a) m - (-a) n|
       = |(- a m) - (- a n)| := rfl
     _ = |-(a m - a n)|      := by ring_nf
     _ = |a m - a n|         := abs_neg _
     _ < ε                   := hN n hn m hm

-- 2ª demostración
-- ===============

example
  (ha : IsCauchy a)
  : IsCauchy (-a) :=
by
  intro ε hε
  -- ε : X
  -- hε : 0 < ε
  -- ⊢ ∃ N, ∀ n ≥ N, ∀ m ≥ N, |(-a) m - (-a) n| < ε
  obtain ⟨N, hN⟩ := ha ε hε
  -- N : ℕ
  -- hN : ∀ n ≥ N, ∀ m ≥ N, |a m - a n| < ε
  refine ⟨N, fun n hn m hm => ?_⟩
  -- n : ℕ
  -- hn : n ≥ N
  -- m : ℕ
  -- hm : m ≥ N
  -- ⊢ |(-a) m - (-a) n| < ε
  calc |(-a) m - (-a) n|
       = |(- a m) - (- a n)| := rfl
     _ = |-(a m - a n)|      := congrArg abs (neg_sub' (a m) (a n)).symm
     _ = |a m - a n|         := abs_neg (a m - a n)
     _ < ε                   := hN n hn m hm

-- 3ª demostración
-- ===============

public theorem isCauchy_neg
  (ha : IsCauchy a)
  : IsCauchy (-a) :=
by
  intro ε hε
  -- ε : X
  -- hε : 0 < ε
  -- ⊢ ∃ N, ∀ n ≥ N, ∀ m ≥ N, |(-a) m - (-a) n| < ε
  obtain ⟨N, hN⟩ := ha ε hε
  -- N : ℕ
  -- hN : ∀ n ≥ N, ∀ m ≥ N, |a m - a n| < ε
  refine ⟨N, fun n hn m hm ↦ ?_⟩
  -- n : ℕ
  -- hn : n ≥ N
  -- m : ℕ
  -- hm : m ≥ N
  -- ⊢ |(-a) m - (-a) n| < ε
  rw [Pi.neg_apply, Pi.neg_apply, neg_sub_neg, abs_sub_comm]
  exact hN n hn m hm
