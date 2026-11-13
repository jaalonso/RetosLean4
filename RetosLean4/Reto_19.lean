-- Reto_19.lean
-- Las sucesiones convergentes son sucesiones de Cauchy.
-- Sevilla, 16-septiembre-2026
-- ---------------------------------------------------------------

-- ---------------------------------------------------------------
-- Demostrar que las sucesiones convergentes son de Cauchy.
-- ---------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Sea ε ∈ ℝ tal que ε > 0. Tenemos que demostrar que existe un
-- k ∈ ℕ tal que
--    ∀ n ≥ N, ∀ m ≥ N, |u(m) - u(n)| < ε                      (1)
--
-- Puesto que u es convergente, existe un a ∈ ℝ tal que el límite
-- de u es a. Por tanto, existe un N ∈ ℕ tal que
--    ∀ n ≥ N, |u(n) - a| < ε/2                                (2)
--
-- Para demostrar que con dicho N se cumple (1), sean n, m ∈ ℕ
-- tales que n ≥ N y m ≥ N. Entonces, por (2), se tiene que
--    |u(n) - a| < ε/2                                         (3)
--    |u(m) - a| < ε/2                                         (4)
-- Por tanto,
--    |u(m) - u(m)| = |(u(m) - a) + (a - u(m))|
--                  ≤ |u(m) - a|  + |a - u(m)|
--                  = |u(m) - a|  + |u(m) - a|
--                  < ε/2 + ε/2                    [por (3) y (4)]
--                  = ε

-- Demostraciones con Lean4
-- ========================

module

import Mathlib.Basic.Real.Basic
import Mathlib.Tactic
public import RetosLean4.Defs -- SeqLim, SeqConv, IsCauchy

variable {u : ℕ → ℝ}

-- 1ª demostración
-- ===============

example
  (h : SeqConv u)
  : IsCauchy u :=
by
  intros ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ N, ∀ n ≥ N, ∀ m ≥ N, |u m - u n| < ε
  obtain ⟨a, ha⟩ := h
  -- a : ℝ
  -- ha : SeqLim u a
  obtain ⟨N, hN⟩ := ha (ε/2) (by grind)
  -- N : ℕ
  -- hN : ∀ n ≥ N, |u n - a| < ε / 2
  use N
  -- ⊢ ∀ n ≥ N, ∀ m ≥ N, |u m - u n| < ε
  intros n hn m hm
  -- n : ℕ
  -- hn : n ≥ N
  -- m : ℕ
  -- hm : m ≥ N
  -- ⊢ |u m - u n| < ε
  grind

-- 2ª demostración
-- ===============

example
  (h : SeqConv u)
  : IsCauchy u :=
by
  intros ε hε
  -- ε : ℝ
  -- hε : 0 < ε
  -- ⊢ ∃ N, ∀ n ≥ N, ∀ m ≥ N, |u m - u n| < ε
  obtain ⟨a, ha⟩ := h
  -- a : ℝ
  -- ha : SeqLim u a
  obtain ⟨N, hN⟩ := ha (ε/2) (by grind)
  -- N : ℕ
  -- hN : ∀ n ≥ N, |u n - a| < ε / 2
  use N
  -- ⊢ ∀ n ≥ N, ∀ m ≥ N, |u m - u n| < ε
  intros n hn m hm
  -- n : ℕ
  -- hn : n ≥ N
  -- m : ℕ
  -- hm : m ≥ N
  -- ⊢ |u m - u n| < ε
  calc |u m - u n|
       = |(u m - a) + (a - u n)| := by grind
     _ ≤ |u m - a|  + |a - u n|  := by grind
     _ = |u m - a|  + |u n - a|  := by grind
     _ < ε                       := by grind

-- 3ª demostración
-- ===============

example
  (h : SeqConv u)
  : IsCauchy u :=
by
  intros ε hε
  -- ε : ℝ
  -- hε : 0 < ε
  -- ⊢ ∃ N, ∀ n ≥ N, ∀ m ≥ N, |u m - u n| < ε
  obtain ⟨a, ha⟩ := h
  -- a : ℝ
  -- ha : SeqLim u a
  obtain ⟨N, hN⟩ := ha (ε/2) (by positivity)
  -- N : ℕ
  -- hN : ∀ n ≥ N, |u n - a| < ε / 2
  use N
  -- ⊢ ∀ n ≥ N, ∀ m ≥ n, |u m - u n| < ε
  intros n hn m hm
  -- n : ℕ
  -- hn : n ≥ N
  -- m : ℕ
  -- hm : m ≥ N
  -- ⊢ |u m - u n| < ε
  have h1 : |u n - a| < ε / 2 := hN n hn
  have h2 : |u m - a| < ε / 2 := hN m hm
  calc |u m - u n|
       = |(u m - a) + (a - u n)| := by ring_nf
     _ ≤ |u m - a| + |a - u n|   := abs_add_le _ _
     _ = |u m - a| + |u n - a|   := by simp [abs_sub_comm]
     _ < ε / 2 + ε / 2           := by gcongr
     _ = ε                       := by ring

-- 4ª demostración
-- ===============

public theorem isCauchy_of_SeqConv
  (h : SeqConv u)
  : IsCauchy u :=
by
  intros ε hε
  -- ε : ℝ
  -- hε : 0 < ε
  -- ⊢ ∃ N, ∀ n ≥ N, ∀ m ≥ N, |u m - u n| < ε
  obtain ⟨a, ha⟩ := h
  -- a : ℝ
  -- ha : SeqLim u a
  obtain ⟨N, hN⟩ := ha (ε/2) (half_pos hε)
  -- N : ℕ
  -- hN : ∀ n ≥ N, |u n - a| < ε / 2
  use N
  -- ⊢ ∀ n ≥ N, ∀ m ≥ N, |u m - u n| < ε
  intros n hn m hm
  -- n : ℕ
  -- hn : n ≥ N
  -- m : ℕ
  -- hm : m ≥ N
  -- ⊢ |u m - u n| < ε
  calc |u m - u n|
       = |(u m - a) + (a - u n)| :=
           congrArg abs (sub_add_sub_cancel (u m) a (u n)).symm
     _ ≤ |u m - a|  + |a - u n| :=
           abs_add_le (u m - a) (a - u n)
     _ = |u m - a|  + |u n - a| :=
           congrArg (|u m - a| + ·) (abs_sub_comm a (u n))
     _ < ε / 2 + ε / 2 :=
           add_lt_add (hN m hm) (hN n hn)
     _ = ε :=
           add_halves ε

-- Lemas usados
-- ============

/-
variable (a b c d : ℝ)
variable (f : ℝ → ℝ)
#check (abs_add_le a b : |a + b| ≤ |a| + |b|)
#check (abs_sub_comm a b : |a - b| = |b - a|)
#check (add_halves a : a / 2 + a / 2 = a)
#check (add_left_cancel_iff : a + b = a + c ↔ b = c)
#check (add_lt_add : a < b → c < d → a + c < b + d)
#check (congrArg f : a = b → f a = f b)
#check (half_pos : 0 < a → 0 < a / 2)
#check (sub_add_sub_cancel a b c : (a - b) + (b - c) = a - c)
-/
