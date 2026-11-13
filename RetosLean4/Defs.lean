-- Defs.lean
-- Definiciones usadas en los retos de demostración en Lean 4.
-- -----------------------------------------------------------

module

public import Mathlib.Basic.Real.Basic

@[expose] public section

-- L es el límite de la sucesión a.
def SeqLim (a : ℕ → ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ k : ℕ, ∀ n ≥ k, |a n - L| < ε

-- La sucesión a es convergente.
def SeqConv (a : ℕ → ℝ) : Prop :=
  ∃ L, SeqLim a L

-- La sucesión a está acotada.
def SeqBdd (a : ℕ → ℝ) : Prop :=
  ∃ M > 0, ∀ n, |a n| ≤ M

-- M es una cota superior de la sucesión a.
def IsUB (a : ℕ → ℝ) (M : ℝ) : Prop :=
  ∀ n, a n ≤ M

-- a es una sucesión de Cauchy.
def IsCauchy {X : Type*} [AddGroup X] [Lattice X] (a : ℕ → X) : Prop :=
  ∀ (ε : X), 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ N, |a m - a n| < ε

-- φ es una función de extracción.
def IsExtraction (φ : ℕ → ℕ) : Prop :=
  StrictMono φ

-- v es una subsucesión de u.
def Subseq (v u : ℕ → ℝ) : Prop :=
  ∃ φ, IsExtraction φ ∧ v = u ∘ φ

-- a es una sucesión acotada superiormente.
def SeqBddAbove {X : Type*} [LE X] (a : ℕ → X) : Prop :=
  ∃ M : X, ∀ n, a n ≤ M

-- a es una sucesión acotada superiormente.
def SeqBddBelow {X : Type*} [LE X] (a : ℕ → X) : Prop :=
  ∃ M : X, ∀ n, M ≤ a n

-- n es un pico de la sucesión a
def IsAPeak {X : Type*} [LinearOrder X] (a : ℕ → X) (n : ℕ) : Prop :=
  ∀ m > n, a m ≤ a n

-- los picos de la sucesión a no están acotados
def UnBddPeaks {X : Type*} [LinearOrder X] (a : ℕ → X) : Prop :=
  ∀ k, ∃ n > k, IsAPeak a n
