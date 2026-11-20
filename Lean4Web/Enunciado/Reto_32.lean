-- ---------------------------------------------------------------
-- Una subsucesión se obtiene aplicando a la sucesión original una
-- función de extracción; es decir, una función φ : ℕ → ℕ
-- estrictamente creciente. Por ejemplo, la subsucesión
--    u₀, u₂, u₄, u₆, ...
-- se obtiene con la función de extracción φ definida por
-- φ(n) = 2n.
--
-- Demostrar que si
--    ∀ n, φ(n) < φ (n+1),
-- entonces φ es una función de extracción.
-- ---------------------------------------------------------------

import Mathlib.Basic.Real.Basic

def IsExtraction (φ : ℕ → ℕ) : Prop :=
  StrictMono φ

variable (φ : ℕ → ℕ)

example
  (hφ : ∀ n, φ n < φ (n + 1))
  : IsExtraction φ :=
by
  sorry
