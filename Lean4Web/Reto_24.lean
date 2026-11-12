-- Reto_24.lean
-- La sucesión 1, -1, 1, -1,... no es convergente (2ª versión)
-- Sevilla, 19-octubre-2026
-- ---------------------------------------------------------------

-- ---------------------------------------------------------------
-- Usando el Reto 22 (que afirma que si una sucesión tiene dos
-- subsucesiones que convergen a límites distintos, entonces la
-- sucesión no es convergente) demostrar que la sucesión definida
-- por 1, -1, 1, -1, ... no es convergente.
--
-- Para ello, completar la siguiente teoría:
--    import Mathlib.Tactic
--
--    -- a converge a L
--    def SeqLim (a : ℕ → ℝ) (L : ℝ) : Prop :=
--      ∀ ε > 0, ∃ k : ℕ, ∀ n ≥ k, |a n - L| < ε
--
--    -- La sucesión a es convergente
--    def SeqConv (a : ℕ → ℝ) : Prop :=
--      ∃ L, SeqLim a L
--
--    -- φ es una función de extracción.
--    def IsExtraction (φ : ℕ → ℕ) : Prop :=
--      StrictMono φ
--
--    -- b es una subsucesión de a.
--    def Subseq (b a : ℕ → ℝ) : Prop :=
--      ∃ φ, IsExtraction φ ∧ b = a ∘ φ
--
--    variable {a : ℕ → ℝ}
--
--    example
--      (ha : ∀ n, a n = (-1)^n)
--      : ¬SeqConv a :=
--    by sorry
-- ---------------------------------------------------------------

-- Demostración en lenguaje natural
-- ================================

-- Por el Reto 22, basta demostrar que la sucesión a tiene dos
-- subsucesiones que convergen a límites distintos. Para ello,
-- consideramos las funciones φ₁ y φ₂ de ℕ en ℕ definidas por
--    φ₁(n) = 2n
--    φ₂(n) = 2n + 1
-- Ambas son funciones de extracción ya que, para todo i, j ∈ ℕ
-- con i < j, se tiene que
--    φ₁(i) = 2i < 2j = φ₁(j)
--    φ₂(i) = 2i + 1 < 2j + 1 = φ₂(j)
-- Definimos las subsucesiones de a
--    b₁ = a ∘ φ₁
--    b₂ = a ∘ φ₂
-- Ambas subsucesiones son constantes (b₁ vale 1 y b₂ vale -1), ya
-- que para todo n ∈ ℕ
--    b₁(n) = a(2n) = (-1)²ⁿ = 1
--    b₂(n) = a(2n + 1) = (-1)²ⁿ⁺¹ = -1
-- Luego, aplicando el Reto 23 que dice "toda sucesión constante
-- converge a su valor", b₁ converge a 1 y b₂ converge a -1. Como
-- 1 ≠ -1, a tiene dos subsucesiones con límites distintos y, por
-- el Reto 22, no es convergente.

-- Demostraciones en Lean 4
-- ========================

import Mathlib.Tactic

variable {a : ℕ → ℝ}

-- Definiciones
-- ============

-- L es el límite de la sucesión a.
def SeqLim (a : ℕ → ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ k : ℕ, ∀ n ≥ k, |a n - L| < ε

-- La sucesión a es convergente.
def SeqConv (a : ℕ → ℝ) : Prop :=
  ∃ L, SeqLim a L

-- φ es una función de extracción.
def IsExtraction (φ : ℕ → ℕ) : Prop :=
  StrictMono φ

-- v es una subsucesión de u.
def Subseq (v u : ℕ → ℝ) : Prop :=
  ∃ φ, IsExtraction φ ∧ v = u ∘ φ

-- Lemas auxiliares demostrados en retos anteriores
-- ================================================

lemma seqLim_unique -- del Reto 9
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

lemma seqLim_of_subseq -- del reto 21
  {u v : ℕ → ℝ}
  {a : ℝ}
  (hv : Subseq v u)
  (ha : SeqLim u a)
  : SeqLim v a :=
by
  obtain ⟨φ, hφ, rfl⟩ := hv
  -- φ : ℕ → ℕ
  -- hφ : IsExtraction φ
  -- ⊢ SeqLim (u ∘ φ) a
  intros ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ∃ k, ∀ n ≥ k, |(u ∘ φ) n - a| < ε
  obtain ⟨k, hk⟩ := ha ε hε
  -- k : ℕ
  -- hk : ∀ n ≥ k, |u n - a| < ε
  exact ⟨k, fun n hn ↦ hk (φ n) (le_trans hn hφ.le_apply)⟩

lemma not_seqConv_of_subseq_seqLim_ne -- del Reto 22
  (hb₁ : Subseq b₁ a)
  (hL₁ : SeqLim b₁ L₁)
  (hb₂ : Subseq b₂ a)
  (hL₂ : SeqLim b₂ L₂)
  (h : L₁ ≠ L₂)
  : ¬SeqConv a :=
by
  rintro ⟨L, hL⟩
  -- L : ℝ
  -- hL : SeqLim a L
  -- ⊢ False
  exact h ((seqLim_unique hL₁ (seqLim_of_subseq hb₁ hL)).trans
           (seqLim_unique (seqLim_of_subseq hb₂ hL) hL₂))

lemma seqLim_const -- del Reto 23
  (h : ∀ n, a n = L)
  : SeqLim a L :=
by
  intro ε hε
  -- ε : ℝ
  -- hε : ε > 0
  -- ⊢ ⊢ ∃ k, ∀ n ≥ k, |a n - L| < ε
  use 0
  -- ⊢ ∀ n ≥ 0, |a n - L| < ε
  rintro n -
  -- n : ℕ
  -- ⊢ |a n - L| < ε
  calc |a n - L|
     = |L - L|    := congrArg (|· - L|) (h n)
   _ = |0|        := congrArg abs (sub_self L)
   _ = 0          := abs_zero
   _ < ε          := hε

-- Soluciones del ejercicio
-- ========================

-- 1ª demostración
-- ===============

lemma isExtraction_even : IsExtraction (fun n => 2 * n) :=
by
  intro i j hij
  -- i j : ℕ
  -- hij : i < j
  -- ⊢ (fun n => 2 * n) i < (fun n => 2 * n) j
  dsimp
  -- ⊢ 2 * i < 2 * j
  omega

lemma isExtraction_odd : IsExtraction (fun n => 2 * n + 1) :=
by
  intro i j hij
  -- i j : ℕ
  -- hij : i < j
  -- ⊢ (fun n => 2 * n + 1) i < (fun n => 2 * n + 1) j
  dsimp
  -- ⊢ 2 * i + 1 < 2 * j + 1
  omega

lemma seq_even
  (ha : ∀ n, a n = (-1)^n)
  (n : ℕ)
  : a (2 * n) = 1 :=
by
  calc a (2 * n)
         = (-1) ^ (2 * n) := ha (2 * n)
       _ = 1              := by simp

lemma seq_odd
  (ha : ∀ n, a n = (-1)^n)
  (n : ℕ)
  : a (2 * n + 1) = -1 :=
by
  calc a (2 * n + 1)
         = (-1) ^ (2 * n + 1) := ha (2 * n + 1)
       _ = -1                 := by simp [pow_succ]

example
  (ha : ∀ n, a n = (-1)^n)
  : ¬SeqConv a :=
by
  let φ₁ := fun n : ℕ => 2 * n
  let φ₂ := fun n : ℕ => 2 * n + 1
  have hb₁ : Subseq (a ∘ φ₁) a := ⟨φ₁, isExtraction_even, rfl⟩
  have hb₂ : Subseq (a ∘ φ₂) a  := ⟨φ₂, isExtraction_odd, rfl⟩
  have hL₁ : SeqLim (a ∘ φ₁) 1 :=
    seqLim_const (fun n => seq_even ha n)
  have hL₂ : SeqLim (a ∘ φ₂) (-1) :=
    seqLim_const (fun n => seq_odd ha n)
  have h : (1:ℝ) ≠ -1 := by norm_num
  exact not_seqConv_of_subseq_seqLim_ne hb₁ hL₁ hb₂ hL₂ h

-- 2ª demostración
-- ===============

example
  (ha : ∀ n, a n = (-1)^n)
  : ¬SeqConv a :=
by
  have h1 : IsExtraction (fun n => 2 * n) := isExtraction_even
  have hb₁ : Subseq (a ∘ fun n => 2 * n) a := ⟨_, h1, rfl⟩
  have hL₁ : SeqLim (a ∘ fun n => 2 * n) 1 :=
    seqLim_const (fun n => seq_even ha n)
  have h2 : IsExtraction (fun n => 2 * n + 1) := isExtraction_odd
  have hb₂ : Subseq (a ∘ fun n => 2 * n + 1) a := ⟨_, h2, rfl⟩
  have hL₂ : SeqLim (a ∘ fun n => 2 * n + 1) (-1) :=
    seqLim_const (fun n => seq_odd ha n)
  exact not_seqConv_of_subseq_seqLim_ne hb₁ hL₁ hb₂ hL₂ (by norm_num)

-- 3ª demostración
-- ===============

theorem not_seqConv_neg_one_pow
  (ha : ∀ n, a n = (-1)^n)
  : ¬SeqConv a :=
not_seqConv_of_subseq_seqLim_ne
  ⟨_, isExtraction_even, rfl⟩
  (seqLim_const (fun n => seq_even ha n))
  ⟨_, isExtraction_odd, rfl⟩
  (seqLim_const (fun n => seq_odd ha n))
  (by norm_num)

-- Soluciones colaborativas
-- ========================

-- Solución C1
-- ===========

example
  (ha : ∀ n, a n = (-1)^n)
  : ¬SeqConv a :=
by
  refine not_seqConv_of_subseq_seqLim_ne
    (b₁ := fun n => a (2 * n))
    (b₂ := fun n => a (2 * n + 1))
    (L₁ := 1)
    (L₂ := -1)
    ⟨fun n => 2 * n,
     fun i j hij => by show 2 * i < 2 * j; omega,
     rfl⟩
    ?_
    ⟨fun n => 2 * n + 1,
     fun i j hij => by show 2 * i + 1 < 2 * j + 1; omega,
     rfl⟩
    ?_
    (by norm_num)
  · -- ⊢ SeqLim (fun n => a (2 * n)) 1
    refine seqLim_const (fun n => ?_)
    -- ⊢ a (2 * n) = 1
    rw [ha, pow_mul]
    -- ⊢ ((-1) ^ 2) ^ n = 1
    norm_num
  · -- ⊢ SeqLim (fun n => a (2 * n + 1)) (-1)
    refine seqLim_const (fun n => ?_)
    -- ⊢ a (2 * n + 1) = -1
    rw [ha, pow_succ, pow_mul]
    -- ⊢ ((-1) ^ 2) ^ n * -1 = -1
    norm_num
