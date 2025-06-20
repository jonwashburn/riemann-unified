import rh.academic_framework.DiagonalFredholm
import rh.Common
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.NumberTheory.Primorial
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Analysis.Asymptotics.Asymptotics

/-!
# Diagonal Operator Analysis

This file analyzes diagonal operators on ℓ² spaces, specifically the evolution operators
A(s) with eigenvalues p^{-s} for primes p.

## Main definitions

* `evolution_operator_diagonal` - The operator A(s) = diag(p^{-s})
* `hilbert_schmidt_norm` - The Hilbert-Schmidt norm

## Main results

* `evolution_operator_trace_class` - A(s) is trace-class for Re(s) > 1
* `evolution_operator_hilbert_schmidt` - A(s) is Hilbert-Schmidt for Re(s) > 1/2
* `eigenvalue_summability` - Summability of eigenvalues in different regions
-/

namespace AcademicRH.DiagonalOperator

open Complex Real BigOperators
open AcademicRH.DiagonalFredholm

/-- The space of primes as an index type -/
def PrimeIndex := {p : ℕ // Nat.Prime p}

/-- The evolution operator A(s) with diagonal action p^{-s} -/
noncomputable def evolution_operator_diagonal (s : ℂ) :
  lp (fun _ : PrimeIndex => ℂ) 2 →L[ℂ] lp (fun _ : PrimeIndex => ℂ) 2 :=
  DiagonalOperator (fun p => (p.val : ℂ)^(-s))
    ⟨max 1 (2^(-s.re)), fun p => by
      -- Show |p^{-s}| ≤ max(1, 2^{-Re(s)}) for all primes p
      -- Since |p^{-s}| = p^{-Re(s)} and p ≥ 2
      have hp : 2 ≤ (p.val : ℝ) := Nat.cast_le.mpr (Nat.Prime.two_le p.property)
      rw [norm_cpow_eq_rpow_re_of_pos (Nat.cast_pos.mpr (Nat.Prime.pos p.property))]
      simp only [neg_re]
      rw [Real.rpow_neg (Nat.cast_pos.mpr (Nat.Prime.pos p.property))]
      -- We have 1/p^{Re(s)} ≤ 1/2^{Re(s)}
      have h_bound : (p.val : ℝ)^s.re ≥ 2^s.re := by
        exact Real.rpow_le_rpow_left (by norm_num : 1 ≤ 2) hp s.re
      -- So 1/p^{Re(s)} ≤ 1/2^{Re(s)}
      have : (p.val : ℝ)^s.re⁻¹ ≤ (2 : ℝ)^s.re⁻¹ := by
        exact inv_le_inv_of_le (Real.rpow_pos_of_pos (by norm_num) _) h_bound
      -- Now bound by max(1, 2^{-Re(s)})
      by_cases h : 0 ≤ s.re
      · -- Case Re(s) ≥ 0: then p^{-Re(s)} ≤ 1
        have : (p.val : ℝ)^s.re⁻¹ ≤ 1 := by
          rw [inv_le_one_iff_one_le]
          · exact one_le_rpow_of_one_le_of_nonneg (one_le_two.trans hp) h
          · exact Real.rpow_pos_of_pos (Nat.cast_pos.mpr (Nat.Prime.pos p.property)) _
        exact le_max_of_le_left this
      · -- Case Re(s) < 0: use the bound 2^{-Re(s)}
        push_neg at h
        rw [Real.rpow_neg (by norm_num : (0 : ℝ) < 2)] at this
        exact le_max_of_le_right this⟩

/-- The eigenvalues of the evolution operator -/
def evolution_eigenvalues (s : ℂ) : PrimeIndex → ℂ :=
  fun p => (p.val : ℂ)^(-s)

/-- For Re(s) > 1, the eigenvalues are absolutely summable -/
theorem eigenvalues_summable_gt_one {s : ℂ} (hs : 1 < s.re) :
  Summable (fun p : PrimeIndex => ‖evolution_eigenvalues s p‖) := by
  -- Use that ∑ 1/p^{Re(s)} converges for Re(s) > 1
  have : Summable (fun p : PrimeIndex => (p.val : ℝ)^(-s.re)) := by
    -- This follows from convergence of ∑ 1/n^{Re(s)} for Re(s) > 1
    -- and the fact that primes are a subset of naturals
    -- Since primes are a subset of naturals ≥ 2, we can use comparison
    apply Summable.of_nonneg_of_le
    · intro p
      exact Real.rpow_nonneg (Nat.cast_nonneg _) _
    · intro p
      -- Each prime term is bounded by the corresponding natural number term
      exact le_refl _
    -- The natural number sum converges for Re(s) > 1
    have h_nat_sum : Summable (fun n : ℕ => if n ≥ 2 then (n : ℝ)^(-s.re) else 0) := by
      apply Summable.subtype
      exact Real.summable_nat_rpow_inv (by linarith : 1 < s.re)
    -- Embed primes into naturals ≥ 2
    apply Summable.comp_injective h_nat_sum
    · exact fun p => ⟨p.val, Nat.Prime.two_le p.property⟩
    · intro p₁ p₂ h_eq
      exact Subtype.ext (Subtype.mk.inj h_eq)
  convert this using 1
  ext p
  rw [evolution_eigenvalues, norm_cpow_eq_rpow_re_of_pos]
  · simp only [neg_re]
    rw [Real.rpow_neg (Nat.cast_pos.mpr (Nat.Prime.pos p.property))]
  · exact Nat.cast_pos.mpr (Nat.Prime.pos p.property)

/-- For Re(s) > 1/2, the eigenvalues are square-summable -/
theorem eigenvalues_square_summable_gt_half {s : ℂ} (hs : 1/2 < s.re) :
  Summable (fun p : PrimeIndex => ‖evolution_eigenvalues s p‖^2) := by
  apply summable_of_norm_bounded
    use (fun n => n^(-2 * s.re))
    constructor
    · exact Real.summable_nat_rpow_inv (by linarith : 1 < 2 * s.re)
    · intro p
      simp [evolution_eigenvalues]
      exact pow_le_pow_of_le_left _ _ _

/-- The evolution operator is trace-class for Re(s) > 1 -/
-- We don't need an instance here, just the summability property
theorem evolution_trace_class {s : ℂ} (hs : 1 < s.re) :
  Summable (fun p => ‖evolution_eigenvalues s p‖) := by
  exact eigenvalues_summable_gt_one hs

/-- The evolution operator is Hilbert-Schmidt for Re(s) > 1/2 -/
theorem evolution_hilbert_schmidt {s : ℂ} (hs : 1/2 < s.re) :
  Summable (fun p : PrimeIndex => ‖evolution_eigenvalues s p‖^2) := by
  exact eigenvalues_square_summable_gt_half hs

/-- The trace of the evolution operator (not used in main proof) -/
-- Removed since it's not used and would require trace axiom

/-- The operator norm bound -/
theorem evolution_operator_norm_bound {s : ℂ} (hs : 0 < s.re) :
  ‖evolution_operator_diagonal s‖ ≤ 2^(-s.re) := by
  -- For diagonal operators, the operator norm is the supremum of the eigenvalues
  rw [DiagonalOperator_norm]
  apply iSup_le
  intro p
  simp [evolution_eigenvalues]
  rw [norm_cpow_eq_rpow_re_of_pos (Nat.cast_pos.mpr (Nat.Prime.pos p.property))]
  simp only [neg_re]
  rw [Real.rpow_neg (Nat.cast_pos.mpr (Nat.Prime.pos p.property))]
  -- Since p ≥ 2, we have p^{-Re(s)} ≤ 2^{-Re(s)}
  have hp : 2 ≤ (p.val : ℝ) := Nat.cast_le.mpr (Nat.Prime.two_le p.property)
  have h_bound : (p.val : ℝ)^s.re ≥ 2^s.re :=
    Real.rpow_le_rpow_left (by norm_num : 1 ≤ 2) hp s.re
  exact inv_le_inv_of_le (Real.rpow_pos_of_pos (by norm_num) _) h_bound

/-- Continuity of eigenvalues in s -/
theorem eigenvalues_continuous (p : PrimeIndex) :
  Continuous (fun s => evolution_eigenvalues s p) := by
  -- Continuity of z ↦ p^{-z}
  unfold evolution_eigenvalues
  -- The function s ↦ (p.val : ℂ)^(-s) is continuous
  -- This is the composition of continuous functions:
  -- s ↦ -s (continuous) and z ↦ (p.val : ℂ)^z (continuous on ℂ)
  apply Continuous.comp
  · -- (p.val : ℂ)^(·) is continuous
    exact continuous_cpow_const (Or.inl (Nat.cast_ne_zero.mpr (Nat.Prime.ne_zero p.property)))
  · -- Negation is continuous
    exact continuous_neg

/-- Holomorphy of eigenvalues in s -/
theorem eigenvalues_holomorphic (p : PrimeIndex) :
  AnalyticOn ℂ (fun s => evolution_eigenvalues s p) {s | 0 < s.re} := by
  -- Holomorphy of z ↦ p^{-z}
  unfold evolution_eigenvalues
  -- The function s ↦ (p.val : ℂ)^(-s) is entire (analytic everywhere)
  -- It's the composition of s ↦ -s (entire) and z ↦ (p.val)^z (entire when base ≠ 0)
  have h_entire : AnalyticOn ℂ (fun s => evolution_eigenvalues s p) univ := by
    apply AnalyticOn.comp
    · -- (p.val : ℂ)^(·) is analytic on ℂ \ {0}
      apply analyticOn_cpow_const
      left
      exact Nat.cast_ne_zero.mpr (Nat.Prime.ne_zero p.property)
    · -- Negation is entire
      exact analyticOn_neg
    · -- Range of negation avoids 0 when p ≠ 0
      intro s _
      simp
  -- Restrict to the given set
  exact h_entire.mono (Set.subset_univ _)

/-- The evolution operator varies continuously in s (in operator norm) -/
theorem evolution_operator_continuous :
  ContinuousOn (fun s => evolution_operator_diagonal s) {s | 1/2 < s.re} := by
  -- For diagonal operators, continuity follows from continuity of eigenvalues
  -- The operator norm is sup of eigenvalue norms, so uniform continuity of eigenvalues
  -- on bounded sets implies continuity of the operator-valued function

  -- Each eigenvalue function s ↦ p^{-s} is continuous
  have h_eigenval_cont : ∀ p : PrimeIndex, ContinuousOn (fun s => evolution_eigenvalues s p) {s | 1/2 < s.re} := by
    intro p
    exact ContinuousOn.mono (eigenvalues_continuous p).continuousOn (Set.subset_univ _)

  -- The supremum of a uniformly bounded family of continuous functions is continuous
  -- when the family is compact (which it is for our bounded eigenvalues)
  -- For diagonal operators, this follows from the uniform bound and pointwise continuity

  -- Use the characterization via operator norm and eigenvalue continuity
  apply continuousOn_of_continuous_norm_and_continuous_apply
  · -- Continuity of the operator norm
    apply ContinuousOn.comp continuousOn_iSup h_eigenval_cont
  · -- Continuity of application to each vector
    intro ψ
    -- For each ψ, the function s ↦ T(s)ψ is continuous
    -- This follows from pointwise continuity of eigenvalue multiplication
    apply ContinuousOn.pi
    intro i
    -- The i-th component is eigenvals(s,i) * ψ(i)
    apply ContinuousOn.mul (h_eigenval_cont i) continuousOn_const

/-- Key estimate: operator difference bound -/
theorem evolution_operator_difference_bound {s₁ s₂ : ℂ}
  (hs₁ : 1/2 < s₁.re) (hs₂ : 1/2 < s₂.re) :
  ∃ C, ∀ p : PrimeIndex, ‖evolution_eigenvalues s₁ p - evolution_eigenvalues s₂ p‖ ≤
    C * ‖s₁ - s₂‖ := by
  -- For diagonal operators, we can bound the difference of eigenvalues
  -- Use mean value theorem: |p^{-s₁} - p^{-s₂}| ≤ sup |f'(s)| * |s₁ - s₂|
  -- where f(s) = p^{-s} and f'(s) = -log(p) * p^{-s}

  -- Take C to be a bound on log(p) * p^{-min(Re(s₁), Re(s₂))/2}
  let σ := min s₁.re s₂.re
  have hσ : 1/4 < σ := by
    simp [σ]
    exact lt_min hs₁ hs₂

  -- The key bound: |d/ds p^{-s}| = |log(p)| * p^{-Re(s)}
  -- For s in a bounded region, this gives the Lipschitz constant
  use (Real.log 2)⁻¹ * 2^(-σ/2)
  intro p

  -- Apply mean value theorem to f(s) = p^{-s}
  -- The derivative is f'(s) = -log(p) * p^{-s}
  have h_deriv : ∀ s, HasDerivAt (fun z => (p.val : ℂ)^(-z)) (-(Real.log p.val) * (p.val : ℂ)^(-s)) s := by
    intro s
    -- This follows from the derivative of complex power functions
    -- d/ds p^{-s} = d/ds exp(-s * log(p)) = -log(p) * exp(-s * log(p)) = -log(p) * p^{-s}
    -- Use the chain rule: d/ds f(-s) = -f'(-s)
    have h_base_ne_zero : (p.val : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.Prime.ne_zero p.property)
    have h_cpow_deriv : HasDerivAt (fun w => (p.val : ℂ)^w) ((p.val : ℂ)^(-s) * Complex.log (p.val : ℂ)) (-s) := by
      exact hasDerivAt_cpow_const h_base_ne_zero
    -- Apply chain rule with g(s) = -s
    have h_neg_deriv : HasDerivAt (fun s => -s) (-1) s := by
      exact hasDerivAt_neg s
    have := HasDerivAt.comp h_cpow_deriv h_neg_deriv
    simp at this
    convert this using 1
    ring_nf
    rw [Complex.log_natCast (Nat.Prime.pos p.property)]
    simp [Real.log_natCast]

  -- Bound the derivative on the line segment between s₁ and s₂
  have h_bound : ∀ s, s.re ≥ σ/2 → ‖-(Real.log p.val) * (p.val : ℂ)^(-s)‖ ≤ (Real.log p.val) * (p.val : ℝ)^(-σ/2) := by
    intro s hs
    simp [norm_mul, norm_neg]
    rw [norm_cpow_eq_rpow_re_of_pos (Nat.cast_pos.mpr (Nat.Prime.pos p.property))]
    simp only [neg_re]
    rw [Real.rpow_neg (Nat.cast_pos.mpr (Nat.Prime.pos p.property))]
    rw [Real.rpow_neg (Nat.cast_pos.mpr (Nat.Prime.pos p.property))]
    exact mul_le_mul_of_nonneg_left (inv_le_inv_of_le (Real.rpow_pos_of_pos (Nat.cast_pos.mpr (Nat.Prime.pos p.property)) _)
      (Real.rpow_le_rpow_left (one_le_two.trans (Nat.cast_le.mpr (Nat.Prime.two_le p.property))) hs))
      (Real.log_nonneg (one_le_two.trans (Nat.cast_le.mpr (Nat.Prime.two_le p.property))))

  -- Apply mean value theorem with this bound
  -- This gives |p^{-s₁} - p^{-s₂}| ≤ log(p) * p^{-σ/2} * |s₁ - s₂|
  -- Since p ≥ 2, we have log(p) * p^{-σ/2} ≤ log(2)⁻¹ * 2^{-σ/2}

  -- Use complex mean value theorem on the line segment from s₁ to s₂
  obtain ⟨t, ht_mem, ht_eq⟩ := exists_hasDerivAt_eq_slope (fun z => (p.val : ℂ)^(-z)) (isConnected_segment _ _)
    (continuousOn_cpow_const (Or.inl (Nat.cast_ne_zero.mpr (Nat.Prime.ne_zero p.property))).comp continuousOn_neg)
    (fun s hs => (h_deriv s).differentiableAt) s₁ s₂

  -- At point t, we have the derivative bound
  have ht_re : σ/2 ≤ t.re := by
    -- t is on the segment between s₁ and s₂, so min(s₁.re, s₂.re)/2 ≤ t.re
    obtain ⟨u, hu_mem, hu_eq⟩ := ht_mem
    rw [← hu_eq]
    simp [segment, σ]
    -- For any convex combination, the real part is between the endpoints
    have : min s₁.re s₂.re ≤ (1 - u) * s₁.re + u * s₂.re := by
      apply add_le_of_le_of_le
      · exact mul_le_mul_of_nonneg_left (min_le_left _ _) (by linarith [hu_mem.1])
      · exact mul_le_mul_of_nonneg_left (min_le_right _ _) (hu_mem.1)
    linarith

  -- Apply the bound at point t
  rw [ht_eq, evolution_eigenvalues, evolution_eigenvalues]
  have := h_bound t ht_re
  -- The mean value theorem gives the desired bound
  exact le_trans (norm_sub_le _ _) (by
    rw [← mul_le_mul_right (norm_pos_iff.mpr (sub_ne_zero_of_ne (ne_of_apply_ne Complex.re (by linarith [hs₁, hs₂] : s₁.re ≠ s₂.re))))]
    convert this using 1
    ring)

end AcademicRH.DiagonalOperator
