import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.Tactic

open scoped BigOperators
open Finset

namespace IsogenyAttack

/-- The degree weight printed in Algorithm 5; zero is outside the sampling range. -/
def printedWeight (n : ℕ) : ℕ :=
  if n = 0 then 0 else ∏ p ∈ n.primeFactors, (p + 1) ^ n.factorization p

/-- The number of index-n sublattices of a rank-two lattice. -/
abbrev sigmaOne (n : ℕ) : ℕ := ArithmeticFunction.sigma 1 n

lemma geometric_sum_le_add_one_pow (p a : ℕ) :
    (∑ i ∈ range (a + 1), p ^ i) ≤ (p + 1) ^ a := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [sum_range_succ, pow_succ]
    have hp : p ^ (a + 1) ≤ p * (p + 1) ^ a := by
      rw [pow_succ, mul_comm]
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) a)
    simp only [pow_succ] at hp ⊢
    nlinarith

/-- The printed weight dominates the number of kernels, a stronger bound than W ≥ psi. -/
theorem sigmaOne_le_printedWeight (n : ℕ) : sigmaOne n ≤ printedWeight n := by
  by_cases hn : n = 0
  · subst n; simp [sigmaOne, printedWeight]
  unfold sigmaOne
  rw [printedWeight, if_neg hn,
    ArithmeticFunction.sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul hn]
  apply prod_le_prod' 
  intro p hp
  simpa using geometric_sum_le_add_one_pow p (n.factorization p)

@[simp] theorem printedWeight_zero : printedWeight 0 = 0 := by simp [printedWeight]
@[simp] theorem printedWeight_one : printedWeight 1 = 1 := by simp [printedWeight]

theorem printedWeight_pos {n : ℕ} (hn : 0 < n) : 0 < printedWeight n :=
  lt_of_lt_of_le (ArithmeticFunction.sigma_pos 1 n (by omega)) (sigmaOne_le_printedWeight n)

/-- The convolution factor W = id * g. -/
def convolutionWeight (n : ℕ) : ℕ :=
  if n = 0 then 0 else ∏ p ∈ n.primeFactors, (p + 1) ^ (n.factorization p - 1)

@[simp] theorem convolutionWeight_zero : convolutionWeight 0 = 0 := by simp [convolutionWeight]
@[simp] theorem convolutionWeight_one : convolutionWeight 1 = 1 := by simp [convolutionWeight]

lemma factorization_prod_coprime (F : ℕ → ℕ → ℕ) {a b : ℕ} (hab : a.Coprime b) :
    (a * b).factorization.prod F = a.factorization.prod F * b.factorization.prod F := by
  rw [Nat.factorization_mul_of_coprime hab,
    Finsupp.prod_add_index_of_disjoint hab.disjoint_primeFactors]

lemma convolutionWeight_mul {a b : ℕ} (hab : a.Coprime b) :
    convolutionWeight (a * b) = convolutionWeight a * convolutionWeight b := by
  by_cases ha : a = 0
  · subst a; simp
  by_cases hb : b = 0
  · subst b; simp
  simp only [convolutionWeight, if_neg ha, if_neg hb, if_neg (mul_ne_zero ha hb)]
  simpa only [Finsupp.prod, Nat.support_factorization] using
    factorization_prod_coprime (fun p k => (p + 1) ^ (k - 1)) hab

lemma printedWeight_mul {a b : ℕ} (hab : a.Coprime b) :
    printedWeight (a * b) = printedWeight a * printedWeight b := by
  by_cases ha : a = 0
  · subst a; simp
  by_cases hb : b = 0
  · subst b; simp
  simp only [printedWeight, if_neg ha, if_neg hb, if_neg (mul_ne_zero ha hb)]
  simpa only [Finsupp.prod, Nat.support_factorization] using
    factorization_prod_coprime (fun p k => (p + 1) ^ k) hab

lemma printedWeight_prime_pow {p : ℕ} (hp : p.Prime) (a : ℕ) :
    printedWeight (p ^ a) = (p + 1) ^ a := by
  cases a with
  | zero => simp
  | succ a =>
    simp [printedWeight, hp.ne_zero, Nat.primeFactors_pow, hp.factorization_self, hp.primeFactors]

lemma convolutionWeight_prime_pow {p : ℕ} (hp : p.Prime) (a : ℕ) :
    convolutionWeight (p ^ a) = (p + 1) ^ (a - 1) := by
  cases a with
  | zero => simp
  | succ a =>
    simp [convolutionWeight, hp.ne_zero, Nat.primeFactors_pow, hp.factorization_self, hp.primeFactors]

/-- Arithmetic-function packaging of the printed weight. -/
def printedWeightAF : ArithmeticFunction ℕ := ⟨printedWeight, printedWeight_zero⟩
/-- Arithmetic-function packaging of the convolution factor. -/
def convolutionWeightAF : ArithmeticFunction ℕ := ⟨convolutionWeight, convolutionWeight_zero⟩

lemma printedWeightAF_multiplicative : printedWeightAF.IsMultiplicative :=
  ⟨printedWeight_one, fun h => printedWeight_mul h⟩

lemma convolutionWeightAF_multiplicative : convolutionWeightAF.IsMultiplicative :=
  ⟨convolutionWeight_one, fun h => convolutionWeight_mul h⟩

lemma local_convolution_identity (p a : ℕ) :
    (∑ i ∈ range (a + 1), p ^ i * (p + 1) ^ (a - i - 1)) = (p + 1) ^ a := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [sum_range_succ']
    simp only [pow_zero, one_mul, Nat.sub_zero, Nat.add_sub_cancel]
    have h : (∑ k ∈ range (a + 1), p ^ (k + 1) * (p + 1) ^ (a + 1 - (k + 1) - 1)) =
        p * ∑ k ∈ range (a + 1), p ^ k * (p + 1) ^ (a - k - 1) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro k hk
      simp only [Nat.add_sub_add_right, pow_succ]
      ring
    rw [h, ih, pow_succ]
    ring

/-- Exact Dirichlet-convolution formula, with no asymptotic assumption. -/
theorem printedWeightAF_eq_convolution :
    printedWeightAF = ArithmeticFunction.id * convolutionWeightAF := by
  apply (ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers
    printedWeightAF printedWeightAF_multiplicative
    (ArithmeticFunction.id * convolutionWeightAF)
    (ArithmeticFunction.isMultiplicative_id.mul convolutionWeightAF_multiplicative)).2
  intro p a hp
  change printedWeight (p ^ a) = _
  rw [printedWeight_prime_pow hp, ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun x y => ArithmeticFunction.id x * convolutionWeightAF y),
    Nat.sum_divisors_prime_pow hp]
  symm
  calc
    _ = ∑ i ∈ range (a + 1), p ^ i * (p + 1) ^ (a - i - 1) := by
      apply sum_congr rfl
      intro i hi
      have hia : i ≤ a := by simpa only [mem_range, Nat.lt_succ_iff] using hi
      have hdiv : p ^ a / p ^ i = p ^ (a - i) := by
        nth_rw 1 [← Nat.sub_add_cancel hia]
        rw [pow_add, Nat.mul_div_cancel _ (pow_pos hp.pos _)]
      change p ^ i * convolutionWeight (p ^ a / p ^ i) = _
      rw [hdiv, convolutionWeight_prime_pow hp]
    _ = _ := local_convolution_identity p a

end IsogenyAttack
