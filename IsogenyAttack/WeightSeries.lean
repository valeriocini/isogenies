import IsogenyAttack.Weights
import IsogenyAttack.Euler

open scoped BigOperators
open Finset

namespace IsogenyAttack

/-- The normalized convolution factor whose Euler product controls the degree law. -/
noncomputable def normalizedConvolutionWeight (n : ℕ) : ℝ :=
  (convolutionWeight n : ℝ) / (n : ℝ) ^ 2

lemma normalizedConvolutionWeight_nonneg (n : ℕ) :
    0 ≤ normalizedConvolutionWeight n := by unfold normalizedConvolutionWeight; positivity

@[simp] lemma normalizedConvolutionWeight_one : normalizedConvolutionWeight 1 = 1 := by
  simp [normalizedConvolutionWeight]

lemma normalizedConvolutionWeight_mul {a b : ℕ} (hab : a.Coprime b) :
    normalizedConvolutionWeight (a * b) =
      normalizedConvolutionWeight a * normalizedConvolutionWeight b := by
  simp only [normalizedConvolutionWeight, convolutionWeight_mul hab, Nat.cast_mul,
    mul_pow, mul_div_mul_comm]

lemma normalizedConvolutionWeight_prime_pow {p : ℕ} (hp : p.Prime) (a : ℕ) :
    normalizedConvolutionWeight (p ^ a) = primePowerTerm p a := by
  by_cases ha : a = 0
  · subst a; simp [primePowerTerm]
  simp only [normalizedConvolutionWeight, convolutionWeight_prime_pow hp,
    Nat.cast_pow, Nat.cast_add, Nat.cast_one, primePowerTerm, if_neg ha]
  rw [← pow_mul, Nat.mul_comm a 2]

/-- A finite product over all prime divisors of numbers at most B controls the partial sum. -/
theorem normalizedConvolutionWeight_sum_le_four (B : ℕ) :
    (∑ n ∈ Ioc 0 B, normalizedConvolutionWeight n) ≤ 4 := by
  let P := Icc 2 B
  have hlocal {p : ℕ} (hp : p.Prime) :
      HasSum (fun a : ℕ => normalizedConvolutionWeight (p ^ a)) (eulerFactor p) := by
    simpa only [normalizedConvolutionWeight_prime_pow hp] using hasSum_primePowerTerm hp.two_le
  have hnorm {p : ℕ} (hp : p.Prime) :
      Summable (fun a : ℕ => ‖normalizedConvolutionWeight (p ^ a)‖) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (normalizedConvolutionWeight_nonneg _)] using
      (hlocal hp).summable
  have hEuler := EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum
    normalizedConvolutionWeight_one (fun {_ _} h => normalizedConvolutionWeight_mul h)
    (fun {_} hp => hnorm hp) P
  have hnmem {n : ℕ} (hn : n ∈ Ioc 0 B) : n ∈ Nat.factoredNumbers P := by
    apply Nat.mem_factoredNumbers_of_primeFactors_subset (by have := mem_Ioc.mp hn; omega)
    intro p hp
    exact mem_Icc.mpr ⟨(Nat.prime_of_mem_primeFactors hp).two_le,
      (Nat.le_of_dvd (mem_Ioc.mp hn).1 (Nat.dvd_of_mem_primeFactors hp)).trans (mem_Ioc.mp hn).2⟩
  let e : {n // n ∈ Ioc 0 B} ↪ Nat.factoredNumbers P :=
    ⟨fun n => ⟨n.1, hnmem n.2⟩, by
      intro a b h
      apply Subtype.ext
      exact congrArg (fun z : Nat.factoredNumbers P => (z : ℕ)) h⟩
  have hsum := sum_le_hasSum ((Ioc 0 B).attach.map e)
    (fun n _ => normalizedConvolutionWeight_nonneg n.1) hEuler.2
  have hbound : (∑ n ∈ Ioc 0 B, normalizedConvolutionWeight n) ≤
      ∏ p ∈ P with p.Prime, eulerFactor p := by
    have heq : (∏ p ∈ P with p.Prime, ∑' a : ℕ, normalizedConvolutionWeight (p ^ a)) =
        ∏ p ∈ P with p.Prime, eulerFactor p := by
      apply prod_congr rfl
      intro p hp
      exact (hlocal (mem_filter.mp hp).2).tsum_eq
    rw [heq] at hsum
    rw [sum_map] at hsum
    change (∑ n ∈ (Ioc 0 B).attach, normalizedConvolutionWeight n.val) ≤
      ∏ p ∈ P with p.Prime, eulerFactor p at hsum
    simpa only [sum_attach] using hsum
  exact hbound.trans (eulerProduct_primes_le_four _ (fun p hp => (mem_filter.mp hp).2))

end IsogenyAttack
