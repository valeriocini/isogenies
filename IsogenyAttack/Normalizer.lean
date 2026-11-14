import IsogenyAttack.WeightSeries
import Mathlib.Data.Nat.Cast.Order.Field

open scoped BigOperators
open Finset
namespace IsogenyAttack

/-- The full printed normalizer, including the degree-B endpoint. -/
def normalizer (B : ℕ) : ℝ := ∑ n ∈ Ioc 0 B, (printedWeight n : ℝ)

lemma sum_initial_nat_le_square (N : ℕ) :
    (∑ m ∈ Ioc 0 N, (m : ℝ)) ≤ (N : ℝ) ^ 2 := by
  calc
    _ ≤ ∑ _m ∈ Ioc 0 N, (N : ℝ) := by
      apply sum_le_sum
      intro m hm
      exact_mod_cast (mem_Ioc.mp hm).2
    _ = (N : ℝ) ^ 2 := by simp [pow_two]

lemma normalizer_convolution (B : ℕ) :
    normalizer B = ∑ n ∈ Ioc 0 B,
      (convolutionWeight n : ℝ) * ∑ m ∈ Ioc 0 (B / n), (m : ℝ) := by
  have h := ArithmeticFunction.sum_Ioc_mul_eq_sum_sum
    convolutionWeightAF ArithmeticFunction.id B
  rw [mul_comm, ← printedWeightAF_eq_convolution] at h
  change (∑ n ∈ Ioc 0 B, printedWeight n) =
    ∑ n ∈ Ioc 0 B, convolutionWeight n * ∑ m ∈ Ioc 0 (B / n), m at h
  unfold normalizer
  have hR := congrArg (fun n : ℕ => (n : ℝ)) h
  push_cast at hR
  exact hR

/-- The finite convolution estimate, before bounding the Euler product. -/
theorem normalizer_le_weighted_sum (B : ℕ) :
    normalizer B ≤ (B : ℝ) ^ 2 *
      ∑ n ∈ Ioc 0 B, (convolutionWeight n : ℝ) / (n : ℝ) ^ 2 := by
  rw [normalizer_convolution, mul_sum]
  apply sum_le_sum
  intro n hn
  have hnonneg : 0 ≤ (convolutionWeight n : ℝ) := Nat.cast_nonneg _
  have hdiv : ((B / n : ℕ) : ℝ) ≤ (B : ℝ) / n := Nat.cast_div_le
  calc
    _ ≤ (convolutionWeight n : ℝ) * ((B / n : ℕ) : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_left (sum_initial_nat_le_square _) hnonneg
    _ ≤ (convolutionWeight n : ℝ) * ((B : ℝ) / n) ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) hdiv 2) hnonneg
    _ = _ := by ring

lemma normalizer_pos {B : ℕ} (hB : 1 ≤ B) : 0 < normalizer B := by
  unfold normalizer
  apply sum_pos'
  · intro n hn
    positivity
  · exact ⟨1, mem_Ioc.mpr ⟨by omega, hB⟩, by simp⟩

/-- Absolute, uniform normalization bound for the actual printed degree weight. -/
theorem normalizer_le_four_mul_square (B : ℕ) :
    normalizer B ≤ 4 * (B : ℝ) ^ 2 := by
  have h := normalizedConvolutionWeight_sum_le_four B
  have hc := mul_le_mul_of_nonneg_left h (sq_nonneg (B : ℝ))
  calc
    normalizer B ≤ (B : ℝ) ^ 2 *
        ∑ n ∈ Ioc 0 B, (convolutionWeight n : ℝ) / (n : ℝ) ^ 2 :=
      normalizer_le_weighted_sum B
    _ ≤ (B : ℝ) ^ 2 * 4 := hc
    _ = _ := by ring

end IsogenyAttack
