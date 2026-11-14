import IsogenyAttack.HassePolynomial
import Mathlib.Algebra.Polynomial.Expand

/-!
The Hasse coefficient over a finite extension is the iterated Frobenius
product of the coefficient over the prime characteristic. The calculation
uses only the cubic degree bound and polynomial Frobenius, with no assumed
supersingularity criterion.
-/

namespace IsogenyAttack.Legendre
open Polynomial Finset

variable {K : Type*} [Field K]

/-- Only one term of this product can contribute to the indicated
coefficient: the exponents in a p-th power are divisible by p. -/
theorem coeff_mul_pow_char (p : ℕ) [Fact p.Prime] [CharP K p]
    (A B : K[X]) (hA : A.natDegree < 2*p-1) (k : ℕ) :
    (A * B^p).coeff (p*k+(p-1)) = A.coeff (p-1) * (B.coeff k)^p := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hpminus : p-1+1=p := by omega
  rw [← map_frobenius_expand p B, coeff_mul]
  rw [Finset.sum_eq_single (p-1, p*k)]
  · rw [coeff_map, coeff_expand_mul' hp, frobenius_def]
  · rintro ⟨i,j⟩ hij hne
    have hij' : i+j=p*k+(p-1) := Finset.mem_antidiagonal.mp hij
    by_cases hdi : A.natDegree < i
    · rw [coeff_eq_zero_of_natDegree_lt hdi, zero_mul]
    · have hi : i < 2*p-1 := lt_of_le_of_lt (le_of_not_gt hdi) hA
      rw [coeff_map, coeff_expand hp]
      by_cases hj : p ∣ j
      · have hd : p ∣ i+1 := by
          have htotal : i+1+j=p*(k+1) := by nlinarith
          have hsum : p ∣ i+1+j := htotal ▸ dvd_mul_right p (k+1)
          exact (Nat.dvd_add_iff_left hj).mpr hsum
        obtain ⟨d, hd⟩ := hd
        have hd1 : d = 1 := by
          by_cases hd0 : d = 0
          · simp [hd0] at hd
          have hdpos : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr hd0
          by_contra hdne
          have hd2 : 2 ≤ d := by omega
          have hi2 : i+1 < 2*p := by omega
          nlinarith
        have hi' : i=p-1 := by rw [hd1] at hd; omega
        have hj' : j=p*k := by omega
        exact (hne (Prod.ext hi' hj')).elim
      · simp [hj]
  · intro hnot
    exact (hnot (Finset.mem_antidiagonal.mpr (by omega))).elim

/-- The exponent `(p^r-1)/2`, expressed recursively to expose Frobenius. -/
def halfExtensionExponent (n p : ℕ) : ℕ → ℕ
  | 0 => 0
  | r+1 => n + p * halfExtensionExponent n p r

theorem twice_halfExtensionExponent (n p r : ℕ) (hp : p=2*n+1) :
    2 * halfExtensionExponent n p r + 1 = p^r := by
  induction r with
  | zero => simp [halfExtensionExponent]
  | succ r ih =>
      rw [halfExtensionExponent, pow_succ]
      nlinarith

theorem halfExtensionExponent_eq (n p r : ℕ) (hp : p=2*n+1) :
    halfExtensionExponent n p r = (p^r-1)/2 := by
  have := twice_halfExtensionExponent n p r hp
  omega

/-- The extension-field Hasse coefficient satisfies the exact Frobenius
recurrence, for every polynomial of degree at most three. -/
theorem hasseCoefficient_iteration_step (p n r : ℕ) [Fact p.Prime] [CharP K p]
    (hp : p=2*n+1) (f : K[X]) (hf : f.natDegree ≤ 3) :
    (f ^ halfExtensionExponent n p (r+1)).coeff (p^(r+1)-1) =
      (f^n).coeff (p-1) *
        ((f ^ halfExtensionExponent n p r).coeff (p^r-1))^p := by
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  have hpr : 0 < p^r := pow_pos hp0 r
  have hpminus : p-1+1=p := by omega
  have hprod : 0 < p^r*p := Nat.mul_pos hpr hp0
  have hprodminus : p^r*p-1+1=p^r*p := by omega
  have hindex : p^(r+1)-1=p*(p^r-1)+(p-1) := by
    rw [pow_succ]
    have : p^r = p^r-1+1 := by omega
    nlinarith
  rw [halfExtensionExponent, pow_add, mul_comm p, pow_mul, hindex]
  apply coeff_mul_pow_char
  have hdeg : (f^n).natDegree ≤ 3*n := by
    exact (natDegree_pow_le).trans (by simpa [mul_comm] using Nat.mul_le_mul_right n hf)
  omega

/-- Vanishing of the coefficient over any nontrivial finite extension is
equivalent to vanishing of the original Hasse coefficient. -/
theorem hasseCoefficient_iteration_zero_iff (p n r : ℕ) [Fact p.Prime] [CharP K p]
    (hp : p=2*n+1) (hr : 0 < r) (f : K[X]) (hf : f.natDegree ≤ 3) :
    (f ^ halfExtensionExponent n p r).coeff (p^r-1) = 0 ↔
      (f^n).coeff (p-1) = 0 := by
  induction r with
  | zero => omega
  | succ r ih =>
      rw [hasseCoefficient_iteration_step p n r hp f hf,
        mul_eq_zero, pow_eq_zero_iff (Fact.out : p.Prime).ne_zero]
      by_cases hr0 : r=0
      · subst r
        simp [halfExtensionExponent]
      · rw [ih (Nat.pos_of_ne_zero hr0)]
        simp

/-- The same criterion with the usual exponents `(q-1)/2` and `(p-1)/2`. -/
theorem hasseCoefficient_primePower_zero_iff (p r : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 2 < p) (hr : 0 < r) (f : K[X]) (hf : f.natDegree ≤ 3) :
    (f ^ ((p^r-1)/2)).coeff (p^r-1) = 0 ↔
      (f^((p-1)/2)).coeff (p-1) = 0 := by
  obtain ⟨n, hn⟩ := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  have hpn : p=2*((p-1)/2)+1 := by omega
  rw [← halfExtensionExponent_eq ((p-1)/2) p r hpn]
  exact hasseCoefficient_iteration_zero_iff p ((p-1)/2) r hpn hr f hf

/-- The exact coefficient is a Frobenius product; its exponent is the
geometric sum `1+p+⋯+p^(r-1)`. -/
theorem hasseCoefficient_iteration (p n r : ℕ) [Fact p.Prime] [CharP K p]
    (hp : p=2*n+1) (f : K[X]) (hf : f.natDegree ≤ 3) :
    (f ^ halfExtensionExponent n p r).coeff (p^r-1) =
      ((f^n).coeff (p-1))^(∑ i ∈ Finset.range r, p^i) := by
  induction r with
  | zero => simp [halfExtensionExponent]
  | succ r ih =>
      rw [hasseCoefficient_iteration_step p n r hp f hf, ih, ← pow_mul,
        ← pow_succ']
      congr 1
      rw [Finset.sum_range_succ']
      simp only [pow_succ, pow_zero, Finset.sum_mul]

end IsogenyAttack.Legendre
