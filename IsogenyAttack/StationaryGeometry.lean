import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic

/-!
Algebraic ingredients for a geometric stationary-mass proof. These are genuine
facts about the Legendre j-invariant and Hasse polynomials, not assumptions about
the attack's acceptance probability. The supersingular/Hasse correspondence and
the stationary-walk identification are not asserted in this file.
-/

namespace IsogenyAttack
namespace Legendre

open Polynomial Finset
open scoped BigOperators

variable {K : Type*} [Field K]

/-- The j-invariant formula of the Legendre curve y²=x(x-1)(x-λ). -/
def jInvariant (t : K) : K := 256 * (t ^ 2 - t + 1) ^ 3 / (t ^ 2 * (t - 1) ^ 2)

/-- Clearing the denominator in j(t)=j gives a polynomial of degree six. -/
noncomputable def fiberPolynomial (j : K) : K[X] :=
  C 256 * (X ^ 2 - X + 1) ^ 3 - C j * X ^ 2 * (X - 1) ^ 2

lemma fiberPolynomial_expand (j : K) : fiberPolynomial j =
    C 256 * X ^ 6 - C 768 * X ^ 5 + C (1536-j) * X ^ 4 +
    C (2*j-1792) * X ^ 3 + C (1536-j) * X ^ 2 - C 768 * X + C 256 := by
  unfold fiberPolynomial
  simp only [map_sub, map_mul, map_ofNat]
  ring

lemma fiberPolynomial_coeff_six (j : K) : (fiberPolynomial j).coeff 6 = 256 := by
  rw [fiberPolynomial_expand]
  simp only [coeff_sub, coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C]
  norm_num

lemma fiberPolynomial_natDegree_le (j : K) : (fiberPolynomial j).natDegree ≤ 6 := by
  rw [fiberPolynomial_expand]
  compute_degree!

lemma fiberPolynomial_ne_zero (j : K) (h256 : (256 : K) ≠ 0) : fiberPolynomial j ≠ 0 := by
  intro h
  have hc := congrArg (fun q : K[X] => q.coeff 6) h
  simp [fiberPolynomial_coeff_six, h256] at hc

lemma fiberPolynomial_natDegree (j : K) (h256 : (256 : K) ≠ 0) :
    (fiberPolynomial j).natDegree = 6 := by
  exact natDegree_eq_of_le_of_coeff_ne_zero (fiberPolynomial_natDegree_le j)
    (by simpa only [fiberPolynomial_coeff_six] using h256)

lemma fiberPolynomial_root {t j : K} (ht : t ≠ 0) (ht1 : t ≠ 1)
    (hj : jInvariant t = j) : (fiberPolynomial j).IsRoot t := by
  have hden : t ^ 2 * (t - 1) ^ 2 ≠ 0 := mul_ne_zero (pow_ne_zero _ ht)
    (pow_ne_zero _ (sub_ne_zero.mpr ht1))
  have heq := (div_eq_iff hden).mp hj
  simp only [IsRoot, fiberPolynomial, eval_sub, eval_mul, eval_C, eval_pow, eval_X,
    eval_add, eval_one]
  rw [heq]
  ring

/-- A fiber of the Legendre j-invariant has at most six nonsingular parameters.
This is the geometric multiplicity factor needed when pushing forward a uniform
law on the roots of the Hasse polynomial. -/
theorem j_fiber_card_le_six (j : K) (h256 : (256 : K) ≠ 0) (T : Finset K)
    (hT : ∀ t ∈ T, t ≠ 0 ∧ t ≠ 1 ∧ jInvariant t = j) : T.card ≤ 6 := by
  classical
  have hp := fiberPolynomial_ne_zero j h256
  have hsub : T ⊆ (fiberPolynomial j).roots.toFinset := by
    intro t ht
    rcases hT t ht with ⟨ht0, ht1, hj⟩
    simpa only [Multiset.mem_toFinset, mem_roots hp] using fiberPolynomial_root ht0 ht1 hj
  calc
    T.card ≤ (fiberPolynomial j).roots.toFinset.card := card_le_card hsub
    _ ≤ (fiberPolynomial j).roots.card := Multiset.toFinset_card_le _
    _ ≤ (fiberPolynomial j).natDegree := Polynomial.card_roots' _
    _ ≤ 6 := fiberPolynomial_natDegree_le j

/-- The degree-n Hasse polynomial; for characteristic p>2 use n=(p-1)/2. -/
noncomputable def hassePolynomial (n : ℕ) : K[X] :=
  ∑ i ∈ range (n + 1), C ((n.choose i : K) ^ 2) * X ^ i

@[simp] theorem hassePolynomial_coeff (n k : ℕ) :
    (hassePolynomial (K := K) n).coeff k = (n.choose k : K) ^ 2 := by
  rw [hassePolynomial, finsetSum_coeff]
  simp_rw [coeff_C_mul_X_pow]
  simp +contextual [Nat.choose_eq_zero_of_lt]

@[simp] theorem hassePolynomial_eval_zero (n : ℕ) :
    (hassePolynomial (K := K) n).eval 0 = 1 := by
  rw [← coeff_zero_eq_eval_zero, hassePolynomial_coeff]
  simp

@[simp] theorem hassePolynomial_natDegree (n : ℕ) :
    (hassePolynomial (K := K) n).natDegree = n := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · apply natDegree_le_iff_coeff_eq_zero.mpr
    intro k hk
    simp [Nat.choose_eq_zero_of_lt hk]
  · simp

@[simp] theorem hassePolynomial_monic (n : ℕ) :
    (hassePolynomial (K := K) n).Monic := by
  simp [Monic, leadingCoeff, hassePolynomial_natDegree]

end Legendre
end IsogenyAttack
