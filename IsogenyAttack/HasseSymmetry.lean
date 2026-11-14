import IsogenyAttack.HassePolynomial
import Mathlib.Algebra.BigOperators.Intervals

/-! The two generating symmetries of the Legendre parameter act on the exact
Hasse polynomial. Reflection is proved by its differential equation and
coefficient uniqueness; inversion follows from the binomial symmetry. -/

namespace IsogenyAttack.Legendre
open Polynomial Finset
open scoped BigOperators
variable {K : Type*} [Field K]

/-- The hypergeometric differential operator. -/
noncomputable def hasseODE (n : ℕ) (f : K[X]) : K[X] :=
  X*(1-X)*derivative (derivative f) +
  (1+C (2*(n : K)-1)*X)*derivative f-C ((n : K)^2)*f

lemma recurrence_of_hasseODE {n : ℕ} {f : K[X]} (hode : hasseODE n f = 0) (k : ℕ) :
    (k+1 : K)^2 * f.coeff (k+1) = ((n : K)-k)^2 * f.coeff k := by
  have htheta : theta (theta f) - X * (theta (theta f) -
      C (2*(n : K))*theta f+C ((n : K)^2)*f) = 0 := by
    simp only [hasseODE, theta, derivative_mul, derivative_X, one_mul,
      map_sub, map_mul, map_ofNat, map_one] at hode ⊢
    linear_combination X*hode
  have h := congrArg (fun q : K[X] => q.coeff (k+1)) htheta
  simp only [coeff_sub, theta_coeff, coeff_X_mul, coeff_add, coeff_C_mul,
    coeff_zero] at h
  push_cast at h ⊢
  linear_combination h

lemma recurrence_scalar_hasse (n : ℕ) (a : K) (k : ℕ) :
    (k+1 : K)^2 * (C a*hassePolynomial n).coeff (k+1) =
      ((n : K)-k)^2 * (C a*hassePolynomial n).coeff k := by
  simp only [coeff_C_mul, hassePolynomial_coeff]
  linear_combination a*hasse_coefficient_recurrence (K := K) n k

/-- A low-degree solution is determined by its constant coefficient. -/
lemma hasse_recurrence_unique (p : ℕ) [CharP K p] {n : ℕ} (hnp : n < p)
    {f g : K[X]} (hf : f.natDegree ≤ n) (hg : g.natDegree ≤ n)
    (hrecf : ∀ k : ℕ, (k+1 : K)^2*f.coeff (k+1) = ((n : K)-k)^2*f.coeff k)
    (hrecg : ∀ k : ℕ, (k+1 : K)^2*g.coeff (k+1) = ((n : K)-k)^2*g.coeff k)
    (hzero : f.coeff 0 = g.coeff 0) : f=g := by
  ext k
  induction k with
  | zero => exact hzero
  | succ k ih =>
    by_cases hk : k+1 ≤ n
    · have hk0 : (k+1 : K) ≠ 0 := by
        simpa only [Nat.cast_add, Nat.cast_one] using
          small_natCast_ne_zero (K := K) p (by omega : 0 < k+1) (lt_of_le_of_lt hk hnp)
      apply mul_left_cancel₀ (pow_ne_zero 2 hk0)
      rw [hrecf, hrecg, ih]
    · rw [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hf (by omega)),
        coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hg (by omega))]

lemma reflected_hasseODE (p : ℕ) [CharP K p] {n : ℕ} (hp : p=2*n+1) :
    hasseODE n ((hassePolynomial (K := K) n).comp (1-X)) = 0 := by
  have hn : 2*(n : K) = -1 := by
    have h := CharP.cast_eq_zero K p
    rw [hp] at h
    push_cast at h
    linear_combination h
  have h := congrArg (fun q : K[X] => q.comp (1-X)) (hasse_differential_equation (K := K) n)
  simp only [add_comp, sub_comp, mul_comp, C_comp, X_comp, one_comp, zero_comp] at h
  unfold hasseODE
  rw [derivative_comp_one_sub_X, derivative_neg, derivative_comp_one_sub_X, neg_neg]
  simp only [hn] at h ⊢
  simp only [map_sub, map_neg, map_one] at h ⊢
  linear_combination h

/-- Exact reflection identity for the supersingular Hasse index. -/
theorem hassePolynomial_reflection (p : ℕ) [CharP K p] [Fact p.Prime]
    {n : ℕ} (hp : p=2*n+1) :
    (hassePolynomial (K := K) n).comp (1-X) = C ((-1 : K)^n)*hassePolynomial n := by
  apply hasse_recurrence_unique p (show n<p by omega)
  · calc
      _ ≤ (hassePolynomial (K := K) n).natDegree*(1-X : K[X]).natDegree := natDegree_comp_le
      _ ≤ n*1 := by
        rw [hassePolynomial_natDegree]
        apply Nat.mul_le_mul_left
        compute_degree!
      _ = n := Nat.mul_one n
  · exact (natDegree_mul_le).trans (by simp)
  · exact recurrence_of_hasseODE (reflected_hasseODE (K := K) p hp)
  · exact recurrence_scalar_hasse n ((-1 : K)^n)
  · rw [coeff_zero_eq_eval_zero, eval_comp]
    simp only [eval_sub, eval_one, eval_X, sub_zero, coeff_C_mul, hassePolynomial_coeff,
      Nat.choose_zero_right, Nat.cast_one, one_pow, mul_one]
    exact hassePolynomial_eval_one_sign p hp

/-- Evaluated reflection, including the exact nonzero sign. -/
theorem hassePolynomial_eval_reflection (p : ℕ) [CharP K p] [Fact p.Prime]
    {n : ℕ} (hp : p=2*n+1) (t : K) :
    (hassePolynomial (K := K) n).eval (1-t) =
      (-1 : K)^n*(hassePolynomial n).eval t := by
  have h := congrArg (fun q : K[X] => q.eval t) (hassePolynomial_reflection (K := K) p hp)
  simpa only [eval_comp, eval_sub, eval_one, eval_X, eval_mul, eval_C] using h

/-- The Hasse polynomial is reciprocal, in every characteristic. -/
theorem hassePolynomial_eval_inverse (n : ℕ) {t : K} (ht : t ≠ 0) :
    t^n*(hassePolynomial (K := K) n).eval t⁻¹ = (hassePolynomial n).eval t := by
  simp only [hassePolynomial, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
  rw [mul_sum]
  calc
    _ = ∑ i ∈ range (n+1), (n.choose (n-i) : K)^2*t^(n-i) := by
      apply sum_congr rfl
      intro i hi
      have hin : i ≤ n := by simpa using hi
      rw [Nat.choose_symm hin]
      have hpow : t^n*(t⁻¹)^i = t^(n-i) := by
        calc
          _ = (t^(n-i)*t^i)*(t⁻¹)^i := by rw [← pow_add, Nat.sub_add_cancel hin]
          _ = _ := by rw [inv_pow]; field_simp
      linear_combination (n.choose i : K)^2*hpow
    _ = _ := by
      simpa only [Nat.add_sub_cancel] using
        sum_range_reflect (fun i => (n.choose i : K)^2*t^i) (n+1)

/-- Reflection sends Hasse roots to Hasse roots. -/
theorem hasse_root_reflection (p : ℕ) [CharP K p] [Fact p.Prime]
    {n : ℕ} (hp : p=2*n+1) {t : K} (ht : (hassePolynomial (K := K) n).IsRoot t) :
    (hassePolynomial (K := K) n).IsRoot (1-t) := by
  change _ = 0
  rw [hassePolynomial_eval_reflection p hp, ht, mul_zero]

/-- Inversion sends every nonzero Hasse root to a Hasse root. -/
theorem hasse_root_inverse (n : ℕ) {t : K} (ht0 : t ≠ 0)
    (ht : (hassePolynomial (K := K) n).IsRoot t) :
    (hassePolynomial (K := K) n).IsRoot t⁻¹ := by
  have h := hassePolynomial_eval_inverse n ht0
  rw [ht] at h
  exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero _ ht0)

/-- All five other expressions in the anharmonic orbit of a Hasse root
are again Hasse roots; the sixth expression is the input root itself. -/
theorem hasse_root_anharmonic_orbit (p : ℕ) [CharP K p] [Fact p.Prime]
    {n : ℕ} (hp : p=2*n+1) {t : K} (ht : (hassePolynomial (K := K) n).IsRoot t) :
    (hassePolynomial n).IsRoot (1-t) ∧
    (hassePolynomial n).IsRoot t⁻¹ ∧
    (hassePolynomial n).IsRoot (1-t)⁻¹ ∧
    (hassePolynomial n).IsRoot (t/(t-1)) ∧
    (hassePolynomial n).IsRoot ((t-1)/t) := by
  have ht0 : t ≠ 0 := by intro h; simp [h, IsRoot] at ht
  have ht1 : t ≠ 1 := by
    intro h
    have hz : (hassePolynomial (K := K) n).eval 1 = 0 := by simpa [h, IsRoot] using ht
    rw [hassePolynomial_eval_one_sign p hp] at hz
    exact pow_ne_zero n (neg_ne_zero.mpr one_ne_zero) hz
  have hmt : 1-t ≠ 0 := sub_ne_zero.mpr (Ne.symm ht1)
  have htm : t-1 ≠ 0 := sub_ne_zero.mpr ht1
  have hreflection := hasse_root_reflection p hp ht
  have hinverse := hasse_root_inverse n ht0 ht
  have hinvreflection := hasse_root_inverse n hmt hreflection
  have hreflectioninverse := hasse_root_reflection p hp hinverse
  have hfrac : 1-t⁻¹ = (t-1)/t := by field_simp
  have hfrac0 : 1-t⁻¹ ≠ 0 := by rw [hfrac]; exact div_ne_zero htm ht0
  have hinvreflectioninverse := hasse_root_inverse n hfrac0 hreflectioninverse
  rw [hfrac] at hreflectioninverse hinvreflectioninverse
  rw [inv_div] at hinvreflectioninverse
  exact ⟨hreflection, hinverse, hinvreflection, hinvreflectioninverse, hreflectioninverse⟩

/-- The same closure statement in expressions directly generated by reflection
and inversion, matching the six-factor Legendre-fiber classification. -/
theorem hasse_root_six (p : ℕ) [CharP K p] [Fact p.Prime]
    {n : ℕ} (hp : p=2*n+1) {t : K} (ht : (hassePolynomial (K := K) n).IsRoot t) :
    (hassePolynomial n).IsRoot t ∧
    (hassePolynomial n).IsRoot (1-t) ∧
    (hassePolynomial n).IsRoot t⁻¹ ∧
    (hassePolynomial n).IsRoot (1-t)⁻¹ ∧
    (hassePolynomial n).IsRoot (1-t⁻¹) ∧
    (hassePolynomial n).IsRoot (1-t⁻¹)⁻¹ := by
  obtain ⟨ha,hb,hc,hd,he⟩ := hasse_root_anharmonic_orbit p hp ht
  have ht0 : t ≠ 0 := by intro h; simp [h, IsRoot] at ht
  have hfrac : 1-t⁻¹ = (t-1)/t := by field_simp
  refine ⟨ht,ha,hb,hc,?_,?_⟩
  · rw [hfrac]; exact he
  · rw [hfrac,inv_div]; exact hd

end IsogenyAttack.Legendre
