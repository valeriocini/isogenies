import IsogenyAttack.StationaryGeometry
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.Separable
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Factorial.NatCast

set_option maxHeartbeats 800000

namespace IsogenyAttack.Legendre
open Polynomial Finset
open scoped BigOperators

variable {K : Type*} [Field K]

@[simp] theorem hassePolynomial_eval_one (n : ℕ) :
    (hassePolynomial (K := K) n).eval 1 = ((2*n).choose n : K) := by
  simp only [hassePolynomial, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X,
    one_pow, mul_one]
  have h := congrArg (fun a : ℕ => (a : K)) (Nat.sum_range_choose_sq n)
  push_cast at h
  exact h

/-- The coefficient recurrence underlying the hypergeometric equation. -/
theorem hasse_coefficient_recurrence (n k : ℕ) :
    (k+1 : K)^2 * (n.choose (k+1) : K)^2 =
      ((n : K) - k)^2 * (n.choose k : K)^2 := by
  by_cases hk : k ≤ n
  · have h := congrArg (fun x : ℕ => (x : K)) (Nat.choose_succ_right_eq n k)
    push_cast at h
    rw [Nat.cast_sub hk] at h
    linear_combination h * ((n.choose (k+1) : K) * (k+1) + (n.choose k : K) * ((n : K)-k))
  · have hn : n < k := by omega
    simp [Nat.choose_eq_zero_of_lt hn, Nat.choose_eq_zero_of_lt (by omega : n < k+1)]

/-- Euler differentiation, whose k-th coefficient is k times the original one. -/
noncomputable def theta (f : K[X]) : K[X] := X * derivative f

@[simp] theorem theta_coeff (f : K[X]) (k : ℕ) :
    (theta f).coeff k = (k : K) * f.coeff k := by
  cases k with
  | zero => simp [theta]
  | succ k => simp [theta, coeff_derivative, mul_comm]

/-- A denominator-free exact differential equation, valid over every field. -/
theorem hasse_theta_equation (n : ℕ) :
    theta (theta (hassePolynomial (K := K) n)) =
      X * (theta (theta (hassePolynomial n)) -
        C (2*(n : K)) * theta (hassePolynomial n) + C ((n : K)^2) * hassePolynomial n) := by
  ext k
  cases k with
  | zero => simp
  | succ k =>
    simp only [theta_coeff, coeff_X_mul, coeff_add, coeff_sub, coeff_C_mul,
      hassePolynomial_coeff]
    have h := hasse_coefficient_recurrence (K := K) n k
    push_cast
    linear_combination h

/-- The usual hypergeometric differential equation for H_n. -/
theorem hasse_differential_equation (n : ℕ) :
    X * (1-X) * derivative (derivative (hassePolynomial (K := K) n)) +
      (1+C (2*(n : K)-1)*X) * derivative (hassePolynomial n) -
      C ((n : K)^2) * hassePolynomial n = 0 := by
  have h := hasse_theta_equation (K := K) n
  simp only [theta, derivative_mul, derivative_X, one_mul, map_mul, map_ofNat] at h
  have heq : X * (X * (1-X) * derivative (derivative (hassePolynomial (K := K) n)) +
      (1+C (2*(n : K)-1)*X) * derivative (hassePolynomial n) -
      C ((n : K)^2) * hassePolynomial n) = 0 := by
    simp only [map_sub, map_one, map_mul, map_ofNat]
    linear_combination h
  exact (mul_eq_zero.mp heq).resolve_left X_ne_zero

@[simp] theorem hassePolynomial_map {L : Type*} [Field L] (f : K →+* L) (n : ℕ) :
    (hassePolynomial (K := K) n).map f = hassePolynomial (K := L) n := by
  ext k
  simp

/-- The Hasse polynomial is exactly the middle coefficient of the
Legendre cubic raised to the (p-1)/2 power, up to a nonzero sign. This is the
algebraic coefficient used in the Hasse-invariant supersingularity criterion. -/
theorem legendre_middle_coefficient (n : ℕ) (t : K) :
    ((X * (X-1) * (X-C t) : K[X])^n).coeff (2*n) =
      (-1 : K)^n * (hassePolynomial (K := K) n).eval t := by
  have hpoly : (X * (X-1) * (X-C t) : K[X])^n =
      X^n * ((X+C (-1))^n * (X+C (-t))^n) := by
    simp only [mul_pow, map_neg, map_one, sub_eq_add_neg]
    ring
  rw [hpoly, two_mul, coeff_X_pow_mul, coeff_mul,
    Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [coeff_X_add_C_pow, hassePolynomial, eval_finsetSum, eval_mul,
    eval_C, eval_pow, eval_X]
  rw [mul_sum]
  apply sum_congr rfl
  intro k hk
  have hkn : k ≤ n := by simpa using hk
  rw [Nat.sub_sub_self hkn, Nat.choose_symm hkn]
  have hneg : (-t)^k = (-1 : K)^k * t^k := by rw [← mul_pow]; congr 1; ring
  rw [hneg]
  have hsign : (-1 : K)^(n-k) * (-1)^k = (-1)^n := by
    rw [← pow_add, Nat.sub_add_cancel hkn]
  linear_combination hsign * (n.choose k : K)^2 * t^k

section Characteristic
variable (p : ℕ) [CharP K p]

lemma small_natCast_ne_zero {k : ℕ} (hk : 0 < k) (hkp : k < p) : (k : K) ≠ 0 := by
  rw [Ne, CharP.cast_eq_zero_iff K p]
  exact Nat.not_dvd_of_pos_of_lt hk hkp

/-- In degree less than the characteristic, a zero derivative forces a constant. -/
lemma eq_C_of_derivative_eq_zero_small {f : K[X]} (hfdeg : f.natDegree < p)
    (hd : derivative f = 0) : f = C (f.coeff 0) := by
  ext k
  cases k with
  | zero => simp
  | succ k =>
    simp only [coeff_C, Nat.succ_ne_zero, ite_false]
    by_cases hk : k+1 ≤ f.natDegree
    · have h := congrArg (fun q : K[X] => q.coeff k) hd
      rw [coeff_derivative, coeff_zero] at h
      exact (mul_eq_zero.mp h).resolve_right
        (by simpa only [Nat.cast_add, Nat.cast_one] using
          small_natCast_ne_zero (K := K) p (by omega : 0 < k+1) (lt_of_le_of_lt hk hfdeg))
    · exact coeff_eq_zero_of_natDegree_lt (by omega)

lemma derivative_ne_zero_of_root_small {f : K[X]} {t : K}
    (hf : f ≠ 0) (hfdeg : f.natDegree < p) (ht : f.IsRoot t) : derivative f ≠ 0 := by
  intro hd
  have hc := eq_C_of_derivative_eq_zero_small p hfdeg hd
  have heval : f.coeff 0 = 0 := by
    change f.eval t = 0 at ht
    rw [hc, eval_C] at ht
    exact ht
  exact hf (by rw [hc, heval, C_0])

lemma rootMultiplicity_le_natDegree_aux {f : K[X]} (hf : f ≠ 0) (t : K) :
    f.rootMultiplicity t ≤ f.natDegree := by
  have h := natDegree_le_of_dvd (f.pow_rootMultiplicity_dvd t) hf
  simpa only [natDegree_pow, natDegree_X_sub_C, mul_one] using h

/-- A regular point of a second-order polynomial differential equation cannot
be a repeated root when the polynomial degree is below the characteristic. -/
theorem no_repeated_root_of_ode {f a b c : K[X]} {t : K}
    (hf : f ≠ 0) (hfdeg : f.natDegree < p)
    (hode : a * derivative (derivative f) + b * derivative f + c * f = 0)
    (ha : a.eval t ≠ 0) (ht : f.IsRoot t) : ¬ (derivative f).IsRoot t := by
  intro hdt
  let r := f.rootMultiplicity t
  have hr : 2 ≤ r := by
    have h := (one_lt_rootMultiplicity_iff_isRoot hf).mpr ⟨ht,hdt⟩
    exact h
  have hrp : r < p := lt_of_le_of_lt (rootMultiplicity_le_natDegree_aux hf t) hfdeg
  have hr0 : (r : K) ≠ 0 := small_natCast_ne_zero p (by omega) hrp
  have hdroot : (derivative f).rootMultiplicity t = r-1 :=
    derivative_rootMultiplicity_of_root_of_mem_nonZeroDivisors ht
      (mem_nonZeroDivisors_of_ne_zero hr0)
  have hdf : derivative f ≠ 0 := derivative_ne_zero_of_root_small p hf hfdeg ht
  have hdfdeg : (derivative f).natDegree < p :=
    lt_of_le_of_lt ((natDegree_derivative_le f).trans (Nat.sub_le _ _)) hfdeg
  have hddf : derivative (derivative f) ≠ 0 :=
    derivative_ne_zero_of_root_small p hdf hdfdeg hdt
  have hdcast : ((derivative f).rootMultiplicity t : K) ≠ 0 := by
    rw [hdroot]
    exact small_natCast_ne_zero p (by omega) (by omega)
  have hddroot : (derivative (derivative f)).rootMultiplicity t = r-2 := by
    rw [derivative_rootMultiplicity_of_root_of_mem_nonZeroDivisors hdt
      (mem_nonZeroDivisors_of_ne_zero hdcast), hdroot]
    omega
  have hdivf : (X-C t)^(r-1) ∣ f :=
    (pow_dvd_pow _ (Nat.sub_le r 1)).trans (f.pow_rootMultiplicity_dvd t)
  have hdivd : (X-C t)^(r-1) ∣ derivative f := by
    rw [← hdroot]
    exact (derivative f).pow_rootMultiplicity_dvd t
  have hdiva : (X-C t)^(r-1) ∣ a * derivative (derivative f) := by
    have hsum : (X-C t)^(r-1) ∣ b * derivative f + c * f :=
      dvd_add (dvd_mul_of_dvd_right hdivd _) (dvd_mul_of_dvd_right hdivf _)
    have heq : a * derivative (derivative f) = -(b * derivative f + c * f) := by
      linear_combination hode
    rw [heq]
    exact dvd_neg.mpr hsum
  have ha0 : a ≠ 0 := by intro h; simp [h] at ha
  have hproduct := mul_ne_zero ha0 hddf
  have hmult := (le_rootMultiplicity_iff hproduct).mpr hdiva
  rw [rootMultiplicity_mul hproduct, rootMultiplicity_eq_zero ha, zero_add, hddroot] at hmult
  omega

variable [Fact p.Prime]

lemma choose_cast_ne_zero_of_lt {n k : ℕ} (hkn : k ≤ n) (hnp : n < p) :
    (n.choose k : K) ≠ 0 := by
  have hfac : (n.factorial : K) ≠ 0 :=
    (IsUnit.natCast_factorial_iff_of_charP p).mpr hnp |>.ne_zero
  have h := congrArg (fun a : ℕ => (a : K)) (Nat.choose_mul_factorial_mul_factorial hkn)
  push_cast at h
  intro hzero
  simp only [hzero, zero_mul] at h
  exact hfac h.symm

lemma hassePolynomial_eval_one_ne_zero {n : ℕ} (hnp : 2*n < p) :
    (hassePolynomial (K := K) n).eval 1 ≠ 0 := by
  rw [hassePolynomial_eval_one]
  exact choose_cast_ne_zero_of_lt p (by omega) hnp

/-- Hasse polynomials of degree n have only simple roots in characteristic
p>2n. This includes the supersingular Legendre degree n=(p-1)/2. -/
theorem hassePolynomial_no_repeated_root {n : ℕ} (hnp : 2*n < p) {t : K}
    (ht : (hassePolynomial (K := K) n).IsRoot t) :
    ¬ (derivative (hassePolynomial (K := K) n)).IsRoot t := by
  have ht0 : t ≠ 0 := by intro h; simp [h, IsRoot] at ht
  have ht1 : t ≠ 1 := by
    intro h
    exact hassePolynomial_eval_one_ne_zero p hnp (by simpa [h, IsRoot] using ht)
  apply no_repeated_root_of_ode (K := K) (a := X*(1-X))
    (b := 1+C (2*(n : K)-1)*X) (c := -C ((n : K)^2)) p
    (hassePolynomial_monic (K := K) n).ne_zero
    (by simpa using (show n < p by omega))
    (by simpa only [neg_mul, sub_eq_add_neg] using hasse_differential_equation (K := K) n) _ ht
  simp only [eval_mul, eval_X, eval_sub, eval_one]
  exact mul_ne_zero ht0 (sub_ne_zero.mpr (Ne.symm ht1))

/-- Algebraically closed form of Hasse-polynomial separability. -/
theorem hassePolynomial_separable [IsAlgClosed K] {n : ℕ} (hnp : 2*n < p) :
    (hassePolynomial (K := K) n).Separable := by
  change IsCoprime (hassePolynomial (K := K) n) (derivative (hassePolynomial n))
  rw [Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed (k := K) K]
  intro t
  by_cases ht : (hassePolynomial (K := K) n).eval t = 0
  · right
    simpa only [aeval_def, Algebra.algebraMap_self, eval₂_id, IsRoot] using hassePolynomial_no_repeated_root p hnp ht
  · left
    simpa only [aeval_def, Algebra.algebraMap_self, eval₂_id] using ht

/-- The separability statement descends from the algebraic closure, so no
algebraic-closedness hypothesis is needed for the base field. -/
theorem hassePolynomial_separable_field {n : ℕ} (hnp : 2*n < p) :
    (hassePolynomial (K := K) n).Separable := by
  apply (separable_map (algebraMap K (AlgebraicClosure K))).mp
  rw [hassePolynomial_map]
  exact hassePolynomial_separable p hnp

/-- The familiar binomial congruence at p-1, expressed directly in the field. -/
theorem choose_pred_cast : ∀ k : ℕ, k < p →
    ((p-1).choose k : K) = (-1 : K)^k := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    have hk0 : k < p := by omega
    have hkp : k ≤ p-1 := by omega
    have hp1 : 1 ≤ p := (Fact.out : p.Prime).pos
    have hpcast : ((p-1 : ℕ) : K) = -1 := by
      rw [Nat.cast_sub hp1, Nat.cast_one, CharP.cast_eq_zero K p]
      ring
    have h := congrArg (fun a : ℕ => (a : K)) (Nat.choose_succ_right_eq (p-1) k)
    push_cast at h
    rw [Nat.cast_sub hkp, hpcast, ih hk0] at h
    apply (mul_right_cancel₀ (small_natCast_ne_zero (K := K) p (by omega : 0 < k+1) hk))
    push_cast
    rw [pow_succ]
    linear_combination h

/-- For the supersingular Hasse index, the value at one is exactly a sign. -/
theorem hassePolynomial_eval_one_sign {n : ℕ} (hp : p = 2*n+1) :
    (hassePolynomial (K := K) n).eval 1 = (-1 : K)^n := by
  rw [hassePolynomial_eval_one]
  have hpred : p-1 = 2*n := by omega
  rw [← hpred]
  exact choose_pred_cast p n (by omega)

end Characteristic
end IsogenyAttack.Legendre
