import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Mathlib.Tactic

/-!
Degree and separability ingredients for multiplication on genuine Mathlib
Weierstrass curves, in arbitrary characteristic. The polynomial identities
are proved directly from mathlib's division-polynomial coefficients; no
characteristic-zero hypothesis or elliptic-torsion counting axiom is used.
-/

namespace IsogenyAttack.TorsionPolynomials
open Polynomial WeierstrassCurve

variable {K : Type*} [Field K] (W : WeierstrassCurve K)

/-- Polynomial cutting out an x-coordinate fiber of the multiplication formula. -/
noncomputable def fibrePolynomial (n : ℕ) (x₀ : K) : K[X] :=
  W.Φ n - C x₀ * W.ΨSq n

/-- The degree bound for ΨSq suffices; n need not be invertible for this lemma. -/
theorem fibrePolynomial_natDegree (n : ℕ) (hn : 0 < n) (x₀ : K) :
    (fibrePolynomial W n x₀).natDegree = n ^ 2 := by
  have hn2 : 1 ≤ n ^ 2 := Nat.one_le_pow _ _ hn
  have hdeg : (C x₀ * W.ΨSq n).natDegree < (W.Φ n).natDegree := by
    rw [W.natDegree_Φ, Int.natAbs_natCast]
    exact lt_of_le_of_lt ((natDegree_C_mul_le _ _).trans (W.natDegree_ΨSq_le n))
      (by simpa using (show n ^ 2 - 1 < n ^ 2 by omega))
  rw [fibrePolynomial, natDegree_sub_eq_left_of_natDegree_lt hdeg,
    W.natDegree_Φ, Int.natAbs_natCast]

/-- The formal Wronskian of the rational multiplication formula. -/
noncomputable def multiplicationWronskian (n : ℕ) : K[X] :=
  derivative (W.Φ n) * W.ΨSq n - W.Φ n * derivative (W.ΨSq n)

/-- Its leading candidate coefficient is n², in arbitrary characteristic.
Only upper degree bounds for the derivatives are used, including when the
coefficient n²−1 vanishes in the field. -/
theorem multiplicationWronskian_coeff (n : ℕ) (hn : 0 < n) :
    (multiplicationWronskian W n).coeff (2 * n ^ 2 - 2) = (n : K) ^ 2 := by
  rcases Nat.lt_or_ge n 2 with hsmall | hlarge
  · have hn1 : n = 1 := by omega
    subst n
    simp [multiplicationWronskian]
  let N : ℕ := n ^ 2
  have hN : 2 ≤ N := by dsimp [N]; nlinarith
  have hΦ : (W.Φ n).natDegree ≤ N := W.natDegree_Φ_le n
  have hΨ : (W.ΨSq n).natDegree ≤ N - 1 := by simpa [N] using W.natDegree_ΨSq_le n
  have hdΦ : (derivative (W.Φ n)).natDegree ≤ N - 1 :=
    (natDegree_derivative_le _).trans (Nat.sub_le_sub_right hΦ 1)
  have hdΨ : (derivative (W.ΨSq n)).natDegree ≤ N - 2 := by
    have h := (natDegree_derivative_le (W.ΨSq n)).trans (Nat.sub_le_sub_right hΨ 1)
    simpa [Nat.sub_sub] using h
  have hΦc : (W.Φ n).coeff N = 1 := by simpa [N] using W.coeff_Φ n
  have hΨc : (W.ΨSq n).coeff (N-1) = (N : K) := by
    have h := W.coeff_ΨSq n
    simpa [N] using h
  have hdΦc : (derivative (W.Φ n)).coeff (N-1) = (N : K) := by
    rw [coeff_derivative, Nat.sub_add_cancel (by omega), hΦc, one_mul]
    push_cast [Nat.cast_sub (by omega : 1 ≤ N)]
    ring
  have hdΨc : (derivative (W.ΨSq n)).coeff (N-2) = (N : K) * ((N : K)-1) := by
    rw [coeff_derivative, show N-2+1=N-1 by omega, hΨc]
    push_cast [Nat.cast_sub (by omega : 2 ≤ N)]
    ring
  have heq1 : 2 * N - 2 = (N-1)+(N-1) := by omega
  have heq2 : 2 * N - 2 = N+(N-2) := by omega
  rw [multiplicationWronskian, coeff_sub]
  change ((derivative (W.Φ n) * W.ΨSq n).coeff (2*N-2) -
    (W.Φ n * derivative (W.ΨSq n)).coeff (2*N-2)) = _
  rw [heq1, coeff_mul_add_eq_of_natDegree_le hdΦ hΨ, hdΦc, hΨc]
  rw [← heq1, heq2, coeff_mul_add_eq_of_natDegree_le hΦ hdΨ, hΦc, hdΨc]
  dsimp [N]
  push_cast
  ring

/-- The rational multiplication formula is separable whenever n is nonzero
in the field; this is the polynomial nonvanishing ingredient, not yet a theorem
identifying that formula with the point-group multiplication map. -/
theorem multiplicationWronskian_ne_zero (n : ℕ) (hn : (n : K) ≠ 0) :
    multiplicationWronskian W n ≠ 0 := by
  have hnat : 0 < n := by
    by_contra h
    have hn0 : n = 0 := by omega
    exact hn (by simp [hn0])
  intro hz
  have hc := multiplicationWronskian_coeff W n hnat
  rw [hz, coeff_zero] at hc
  exact (pow_ne_zero 2 hn) hc.symm

end IsogenyAttack.TorsionPolynomials
