import Mathlib.Tactic
import Mathlib.FieldTheory.Finite.Basic

/-! Elementary arithmetic and algebra used to determine the sign of Frobenius. -/
namespace IsogenyAttack

/-- A supersingular trace over a square field, for a curve with full rational
`2`-torsion, is one of the two Hasse endpoints. -/
theorem trace_endpoints {p : ℕ} {t : ℤ} (hp : 0 < p) (hp4 : p % 4 = 3)
    (hpt : (p : ℤ) ∣ t) (hHasse : t ^ 2 ≤ 4 * (p : ℤ) ^ 2)
    (hfour : 4 ∣ (p : ℤ) ^ 2 + 1 - t) :
    t = -2 * (p : ℤ) ∨ t = 2 * (p : ℤ) := by
  obtain ⟨k, rfl⟩ := hpt
  have hpZ : (0 : ℤ) < p := by exact_mod_cast hp
  have hklo : -2 ≤ k := by
    by_contra h
    have : k ≤ -3 := by omega
    have hprod : (p : ℤ) * k ≤ -3 * p := by nlinarith
    nlinarith [sq_nonneg ((p : ℤ) * k + 3 * p), sq_nonneg (p : ℤ)]
  have hkhi : k ≤ 2 := by
    by_contra h
    have : 3 ≤ k := by omega
    have hprod : 3 * (p : ℤ) ≤ p * k := by nlinarith
    nlinarith [sq_nonneg ((p : ℤ) * k - 3 * p), sq_nonneg (p : ℤ)]
  have hp4Z : (p : ℤ) % 4 = 3 := by omega
  have hfour' : ((p : ℤ) ^ 2 + 1 - p * k) % 4 = 0 := Int.emod_eq_zero_of_dvd hfour
  interval_cases k <;> first
    | solve | left; ring
    | solve | right; ring
    | norm_num [Int.add_emod, Int.sub_emod, Int.mul_emod, pow_two, hp4Z] at hfour'

/-- In a ring without zero divisors a repeated quadratic root is scalar. -/
theorem repeated_root_scalar {R : Type*} [Ring R] [NoZeroDivisors R]
    (a : R) (m : ℤ)
    (h : a * a = (2 * m) • a - (m * m) • (1 : R)) :
    a = m • (1 : R) := by
  have hcomm : Commute a (m : R) := (Int.cast_commute m a).symm
  have hz : (a - (m : R)) * (a - (m : R)) = 0 := by
    simp only [zsmul_eq_mul, Int.cast_mul, Int.cast_ofNat, mul_one] at h
    rw [sub_mul, mul_sub, mul_sub, h]
    have hm : (m : R) * a = a * m := hcomm.eq.symm
    simp only [mul_assoc, hm]
    noncomm_ring
  rcases mul_eq_zero.mp hz with hz | hz <;>
    simpa only [zsmul_eq_mul, mul_one] using sub_eq_zero.mp hz

/-- The square field of an odd prime admits a square root of minus one. -/
theorem exists_sqrt_neg_one_of_square_card {F : Type*} [Field F] [Finite F]
    {p : ℕ} (hp4 : p % 4 = 3) (hcard : Nat.card F = p ^ 2)
    (hchar : ringChar F ≠ 2) : ∃ i : F, i ^ 2 = -1 := by
  classical
  letI := Fintype.ofFinite F
  have hmod : p ^ 2 % 4 = 1 := by simp [pow_two, Nat.mul_mod, hp4]
  have heven : Even (Fintype.card F / 2) := by
    rw [← Nat.card_eq_fintype_card, hcard, Nat.even_iff]
    omega
  have hs : IsSquare (-1 : F) :=
    (FiniteField.isSquare_iff hchar (neg_ne_zero.mpr one_ne_zero)).mpr heven.neg_one_pow
  obtain ⟨i, hi⟩ := hs
  exact ⟨i, by simpa [pow_two] using hi.symm⟩

/-- A scalar congruent to minus one modulo four acts by negation on four-torsion. -/
theorem nsmul_eq_neg_of_mod_four {G : Type*} [AddCommGroup G] {p : ℕ}
    (hp : p % 4 = 3) {P : G} (hP : (4 : ℕ) • P = 0) : p • P = -P := by
  rw [nsmul_eq_mod_nsmul p hP, hp]
  apply eq_neg_iff_add_eq_zero.mpr
  simpa only [← succ_nsmul] using hP

end IsogenyAttack
