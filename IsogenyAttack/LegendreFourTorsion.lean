import IsogenyAttack.LegendreCurve
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Tactic

/-! An explicit point of exact order four on a Legendre curve. -/
namespace IsogenyAttack.Legendre
open WeierstrassCurve WeierstrassCurve.Affine
variable {K : Type*} [Field K] [DecidableEq K]

@[simp] theorem curve_equation {t x y : K} :
    (curve t).toAffine.Equation x y ↔ y ^ 2 = x * (x - 1) * (x - t) := by
  rw [Affine.equation_iff]
  simp only [curve, zero_mul, zero_add, mul_zero, add_zero]
  constructor <;> intro h <;> linear_combination h

/-- The point `(0,0)` on a nonsingular Legendre curve. -/
def zeroTwoPoint (t : K) [(curve t).IsElliptic] : (curve t).toAffine.Point :=
  .some 0 0 (Affine.equation_iff_nonsingular.mp (by rw [curve_equation]; ring))

@[simp] theorem zeroTwoPoint_ne_zero (t : K) [(curve t).IsElliptic] :
    zeroTwoPoint t ≠ 0 := Point.some_ne_zero _

@[simp] theorem two_smul_zeroTwoPoint (t : K) [(curve t).IsElliptic] :
    (2 : ℕ) • zeroTwoPoint t = 0 := by
  rw [two_nsmul]
  apply Point.add_self_of_Y_eq
  simp [Affine.negY, curve]

/-- A square root of the Legendre parameter gives a half of `(0,0)`. -/
theorem half_zero_point {t r i : K} [(curve t).IsElliptic]
    (h2 : (2 : K) ≠ 0) (ht0 : t ≠ 0) (ht1 : t ≠ 1)
    (hr : r ^ 2 = t) (hi : i ^ 2 = -1) :
    ∃ h : (curve t).toAffine.Nonsingular r (i * r * (r - 1)),
      (2 : ℕ) • Point.some r (i * r * (r - 1)) h = zeroTwoPoint t := by
  have hr0 : r ≠ 0 := by intro h; simp [h] at hr; exact ht0 hr.symm
  have hr1 : r - 1 ≠ 0 := by
    intro h
    have : r = 1 := sub_eq_zero.mp h
    exact ht1 (by simpa [this] using hr.symm)
  have hi0 : i ≠ 0 := by intro h; simp [h] at hi
  have hy0 : i * r * (r - 1) ≠ 0 := mul_ne_zero (mul_ne_zero hi0 hr0) hr1
  have heq : (curve t).toAffine.Equation r (i * r * (r - 1)) := by
    rw [curve_equation, ← hr]
    calc
      (i * r * (r - 1)) ^ 2 = i ^ 2 * r ^ 2 * (r - 1) ^ 2 := by ring
      _ = r * (r - 1) * (r - r ^ 2) := by rw [hi]; ring
  let h := Affine.equation_iff_nonsingular.mp heq
  refine ⟨h, ?_⟩
  have hneg : i * r * (r - 1) ≠ (curve t).toAffine.negY r (i * r * (r - 1)) := by
    simp only [Affine.negY, curve, zero_mul, sub_zero]
    intro hh
    have hzero : (2 : K) * (i * r * (r - 1)) = 0 := by linear_combination hh
    exact (mul_ne_zero h2 hy0) hzero
  have hslope : (curve t).toAffine.slope r r (i * r * (r - 1)) (i * r * (r - 1)) =
      i * (r - 1) := by
    rw [Affine.slope_of_Y_ne rfl hneg]
    simp only [curve, Affine.negY, zero_mul, sub_zero]
    apply (div_eq_iff (by
      have : (2 : K) * (i * r * (r - 1)) ≠ 0 := mul_ne_zero h2 hy0
      convert this using 1 <;> ring)).mpr
    rw [← hr]
    calc
      3 * r ^ 2 + 2 * -(r ^ 2 + 1) * r + r ^ 2 =
          -2 * r * (r - 1) ^ 2 := by ring
      _ = i * (r - 1) * (i * r * (r - 1) - -(i * r * (r - 1))) := by
        linear_combination -2 * r * (r - 1) ^ 2 * hi
  rw [two_nsmul, Point.add_self_of_Y_ne hneg]
  change Point.some _ _ _ = Point.some 0 0 _
  apply (Point.some.injEq _ _ _ _ _ _).mpr
  rw [hslope]
  constructor
  · simp only [Affine.addX, curve, zero_mul, add_zero]
    rw [mul_pow, hi, ← hr]
    ring
  · simp only [Affine.addY, Affine.negAddY, Affine.negY, Affine.addX, curve,
      zero_mul, add_zero, sub_zero]
    rw [mul_pow, hi, ← hr]
    ring

end IsogenyAttack.Legendre
