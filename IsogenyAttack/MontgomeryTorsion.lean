import IsogenyAttack.MontgomeryGeometry
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

namespace IsogenyAttack.Montgomery
open WeierstrassCurve.Affine
variable {K : Type*} [Field K] [DecidableEq K] {A : K}

lemma zeroPoint_nonsingular (A : K) : (curve A).toAffine.Nonsingular 0 0 := by
  rw [nonsingular_iff, equation_iff]
  norm_num [curve]

def zeroPoint (A : K) : (curve A).toAffine.Point :=
  .some 0 0 (zeroPoint_nonsingular A)

lemma zeroPoint_add_self (A : K) : zeroPoint A + zeroPoint A = 0 := by
  apply Point.add_self_of_Y_eq
  simp [negY, curve]

lemma unitPoint_nonsingular {y : K} (h2 : (2 : K) ≠ 0) (hy : y ≠ 0)
    (he : y^2 = A+2) : (curve A).toAffine.Nonsingular 1 y := by
  rw [nonsingular_iff, equation_iff]
  simp only [curve, zero_mul, one_pow, mul_one, add_zero]
  constructor
  · linear_combination he
  · right
    intro hz
    apply mul_ne_zero h2 hy
    linear_combination hz

def unitPoint {y : K} (h2 : (2 : K) ≠ 0) (hy : y ≠ 0) (he : y^2 = A+2) :
    (curve A).toAffine.Point := .some 1 y (unitPoint_nonsingular h2 hy he)

lemma unitPoint_add_self {y : K} (h2 : (2 : K) ≠ 0) (hy : y ≠ 0)
    (he : y^2 = A+2) : unitPoint h2 hy he + unitPoint h2 hy he = zeroPoint A := by
  have hny : y ≠ (curve A).toAffine.negY 1 y := by
    intro hz
    apply mul_ne_zero h2 hy
    simp only [negY, curve, zero_mul, sub_zero] at hz
    linear_combination hz
  have hs : (curve A).toAffine.slope 1 1 y y = y := by
    rw [slope_of_Y_ne rfl hny]
    simp only [curve, one_pow, mul_one, zero_mul, sub_zero, negY]
    rw [show y - -y = 2*y by ring]
    apply (div_eq_iff (mul_ne_zero h2 hy)).mpr
    linear_combination -2*he
  unfold unitPoint zeroPoint
  rw [Point.add_self_of_Y_ne hny]
  rw [Point.some.injEq]
  simp only [addX, addY, negAddY, negY, curve]
  dsimp only [curve] at hs
  rw [hs]
  constructor
  · linear_combination he
  · linear_combination -y*he

lemma unitPoint_four_nsmul {y : K} (h2 : (2 : K) ≠ 0) (hy : y ≠ 0)
    (he : y^2 = A+2) : (4 : ℕ) • unitPoint h2 hy he = 0 := by
  have h := zeroPoint_add_self A
  rw [← unitPoint_add_self h2 hy he] at h
  simpa only [show (4 : ℕ)=2*2 from rfl, mul_nsmul, two_nsmul] using h

lemma odd_nsmul_zeroPoint (n : ℕ) (hn : Odd n) : n • zeroPoint A = zeroPoint A := by
  obtain ⟨k,rfl⟩ := hn
  simp [add_nsmul, mul_nsmul, two_nsmul, zeroPoint_add_self]

lemma odd_nsmul_unitPoint {y : K} (h2 : (2 : K) ≠ 0) (hy : y ≠ 0)
    (he : y^2 = A+2) (n : ℕ) (hn : Odd n) :
    n • unitPoint h2 hy he = unitPoint h2 hy he ∨
      n • unitPoint h2 hy he = -unitPoint h2 hy he := by
  have h4 := unitPoint_four_nsmul h2 hy he
  have hm : n • unitPoint h2 hy he = (n%4) • unitPoint h2 hy he := by
    conv_lhs => rw [← Nat.mod_add_div n 4]
    simp [add_nsmul, mul_nsmul, h4]
  rw [hm]
  have hn2 : n%2=1 := Nat.odd_iff.mp hn
  have hmod : n%4=1 ∨ n%4=3 := by omega
  rcases hmod with h|h
  · simp [h]
  · right
    rw [h]
    apply eq_neg_of_add_eq_zero_left
    simpa only [show (4 : ℕ)=3+1 from rfl, add_nsmul, one_nsmul] using h4

/-- A Montgomery coordinate change preserving the marked x-coordinates 0 and 1
preserves its parameter. -/
lemma parameter_eq_of_marked_variableChange {B : K}
    (h2 : (2 : K) ≠ 0) (C : WeierstrassCurve.VariableChange K)
    (hC : C • curve A = curve B) (hr : C.r = 0) (hu : (C.u : K)^2 = 1) : A=B := by
  have hs : C.s = 0 := by
    have hh := congrArg WeierstrassCurve.a₁ hC
    simpa [WeierstrassCurve.variableChange_a₁, curve,
      mul_eq_zero, Units.ne_zero, h2] using hh
  simpa [WeierstrassCurve.variableChange_a₂, curve, hr, hs, hu]
    using congrArg WeierstrassCurve.a₂ hC

end IsogenyAttack.Montgomery
