import IsogenyAttack.StationaryGeometry
import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass

/-! The Legendre j-map used in the root-counting argument is the j-invariant
of an actual Mathlib Weierstrass curve, with nonsingularity checked explicitly. -/

namespace IsogenyAttack.Legendre

variable {K : Type*} [Field K]

/-- The curve y²=x(x-1)(x-t), in Mathlib's Weierstrass coordinates. -/
def curve (t : K) : WeierstrassCurve K := ⟨0, -(t+1), 0, t, 0⟩

@[simp] theorem curve_c4 (t : K) : (curve t).c₄ = 16 * (t^2-t+1) := by
  simp only [curve, WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]
  ring

@[simp] theorem curve_discriminant (t : K) : (curve t).Δ = 16 * t^2 * (t-1)^2 := by
  simp only [curve, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

/-- Away from t=0,1 and characteristic two, the Legendre equation is elliptic. -/
theorem curve_isElliptic {t : K} (h2 : (2 : K) ≠ 0) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    (curve t).IsElliptic := by
  constructor
  rw [curve_discriminant]
  apply isUnit_iff_ne_zero.mpr
  have h16 : (16 : K) ≠ 0 := by
    have := pow_ne_zero 4 h2
    norm_num at this ⊢
    exact this
  exact mul_ne_zero (mul_ne_zero h16 (pow_ne_zero _ ht0))
    (pow_ne_zero _ (sub_ne_zero.mpr ht1))

/-- The rational degree-six map is exactly the elliptic curve's j-invariant. -/
theorem curve_jInvariant (t : K) [h : (curve t).IsElliptic] :
    (curve t).j = jInvariant t := by
  have hΔ := (curve t).isUnit_Δ.ne_zero
  rw [curve_discriminant] at hΔ
  have h16 : (16 : K) ≠ 0 := fun h => hΔ (by rw [h]; simp)
  have ht0 : t ≠ 0 := fun h => hΔ (by rw [h]; simp)
  have ht1 : t - 1 ≠ 0 := fun h => hΔ (by rw [h]; simp)
  rw [WeierstrassCurve.j, Units.val_inv_eq_inv_val, WeierstrassCurve.coe_Δ',
    curve_discriminant, curve_c4]
  unfold jInvariant
  field_simp
  ring

end IsogenyAttack.Legendre
