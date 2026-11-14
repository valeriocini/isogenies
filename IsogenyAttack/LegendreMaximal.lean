import IsogenyAttack.FrobeniusSign
import IsogenyAttack.LegendreFourTorsion
import IsogenyAttack.HasseCriterion
import TauCeti.AlgebraicGeometry.EllipticCurve.MordellWeil.TwoTorsion
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.OneSubFrobenius.Degree
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! Supersingular Legendre curves over a square finite field have negative
scalar Frobenius when its characteristic is 3 modulo 4. -/

namespace IsogenyAttack.Legendre

open WeierstrassCurve WeierstrassCurve.Affine TauCeti.Isogeny

variable {F : Type*} [Field F]

instance curve_isCharNeTwoNF (t : F) : (curve t).IsCharNeTwoNF := ⟨rfl, rfl⟩

/-- All three nonzero geometric points of order two are rational on a
Legendre model, so its group of rational points has order divisible by four. -/
theorem four_dvd_card_point (t : F) [(curve t).IsElliptic] :
    4 ∣ Nat.card (curve t).toAffine.Point := by
  classical
  have ht0 := elliptic_parameter_ne_zero t
  have ht1 := elliptic_parameter_ne_one t
  have heval (x : F) : (curve t).toAffine.f.eval x = x * (x - 1) * (x - t) := by
    rw [Affine.eval_f]
    simp only [curve]
    ring
  have hset : {x : F | (curve t).toAffine.f.eval x = 0} = {0, 1, t} := by
    ext x
    simp [heval, mul_eq_zero, sub_eq_zero, or_assoc]
  have hc : Nat.card {x : F // (curve t).toAffine.f.eval x = 0} = 3 := by
    change Nat.card ↥{x : F | (curve t).toAffine.f.eval x = 0} = 3
    rw [Nat.card_coe_set_eq, hset]
    simp [Ne.symm ht0, Ne.symm ht1]
  have hk : Nat.card (nsmulAddMonoidHom (α := (curve t).toAffine.Point) 2).ker = 4 := by
    rw [Affine.card_ker_nsmul_two, hc]
  rw [← hk]
  exact AddSubgroup.card_addSubgroup_dvd_card _

/-- A rational square root of `-1` makes the `y` coordinate of a geometric
point of order four a rational polynomial in its `x` coordinate. -/
theorem exists_four_torsion_rational_relation
    {L : Type*} [Field L] [Algebra F L] [IsAlgClosed L] [DecidableEq L]
    (t i : F) [(curve t).IsElliptic] (hi : i ^ 2 = -1) :
    ∃ P : ((curve t).baseChange L).toAffine.Point,
      (4 : ℕ) • P = 0 ∧ (2 : ℕ) • P ≠ 0 ∧
      P.yCoord = algebraMap F L i * P.xCoord * (P.xCoord - 1) := by
  classical
  have hb : (curve t).baseChange L = curve (algebraMap F L t) := curve_map _ _
  have : (curve (algebraMap F L t)).IsElliptic := hb ▸ inferInstance
  rw [hb]
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap F L t) (by decide : 0 < 2)
  have hiL : (algebraMap F L i) ^ 2 = -1 := by
    rw [← map_pow, hi, map_neg, map_one]
  have h2 : (2 : L) ≠ 0 := Ring.two_ne_zero (Affine.ringChar_ne_two (curve (algebraMap F L t)).toAffine)
  obtain ⟨h, hd⟩ := half_zero_point h2 (elliptic_parameter_ne_zero _)
    (elliptic_parameter_ne_one _) hr hiL
  refine ⟨Point.some r (algebraMap F L i * r * (r - 1)) h, ?_, ?_, ?_⟩
  · calc
      (4 : ℕ) • Point.some r (algebraMap F L i * r * (r - 1)) h =
          (2 : ℕ) • ((2 : ℕ) • Point.some r (algebraMap F L i * r * (r - 1)) h) := by
            rw [← mul_nsmul]
      _ = 0 := by rw [hd, two_smul_zeroTwoPoint]
  · rw [hd]
    exact zeroTwoPoint_ne_zero _
  · rfl

/-- Over `F` of order `p²`, a supersingular Legendre curve has Frobenius
`[-p]` when `p ≡ 3 (mod 4)`. The sign is proved using geometric 4-torsion. -/
theorem supersingular_frobenius_negative [Finite F]
    (t : F) [(curve t).IsElliptic] (p : ℕ) [ExpChar F p]
    (hp : 0 < p) (hp4 : p % 4 = 3) (hcard : Nat.card F = p ^ 2)
    (hss : (curve t).IsSupersingular p) :
    Hom.ofIsogeny (frobeniusIsogeny (curve t).toAffine) =
      -(p : ℤ) • Hom.id (curve t).toAffine := by
  classical
  obtain hneg | hpos := supersingular_frobenius_scalar_endpoints
    (curve t) p hp hp4 hcard hss (four_dvd_card_point t)
  · exact hneg
  · obtain ⟨i, hi⟩ := exists_sqrt_neg_one_of_square_card hp4 hcard
      (Affine.ringChar_ne_two (curve t).toAffine)
    obtain ⟨P, hfour, htwo, hy⟩ := exists_four_torsion_rational_relation
      (L := AlgebraicClosure F) t i hi
    exact False.elim (frobenius_ne_positive_of_four_torsion
      (curve t) hp4 i P hfour htwo hy hpos)

end IsogenyAttack.Legendre

namespace IsogenyAttack

open WeierstrassCurve TauCeti.Isogeny

variable {F : Type*} [Field F] [Finite F]

/-- Negative scalar Frobenius determines the number of rational points,
by the degree of `1 - Frobenius`. -/
theorem pointCount_of_frobenius_negative (W : WeierstrassCurve F) [W.IsElliptic]
    (p : ℕ)
    (h : Hom.ofIsogeny (frobeniusIsogeny W.toAffine) =
      -(p : ℤ) • Hom.id W.toAffine) :
    W.pointCount = (p + 1) ^ 2 := by
  have hs : (1 : Hom W.toAffine W.toAffine) -
      (-(p : ℤ)) • Hom.id W.toAffine = (p + 1) • Hom.id W.toAffine := by
    rw [Hom.one_def, neg_smul, sub_neg_eq_add, natCast_zsmul, add_nsmul, one_smul]
    abel
  rw [← degree_oneSubFrobeniusIsogeny_eq_pointCount W.toAffine,
    ← Hom.degree_ofIsogeny, ofIsogeny_oneSubFrobeniusIsogeny, h, hs,
    Hom.degree_nsmul, Hom.degree_id, mul_one]

theorem card_point_of_frobenius_negative (W : WeierstrassCurve F) [W.IsElliptic]
    (p : ℕ)
    (h : Hom.ofIsogeny (frobeniusIsogeny W.toAffine) =
      -(p : ℤ) • Hom.id W.toAffine) :
    Nat.card W.toAffine.Point = (p + 1) ^ 2 := by
  rw [← W.pointCount_eq_card_point]
  exact pointCount_of_frobenius_negative W p h

namespace Legendre

/-- Every supersingular Legendre model over the field of order `p²` is
maximal if `p ≡ 3 (mod 4)`. -/
theorem supersingular_pointCount [ExpChar F p]
    (t : F) [(curve t).IsElliptic]
    (hp : 0 < p) (hp4 : p % 4 = 3) (hcard : Nat.card F = p ^ 2)
    (hss : (curve t).IsSupersingular p) :
    (curve t).pointCount = (p + 1) ^ 2 :=
  pointCount_of_frobenius_negative (curve t) p
    (supersingular_frobenius_negative t p hp hp4 hcard hss)

/-- The actual Frobenius trace of a supersingular Legendre model over
the square field is the negative endpoint of the Hasse interval. -/
theorem supersingular_frobeniusTrace [ExpChar F p]
    (t : F) [(curve t).IsElliptic]
    (hp : 0 < p) (hp4 : p % 4 = 3) (hcard : Nat.card F = p ^ 2)
    (hss : (curve t).IsSupersingular p) :
    (curve t).frobeniusTrace = -2 * (p : ℤ) := by
  rw [WeierstrassCurve.frobeniusTrace_def,
    supersingular_pointCount t hp hp4 hcard hss, hcard]
  push_cast
  ring

end Legendre
end IsogenyAttack
