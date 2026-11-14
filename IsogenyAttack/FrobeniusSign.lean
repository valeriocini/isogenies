import IsogenyAttack.FrobeniusScalar
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Basic
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Frobenius.Torsion

/-! An order-four point whose ordinate is a rational polynomial in its
abscissa distinguishes the two scalar Frobenius signs. -/
namespace IsogenyAttack
open WeierstrassCurve WeierstrassCurve.Affine TauCeti.Isogeny

/-- A rational polynomial relation between the coordinates of an order-four
point rules out the positive scalar Frobenius when `p = 3 mod 4`. -/
theorem frobenius_ne_positive_of_four_torsion
    {F L : Type*} [Field F] [Finite F] [Field L] [Algebra F L] [DecidableEq L]
    (W : WeierstrassCurve F) [W.IsElliptic] {p : ℕ} (hp4 : p % 4 = 3)
    (i : F) (P : (W.baseChange L).toAffine.Point)
    (hfour : (4 : ℕ) • P = 0) (htwo : (2 : ℕ) • P ≠ 0)
    (hy : P.yCoord = algebraMap F L i * P.xCoord * (P.xCoord - 1)) :
    Hom.ofIsogeny (frobeniusIsogeny W.toAffine) ≠
      (p : ℤ) • Hom.id W.toAffine := by
  classical
  letI := Fintype.ofFinite F
  intro hpositive
  have hbase := baseChangeFrobenius_scalar W (L := L) (p : ℤ) hpositive
  have hpoint := congrArg (fun f : Hom (W.baseChange L).toAffine
      (W.baseChange L).toAffine => f.pointMap P) hbase
  simp only [Hom.pointMap_ofIsogeny_baseChangeFrobenius, Hom.zsmul_pointMap,
    Hom.id_pointMap, Hom.nsmul_pointMap, natCast_zsmul] at hpoint
  rw [nsmul_eq_neg_of_mod_four hp4 hfour] at hpoint
  let fr := FiniteField.frobeniusAlgHom F L
  have hx : fr P.xCoord = P.xCoord := by
    simpa only [Point.xCoord_map, Point.xCoord_neg] using congrArg Point.xCoord hpoint
  have hyfixed : fr P.yCoord = P.yCoord := by
    rw [hy, map_mul, map_mul, map_sub, map_one, AlgHom.commutes, hx]
  have hfixed : Point.map fr P = P := (Point.map_eq_self_iff fr P).mpr ⟨hx, hyfixed⟩
  have hself : P = -P := hfixed.symm.trans hpoint
  exact htwo (by simpa only [two_nsmul] using eq_neg_iff_add_eq_zero.mp hself)

end IsogenyAttack
