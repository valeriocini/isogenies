import IsogenyAttack.SupersingularDescent
import IsogenyAttack.MontgomeryTorsion
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.RelativeFrobenius.Point
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.Hom

/-! Descent of the normalized Montgomery parameter, including its marked points. -/
namespace IsogenyAttack
open WeierstrassCurve WeierstrassCurve.Affine TauCeti TauCeti.Isogeny

theorem pointMap_variableChange {K : Type*} [Field K] [DecidableEq K]
    (W : WeierstrassCurve K) [W.IsElliptic] (C : VariableChange K)
    (P : W.toAffine.Point) :
    (Hom.ofIsogeny (variableChangeIsogeny C (rfl : C • W.toAffine = C • W.toAffine))).pointMap P =
      (Point.equivVariableChange W C).symm P := by
  rcases P with _ | ⟨a,b,h⟩
  · simp only [← Point.zero_def, Hom.pointMap_zero, Point.equivVariableChange_symm_zero]
  have hinv : (C.baseChange W.toAffine.FunctionField)⁻¹ =
      C⁻¹.baseChange W.toAffine.FunctionField :=
    (map_inv (VariableChange.mapHom (algebraMap K W.toAffine.FunctionField)) C).symm
  rw [Hom.pointMap_eq_iff, Hom.tautologicalPoint_ofIsogeny,
    variableChangeIsogeny_pullback, tautologicalPoint_variableChangePullback,
    genericPoint_eq_some, pointEquivVariableChange_symm_some,
    Point.equivVariableChange_symm_some, Point.equivBaseChangeSelf_some,
    some_sub_baseChange_mem_polePoints_iff, coe_pointEquivDegreeOnePlace_some, hinv]
  simp only [VariableChange.baseChange, VariableChange.map_u, VariableChange.map_r,
    VariableChange.map_s, VariableChange.map_t, Units.coe_map, MonoidHom.coe_ofClass,
    map_add, map_mul, map_pow]
  let v := (Place.ofPrime K W.toAffine.FunctionField (CoordinateRing.pointPlace h.1)).valuation
  have hm (c : K) {z : W.toAffine.FunctionField} (hz : v z < 1) :
      v (algebraMap K W.toAffine.FunctionField c * z) < 1 := by
    rw [map_mul]
    exact (mul_le_mul_of_nonneg_right (Valuation.IsTrivialOn.valuation_algebraMap_le_one v c) zero_le).trans_lt
      (by simpa using hz)
  have hx := valuation_pointPlace_genericX_sub_lt_one W.toAffine h.1
  have hy := valuation_pointPlace_genericY_sub_lt_one W.toAffine h.1
  constructor
  · convert hm (((C⁻¹).u : K)^2) hx using 1; simp only [map_pow]; congr 1; ring
  · convert v.map_add_lt (hm (((C⁻¹).u : K)^3) hy)
      (hm ((((C⁻¹).u : K)^2) * (C⁻¹).s) hx) using 1
    simp only [map_pow, map_mul]
    congr 1
    ring

theorem pointMap_variableChange_xCoord {K : Type*} [Field K] [DecidableEq K]
    {W V : WeierstrassCurve K} [W.IsElliptic] [V.IsElliptic] (C : VariableChange K)
    (hC : C • W = V) {x y : K} (h : W.toAffine.Nonsingular x y) :
    ((Hom.ofIsogeny (variableChangeIsogeny C hC)).pointMap (.some x y h)).xCoord =
      ((C⁻¹).u : K)^2 * x + (C⁻¹).r := by
  subst V
  rw [pointMap_variableChange, Point.equivVariableChange_symm_some, Point.xCoord_some]

namespace Montgomery

/-- Every supersingular normalized Montgomery parameter in odd characteristic is fixed by
the square of Frobenius.  The proof uses the marked points `(0,0)` and `(1,y)` of orders two
and four to rigidify the degree-one factor of multiplication by the characteristic. -/
theorem supersingular_parameter_pow_square_eq {K : Type*} [Field K] [IsAlgClosed K]
    (p : ℕ) [Fact p.Prime] [CharP K p] (hp : p ≠ 2)
    (A : K) [(curve A).IsElliptic] (hA : (curve A).IsSupersingular p) :
    A^(p^2) = A := by
  classical
  let φ := mulByIntIsogenyOfNeZero (curve A).toAffine
    (n := (p : ℤ)) (mod_cast expChar_ne_zero K p)
  have hs : φ.separableDegree = 1 :=
    (WeierstrassCurve.isSupersingular_iff_separableDegree_mulByIntIsogenyOfNeZero_eq_one
      p (curve A)).mp hA
  have hd : φ.degree = p^2 := by
    simp only [φ, degree_mulByIntIsogenyOfNeZero, Int.natAbs_natCast]
  have hi : φ.inseparableDegree = p^2 := by
    have h := φ.separableDegree_mul_inseparableDegree
    rwa [hs, one_mul, hd] at h
  obtain ⟨χ, hχ, -⟩ := existsUnique_comp_iterateRelativeFrobeniusIsogeny_eq p φ hi
  have := isSeparable_of_comp_iterateRelativeFrobeniusIsogeny_eq hi hχ
  have hχd : χ.degree = 1 :=
    (degree_eq_separableDegree_of_comp_iterateRelativeFrobeniusIsogeny_eq hχ).trans hs
  obtain ⟨C, hC, he⟩ := exists_variableChangeIsogeny_eq_of_degree_eq_one χ hχd
  have hpoint (P : (curve A).toAffine.Point) :
      (Hom.ofIsogeny (variableChangeIsogeny C hC)).pointMap
        (Point.mapAlong (iterateFrobenius K p 2) (iterateFrobenius K p 2).injective P) =
      p • P := by
    have h := congrArg (fun f : Isogeny (curve A).toAffine (curve A).toAffine =>
      (Hom.ofIsogeny f).pointMap P) hχ
    rw [← Hom.ofIsogeny_comp_ofIsogeny, Hom.comp_pointMap,
      pointMap_iterateRelativeFrobeniusIsogeny, ← he] at h
    simpa only [φ, ofIsogeny_mulByIntIsogeny, Hom.zsmul_pointMap,
      Hom.id_pointMap, natCast_zsmul, Hom.nsmul_pointMap] using h
  have hodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp
  have hr : (C⁻¹).r = 0 := by
    have h := congrArg Point.xCoord (hpoint (zeroPoint A))
    rw [odd_nsmul_zeroPoint p hodd] at h
    simpa only [zeroPoint, Point.mapAlong_some, map_zero,
      pointMap_variableChange_xCoord, zero_mul, mul_zero, zero_add, Point.xCoord_some] using h
  have h2 : (2 : K) ≠ 0 := by
    intro h
    have := (CharP.cast_eq_zero_iff K p 2).mp h
    exact hp ((Nat.dvd_prime Nat.prime_two).mp this |>.resolve_left (Fact.out : p.Prime).ne_one)
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq (A + 2) (by decide : 0 < (2 : ℕ))
  have hy0 : y ≠ 0 := by
    intro h
    have hΔ := (curve A).isUnit_Δ.ne_zero
    rw [curve_discriminant] at hΔ
    rw [h, zero_pow (by decide : 2 ≠ 0)] at hy
    have heA : A = -2 := by linear_combination -hy
    norm_num [heA] at hΔ
  have hu : ((C⁻¹).u : K)^2 = 1 := by
    have h := congrArg Point.xCoord (hpoint (unitPoint h2 hy0 hy))
    have hpP := odd_nsmul_unitPoint h2 hy0 hy p hodd
    rcases hpP with hpP | hpP
    all_goals
      rw [hpP] at h
      simpa only [unitPoint, Point.mapAlong_some, map_one,
        pointMap_variableChange_xCoord, mul_one, hr, add_zero,
        Point.xCoord_some, Point.neg_some] using h
  have hm : (curve A).map (iterateFrobenius K p 2) = curve (A^(p^2)) := by
    ext <;> simp [curve, iterateFrobenius_def, (Fact.out : p.Prime).ne_zero]
  change C • (curve A).map (iterateFrobenius K p 2) = curve A at hC
  have hCinv : C⁻¹ • curve A = curve (A^(p^2)) := by
    rw [← hC, inv_smul_smul]
    exact hm
  exact (parameter_eq_of_marked_variableChange h2 C⁻¹ hCinv hr hu).symm

theorem supersingular_parameter_mem_quadraticField {K : Type*} [Field K] [IsAlgClosed K]
    (p : ℕ) [Fact p.Prime] [CharP K p] (hp : p ≠ 2)
    (A : K) [(curve A).IsElliptic] (hA : (curve A).IsSupersingular p) :
    A ∈ frobeniusFixedField (K := K) p 2 :=
  supersingular_parameter_pow_square_eq p hp A hA

end Montgomery
end IsogenyAttack

