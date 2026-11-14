import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.RelativeFrobenius.Supersingular
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.RelativeFrobenius.Factorisation
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.VariableChange
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.Degree
import IsogenyAttack.FrobeniusFixedField

open TauCeti.Isogeny

namespace IsogenyAttack

/-- The geometric j-invariant of a supersingular elliptic curve is fixed by
the square of Frobenius. Supersingularity is actual geometric p-torsion zero. -/
theorem supersingular_j_pow_square_eq {K : Type*} [Field K]
    (p : ℕ) [ExpChar K p] (W : WeierstrassCurve K) [W.IsElliptic]
    (hW : W.IsSupersingular p) : W.j^(p^2)=W.j := by
  let φ := mulByIntIsogenyOfNeZero W.toAffine
    (n := (p : ℤ)) (mod_cast expChar_ne_zero K p)
  have hs : φ.separableDegree = 1 :=
    (WeierstrassCurve.isSupersingular_iff_separableDegree_mulByIntIsogenyOfNeZero_eq_one p W).mp hW
  have hd : φ.degree = p^2 := by
    simp only [φ, degree_mulByIntIsogenyOfNeZero, Int.natAbs_natCast]
  have hi : φ.inseparableDegree = p^2 := by
    have h := φ.separableDegree_mul_inseparableDegree
    rwa [hs, one_mul, hd] at h
  obtain ⟨χ, hχ, -⟩ := existsUnique_comp_iterateRelativeFrobeniusIsogeny_eq p φ hi
  haveI := isSeparable_of_comp_iterateRelativeFrobeniusIsogeny_eq hi hχ
  have hχd : χ.degree = 1 :=
    (degree_eq_separableDegree_of_comp_iterateRelativeFrobeniusIsogeny_eq hχ).trans hs
  obtain ⟨C, hC, -⟩ := exists_variableChangeIsogeny_eq_of_degree_eq_one χ hχd
  have hj := WeierstrassCurve.variableChange_j (W.map (iterateFrobenius K p 2)) C
  have hj' : W.j = (W.map (iterateFrobenius K p 2)).j := by
    simpa only [hC] using hj
  rw [W.map_j] at hj'
  simpa only [iterateFrobenius_def] using hj'.symm

/-- Every geometric supersingular j-invariant lies in the explicitly
constructed quadratic finite subfield. -/
theorem supersingular_j_mem_quadraticField {K : Type*} [Field K]
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (W : WeierstrassCurve K) [W.IsElliptic] (hW : W.IsSupersingular p) :
    W.j ∈ frobeniusFixedField (K := K) p 2 :=
  supersingular_j_pow_square_eq p W hW

end IsogenyAttack
