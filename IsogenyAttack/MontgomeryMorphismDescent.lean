import IsogenyAttack.MontgomeryLegendre
import IsogenyAttack.IsogenyDescent

/-! Unique descent of every geometric isogeny between supersingular B=1
Montgomery curves over the quadratic finite field. -/

namespace IsogenyAttack.Montgomery

open WeierstrassCurve TauCeti

variable {F K : Type*} [Field F] [Fintype F] [Field K] [Algebra F K]
  [Algebra.IsAlgebraic F K] [IsGalois F K]

/-- If `#F = p²` and `p ≡ 3 (mod 4)`, every geometric isogeny between two
supersingular B=1 Montgomery curves over `F` is the base change of a unique
isogeny over `F`. No Frobenius or rationality hypothesis on the isogeny is
assumed: the two Frobenius identities are consequences of the curve equations. -/
theorem isogeny_descends (A B : F) (h2 : (2 : F) ≠ 0)
    (hA : A ^ 2 ≠ 4) (hB : B ^ 2 ≠ 4)
    (p : ℕ) [ExpChar F p] (hp : 0 < p) (hp4 : p % 4 = 3)
    (hcard : Nat.card F = p ^ 2)
    (hssA : (curve A).IsSupersingular p) (hssB : (curve B).IsSupersingular p)
    (φ : Isogeny ((curve A).baseChange K).toAffine ((curve B).baseChange K).toAffine) :
    ∃! ψ : Isogeny (curve A).toAffine (curve B).toAffine,
      ψ.map (algebraMap F K) = φ := by
  let := curve_isElliptic h2 hA
  let := curve_isElliptic h2 hB
  apply isogeny_descends_of_common_scalar_frobenius_ground_hom
    (curve A) (curve B) (-(p : ℤ)) ?_ ?_ φ
  · exact supersingular_frobenius_negative A h2 hA p hp hp4 hcard hssA
  · exact supersingular_frobenius_negative B h2 hB p hp hp4 hcard hssB

end IsogenyAttack.Montgomery
