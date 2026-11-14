import IsogenyAttack.MaximalityArithmetic
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Frobenius.Charpoly
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Frobenius.Supersingular
import TauCeti.AlgebraicGeometry.EllipticCurve.HasseBound
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom.BaseChange

/-! At either endpoint of the Hasse interval, the actual Frobenius morphism
is a scalar morphism. -/
namespace IsogenyAttack
open WeierstrassCurve TauCeti.Isogeny

variable {F : Type*} [Field F] [Finite F]

/-- The repeated-root case of the Frobenius characteristic polynomial. -/
theorem frobenius_scalar_of_trace_endpoint (W : WeierstrassCurve F) [W.IsElliptic]
    (m : ℤ) (hcard : (Nat.card F : ℤ) = m * m)
    (htrace : W.frobeniusTrace = 2 * m) :
    Hom.ofIsogeny (frobeniusIsogeny W.toAffine) = m • Hom.id W.toAffine := by
  have h := ofIsogeny_frobeniusIsogeny_comp_ofIsogeny_frobeniusIsogeny W.toAffine
  rw [htrace, ← Hom.mul_def, ← Hom.one_def] at h
  have hn : Nat.card F • (1 : Hom W.toAffine W.toAffine) =
      (m * m) • (1 : Hom W.toAffine W.toAffine) := by
    rw [← natCast_zsmul, hcard]
  rw [hn] at h
  simpa only [Hom.one_def] using repeated_root_scalar _ m h

/-- Full rational two-torsion forces a supersingular Frobenius over a square
field of characteristic `3 mod 4` to be one of the two scalar endpoints. -/
theorem supersingular_frobenius_scalar_endpoints (W : WeierstrassCurve F) [W.IsElliptic]
    (p : ℕ) [ExpChar F p] (hp : 0 < p) (hp4 : p % 4 = 3)
    (hcard : Nat.card F = p ^ 2) (hss : W.IsSupersingular p)
    (hfour : 4 ∣ Nat.card W.toAffine.Point) :
    Hom.ofIsogeny (frobeniusIsogeny W.toAffine) = -(p : ℤ) • Hom.id W.toAffine ∨
      Hom.ofIsogeny (frobeniusIsogeny W.toAffine) = (p : ℤ) • Hom.id W.toAffine := by
  have ht := (W.isSupersingular_iff_dvd_frobeniusTrace p).mp hss
  have hHasse := W.frobeniusTrace_sq_le_four_mul_card
  rw [hcard] at hHasse
  have hc4 : (4 : ℤ) ∣ (p : ℤ)^2 + 1 - W.frobeniusTrace := by
    rw [W.frobeniusTrace_eq_card_point, hcard]
    push_cast
    simpa using (show (4 : ℤ) ∣ (Nat.card W.toAffine.Point : ℤ) by exact_mod_cast hfour)
  rcases trace_endpoints hp hp4 ht (by exact_mod_cast hHasse) hc4 with hminus | hplus
  · left
    apply frobenius_scalar_of_trace_endpoint
    · rw [hcard]
      push_cast
      ring
    · convert hminus using 1 <;> ring
  · right
    apply frobenius_scalar_of_trace_endpoint
    · rw [hcard]
      push_cast
      ring
    · exact hplus

/-- A scalar Frobenius identity remains the same identity after base change. -/
theorem baseChangeFrobenius_scalar (W : WeierstrassCurve F) [W.IsElliptic]
    {L : Type*} [Field L] [Algebra F L] (m : ℤ)
    (h : Hom.ofIsogeny (frobeniusIsogeny W.toAffine) = m • Hom.id W.toAffine) :
    Hom.ofIsogeny (baseChangeFrobenius L W.toAffine) =
      m • Hom.id (W.baseChange L).toAffine := by
  have hm := congrArg (fun f : Hom W.toAffine W.toAffine => f.map (algebraMap F L)) h
  simp only [Hom.ofIsogeny_map, Hom.map_zsmul, Hom.id_map] at hm
  exact hm

end IsogenyAttack
