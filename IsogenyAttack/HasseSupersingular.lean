import IsogenyAttack.HassePointCount
import IsogenyAttack.HasseFiniteDescent
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Frobenius.Supersingular

namespace IsogenyAttack.Legendre
open Polynomial

variable {K : Type*} [Field K]

/-- The classical Hasse criterion for an actual elliptic equation over any
finite field of odd characteristic. -/
theorem isSupersingular_iff_hasseCoefficient [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 2 < p)
    (W : WeierstrassCurve K) [W.IsElliptic]
    (h1 : W.a₁ = 0) (h3 : W.a₃ = 0) :
    W.IsSupersingular p ↔ hasseCoefficient p W = 0 := by
  classical
  let := Fintype.ofFinite K
  rw [WeierstrassCurve.isSupersingular_iff_dvd_frobeniusTrace p W,
    WeierstrassCurve.frobeniusTrace_eq_card_point]
  simpa only [Nat.card_eq_fintype_card] using
    characteristic_dvd_pointTrace_iff_hasseCoefficient p hp W h1 h3

/-- The finite-field criterion descends an integral Legendre parameter to
its finite field of definition and then extends the actual curve back. -/
theorem curve_isSupersingular_iff_hasseCoefficient_of_integral
    (p : ℕ) [Fact p.Prime] [CharP K p] [Algebra (ZMod p) K]
    (hp : 2 < p) (t : K) [(curve t).IsElliptic]
    (ht : IsIntegral (ZMod p) t) :
    (curve t).IsSupersingular p ↔ hasseCoefficient p (curve t) = 0 := by
  classical
  let F : IntermediateField (ZMod p) K := IntermediateField.adjoin (ZMod p) {t}
  have : Module.Finite (ZMod p) F := IntermediateField.adjoin.finiteDimensional ht
  have : Finite F := Module.finite_of_finite (ZMod p)
  let t₀ : F := ⟨t, IntermediateField.subset_adjoin (ZMod p) {t}
    (Set.mem_singleton t)⟩
  have ht0 : t₀ ≠ 0 := fun h => elliptic_parameter_ne_zero t (congrArg Subtype.val h)
  have ht1 : t₀ ≠ 1 := fun h => elliptic_parameter_ne_one t (congrArg Subtype.val h)
  have := curve_isElliptic (small_natCast_ne_zero p (k := 2) (by decide) hp) ht0 ht1
  have hbase : (curve t₀).baseChange K = curve t := by
    change (curve t₀).map (algebraMap F K) = curve t
    rw [curve_map]
    rfl
  rw [← hbase,
    WeierstrassCurve.isSupersingular_baseChange_iff (p := p) (W := curve t₀)
      (Fact.out : p.Prime).ne_zero K,
    isSupersingular_iff_hasseCoefficient p hp (curve t₀) rfl rfl]
  change hasseCoefficient p (curve t₀) = 0 ↔
    hasseCoefficient p ((curve t₀).map (algebraMap F K)) = 0
  rw [hasseCoefficient_map]
  constructor
  · intro hz
    simp [hz]
  · intro hz
    exact (algebraMap F K).injective (hz.trans (map_zero _).symm)

/-- Over an algebraic extension of the prime field, the Hasse criterion is
an equivalence with the genuine geometric p-torsion definition. -/
theorem curve_isSupersingular_iff_hasseCoefficient_of_isAlgebraic
    (p : ℕ) [Fact p.Prime] [CharP K p] [Algebra (ZMod p) K]
    [Algebra.IsAlgebraic (ZMod p) K]
    (hp : 2 < p) (t : K) [(curve t).IsElliptic] :
    (curve t).IsSupersingular p ↔ hasseCoefficient p (curve t) = 0 :=
  curve_isSupersingular_iff_hasseCoefficient_of_integral p hp t
    (Algebra.IsAlgebraic.isAlgebraic t).isIntegral

/-- Every Hasse-polynomial root gives an actual supersingular elliptic
curve, in any field of the stated characteristic. -/
theorem curve_isSupersingular_of_hasse_root
    (p n : ℕ) [Fact p.Prime] [CharP K p] [Algebra (ZMod p) K]
    (hp : 2 < p) (hpn : p=2*n+1) (t : K)
    [(curve t).IsElliptic] (ht : (hassePolynomial (K := K) n).IsRoot t) :
    (curve t).IsSupersingular p := by
  apply (curve_isSupersingular_iff_hasseCoefficient_of_integral p hp t
    (hasseRoot_isIntegral p n t ht)).mpr
  exact (curve_hasseCoefficient_zero_iff p n hpn t).mpr ht


/-- On an algebraically closed algebraic extension of the prime field, the
geometric coefficient-zero locus is exactly genuine supersingularity. -/
theorem hasLegendreHasseZero_iff_isSupersingular
    (p : ℕ) [Fact p.Prime] [CharP K p] [Algebra (ZMod p) K]
    [Algebra.IsAlgebraic (ZMod p) K] [IsAlgClosed K]
    (hp : 2 < p) (W : WeierstrassCurve K) [W.IsElliptic] :
    HasLegendreHasseZero p W ↔ W.IsSupersingular p := by
  constructor
  · rintro ⟨t, C, hC, ht⟩
    have : (curve t).IsElliptic := hC ▸ (inferInstance : (C • W).IsElliptic)
    have hs := (curve_isSupersingular_iff_hasseCoefficient_of_isAlgebraic p hp t).mpr ht
    rw [← hC, WeierstrassCurve.isSupersingular_variableChange_iff] at hs
    exact hs
  · intro hs
    obtain ⟨t, ht, C, hC⟩ := exists_legendre_model
      (small_natCast_ne_zero p (k := 2) (by decide) hp) W
    have := ht
    refine ⟨t, C, hC, ?_⟩
    apply (curve_isSupersingular_iff_hasseCoefficient_of_isAlgebraic p hp t).mp
    rw [← hC, WeierstrassCurve.isSupersingular_variableChange_iff]
    exact hs

/-- The explicit finite Hasse j-set is exactly the set of j-invariants of
actual supersingular elliptic curves. -/
theorem isSupersingular_iff_j_mem_hasse
    (p : ℕ) [Fact p.Prime] [CharP K p] [Algebra (ZMod p) K]
    [Algebra.IsAlgebraic (ZMod p) K] [IsAlgClosed K] [DecidableEq K]
    (hp : 2 < p) (W : WeierstrassCurve K) [W.IsElliptic] :
    W.IsSupersingular p ↔
      W.j ∈ (hassePolynomial (K := K) ((p-1)/2)).roots.toFinset.image jInvariant := by
  exact (hasLegendreHasseZero_iff_isSupersingular p hp W).symm.trans
    (hasLegendreHasseZero_iff_j_mem p hp W)

end IsogenyAttack.Legendre
