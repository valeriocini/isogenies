import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Descent
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Frobenius.BaseChange
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.Commute
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom.BaseChange
import TauCeti.FieldTheory.Finite.FrobeniusFixed

/-!
# Descent when Frobenius is a common scalar

Commutation with the finite-field Frobenius forces the coefficients of an
isogeny to lie in the ground field. Consequently every geometric isogeny
between two curves with the same scalar Frobenius descends uniquely.
-/
namespace IsogenyAttack

open WeierstrassCurve WeierstrassCurve.Affine TauCeti Polynomial
open scoped WeierstrassCurve RatFunc nonZeroDivisors

noncomputable section

variable {F K : Type*} [Field F] [Fintype F] [Field K] [Algebra F K]
    [Algebra.IsAlgebraic F K]

private abbrev coeffFrobenius : K ≃ₐ[F] K :=
  _root_.FiniteField.frobeniusAlgEquivOfAlgebraic F K

private theorem polynomial_fixed_of_frobenius_fixed (p : K[X])
    (hp : p.map (coeffFrobenius (F := F) (K := K)).toRingHom = p)
    (σ : K ≃ₐ[F] K) : p.map σ.toRingHom = p := by
  ext n
  have hpn : (p.coeff n) ^ Fintype.card F = p.coeff n := by
    have he := congrArg (fun q : K[X] => q.coeff n) hp
    rw [coeff_map] at he
    exact he
  obtain ⟨a, ha⟩ := (TauCeti.FiniteField.pow_card_eq_self_iff_mem_range_algebraMap _).mp hpn
  simp only [coeff_map]
  rw [← ha]
  exact σ.commutes a

private theorem ratFunc_fixed_of_frobenius_fixed (z : RatFunc K)
    (hz : RatFunc.mapRingHom
      (Polynomial.mapRingHom (coeffFrobenius (F := F) (K := K)).toRingHom)
      (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
        (Polynomial.map_injective _ (coeffFrobenius (F := F) (K := K)).injective)) z = z)
    (σ : K ≃ₐ[F] K) :
    RatFunc.mapRingHom (Polynomial.mapRingHom σ.toRingHom)
      (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
        (Polynomial.map_injective _ σ.injective)) z = z := by
  have hn : z.num.map (coeffFrobenius (F := F) (K := K)).toRingHom = z.num := by
    simpa only [RatFunc.num_mapRingHom] using congrArg RatFunc.num hz
  have hd : z.denom.map (coeffFrobenius (F := F) (K := K)).toRingHom = z.denom := by
    simpa only [RatFunc.denom_mapRingHom] using congrArg RatFunc.denom hz
  rw [RatFunc.coe_mapRingHom_eq_coe_map, RatFunc.map_apply]
  simp only [Polynomial.coe_mapRingHom,
    polynomial_fixed_of_frobenius_fixed _ hn σ,
    polynomial_fixed_of_frobenius_fixed _ hd σ]
  exact RatFunc.num_div_denom z

/-- A function fixed by coefficient Frobenius is fixed by every coefficient
automorphism: its normalized rational-function coefficients lie in F. -/
theorem functionField_fixed_of_frobenius_fixed (W : WeierstrassCurve F)
    (z : (W⁄K).toAffine.FunctionField)
    (hz : W.functionFieldGaloisAction (coeffFrobenius (F := F) (K := K)) z = z)
    (σ : K ≃ₐ[F] K) : W.functionFieldGaloisAction σ z = z := by
  apply (Affine.FunctionField.basis (W⁄K).toAffine (RatFunc K)).repr.injective
  ext i
  rw [W.functionFieldGaloisAction_basis_repr]
  apply ratFunc_fixed_of_frobenius_fixed
  rw [← W.functionFieldGaloisAction_basis_repr, hz]

/-- The geometric Frobenius pullback composed with coefficient Frobenius is
the q-th-power map on the entire function field. -/
theorem frobenius_pullback_coeff_action (W : WeierstrassCurve F)
    (z : (W⁄K).toAffine.FunctionField) :
    (Isogeny.baseChangeFrobenius K W.toAffine).fieldPullback
      (W.functionFieldGaloisAction (coeffFrobenius (F := F) (K := K)) z) =
        z ^ Nat.card F := by
  have h : (Isogeny.baseChangeFrobenius K W.toAffine).fieldPullback.toRingHom.comp
      (W.functionFieldGaloisAction (coeffFrobenius (F := F) (K := K))).toRingHom =
      (_root_.FiniteField.frobeniusAlgHom F (W⁄K).toAffine.FunctionField).toRingHom := by
    apply Affine.FunctionField.ringHom_ext
    · intro a
      change (Isogeny.baseChangeFrobenius K W.toAffine).fieldPullback
        (W.functionFieldGaloisAction coeffFrobenius
          (algebraMap K (W⁄K).toAffine.FunctionField a)) =
        (algebraMap K (W⁄K).toAffine.FunctionField a) ^ Fintype.card F
      rw [functionFieldGaloisAction_algebraMap, AlgHom.commutes]
      exact map_pow _ _ _
    · change (Isogeny.baseChangeFrobenius K W.toAffine).fieldPullback
        (W.functionFieldGaloisAction coeffFrobenius (W⁄K).toAffine.genericX) =
        (W⁄K).toAffine.genericX ^ Fintype.card F
      rw [functionFieldGaloisAction_genericX,
        Isogeny.fieldPullback_baseChangeFrobenius_genericX, Nat.card_eq_fintype_card]
    · change (Isogeny.baseChangeFrobenius K W.toAffine).fieldPullback
        (W.functionFieldGaloisAction coeffFrobenius (W⁄K).toAffine.genericY) =
        (W⁄K).toAffine.genericY ^ Fintype.card F
      rw [functionFieldGaloisAction_genericY,
        Isogeny.fieldPullback_baseChangeFrobenius_genericY, Nat.card_eq_fintype_card]
  have he := RingHom.congr_fun h z
  change (Isogeny.baseChangeFrobenius K W.toAffine).fieldPullback
    (W.functionFieldGaloisAction coeffFrobenius z) = z ^ Fintype.card F at he
  simpa only [Nat.card_eq_fintype_card] using he

variable [IsGalois F K]

/-- An actual geometric isogeny commuting with the ground-field Frobenius
descends uniquely to that finite field. No separability assumption on the
isogeny is needed. -/
theorem isogeny_descends_of_commutes_frobenius (W₁ W₂ : WeierstrassCurve F)
    (φ : Isogeny (W₁⁄K).toAffine (W₂⁄K).toAffine)
    (hc : φ.comp (Isogeny.baseChangeFrobenius K W₁.toAffine) =
      (Isogeny.baseChangeFrobenius K W₂.toAffine).comp φ) :
    ∃! ψ : Isogeny W₁.toAffine W₂.toAffine, ψ.map (algebraMap F K) = φ := by
  apply (Isogeny.existsUnique_map_eq_iff_galoisEquivariant W₁ W₂ φ).mpr
  have hcomm (z : (W₂⁄K).toAffine.FunctionField) :
      (Isogeny.baseChangeFrobenius K W₁.toAffine).fieldPullback (φ.fieldPullback z) =
        φ.fieldPullback ((Isogeny.baseChangeFrobenius K W₂.toAffine).fieldPullback z) := by
    have he := congrArg (fun ψ => ψ.fieldPullback z) hc
    simpa only [Isogeny.comp_fieldPullback, AlgHom.comp_apply] using he
  have hx : W₁.functionFieldGaloisAction coeffFrobenius
      (φ.fieldPullback (W₂⁄K).toAffine.genericX) =
        φ.fieldPullback (W₂⁄K).toAffine.genericX := by
    apply (Isogeny.baseChangeFrobenius K W₁.toAffine).fieldPullback.injective
    change (Isogeny.baseChangeFrobenius K W₁.toAffine).fieldPullback
        (W₁.functionFieldGaloisAction coeffFrobenius
          (φ.fieldPullback (W₂⁄K).toAffine.genericX)) =
      (Isogeny.baseChangeFrobenius K W₁.toAffine).fieldPullback
        (φ.fieldPullback (W₂⁄K).toAffine.genericX)
    rw [frobenius_pullback_coeff_action, hcomm,
      Isogeny.fieldPullback_baseChangeFrobenius_genericX, map_pow]
  have hy : W₁.functionFieldGaloisAction coeffFrobenius
      (φ.fieldPullback (W₂⁄K).toAffine.genericY) =
        φ.fieldPullback (W₂⁄K).toAffine.genericY := by
    apply (Isogeny.baseChangeFrobenius K W₁.toAffine).fieldPullback.injective
    change (Isogeny.baseChangeFrobenius K W₁.toAffine).fieldPullback
        (W₁.functionFieldGaloisAction coeffFrobenius
          (φ.fieldPullback (W₂⁄K).toAffine.genericY)) =
      (Isogeny.baseChangeFrobenius K W₁.toAffine).fieldPullback
        (φ.fieldPullback (W₂⁄K).toAffine.genericY)
    rw [frobenius_pullback_coeff_action, hcomm,
      Isogeny.fieldPullback_baseChangeFrobenius_genericY, map_pow]
  intro σ z
  have he : (W₁.functionFieldGaloisAction σ).toRingHom.comp φ.fieldPullback.toRingHom =
      φ.fieldPullback.toRingHom.comp (W₂.functionFieldGaloisAction σ).toRingHom := by
    apply Affine.FunctionField.ringHom_ext
    · intro a
      change W₁.functionFieldGaloisAction σ
          (φ.fieldPullback (algebraMap K (W₂⁄K).toAffine.FunctionField a)) =
        φ.fieldPullback (W₂.functionFieldGaloisAction σ
          (algebraMap K (W₂⁄K).toAffine.FunctionField a))
      rw [AlgHom.commutes, functionFieldGaloisAction_algebraMap,
        functionFieldGaloisAction_algebraMap, AlgHom.commutes]
    · change W₁.functionFieldGaloisAction σ (φ.fieldPullback (W₂⁄K).toAffine.genericX) =
        φ.fieldPullback (W₂.functionFieldGaloisAction σ (W₂⁄K).toAffine.genericX)
      rw [functionFieldGaloisAction_genericX]
      exact functionField_fixed_of_frobenius_fixed W₁ _ hx σ
    · change W₁.functionFieldGaloisAction σ (φ.fieldPullback (W₂⁄K).toAffine.genericY) =
        φ.fieldPullback (W₂.functionFieldGaloisAction σ (W₂⁄K).toAffine.genericY)
      rw [functionFieldGaloisAction_genericY]
      exact functionField_fixed_of_frobenius_fixed W₁ _ hy σ
  exact RingHom.congr_fun he z

/-- Every geometric isogeny between finite-field elliptic curves whose
Frobenius endomorphisms are the same nonzero integer scalar is uniquely
defined over the finite ground field. -/
theorem isogeny_descends_of_common_scalar_frobenius
    (W₁ W₂ : WeierstrassCurve F) [W₁.IsElliptic] [W₂.IsElliptic]
    {n : ℤ} (hn : n ≠ 0)
    (h₁ : Isogeny.baseChangeFrobenius K W₁.toAffine =
      Isogeny.mulByIntIsogenyOfNeZero (W₁⁄K).toAffine hn)
    (h₂ : Isogeny.baseChangeFrobenius K W₂.toAffine =
      Isogeny.mulByIntIsogenyOfNeZero (W₂⁄K).toAffine hn)
    (φ : Isogeny (W₁⁄K).toAffine (W₂⁄K).toAffine) :
    ∃! ψ : Isogeny W₁.toAffine W₂.toAffine, ψ.map (algebraMap F K) = φ := by
  apply isogeny_descends_of_commutes_frobenius W₁ W₂ φ
  rw [h₁, h₂]
  exact Isogeny.comp_mulByIntIsogenyOfNeZero φ hn

/-- The common-scalar descent criterion in the additive morphism group.
This form accepts the scalar Frobenius identities proved from the trace. -/
theorem isogeny_descends_of_common_scalar_frobenius_hom
    (W₁ W₂ : WeierstrassCurve F) [W₁.IsElliptic] [W₂.IsElliptic]
    (n : ℤ)
    (h₁ : Isogeny.Hom.ofIsogeny (Isogeny.baseChangeFrobenius K W₁.toAffine) =
      n • Isogeny.Hom.id (W₁⁄K).toAffine)
    (h₂ : Isogeny.Hom.ofIsogeny (Isogeny.baseChangeFrobenius K W₂.toAffine) =
      n • Isogeny.Hom.id (W₂⁄K).toAffine)
    (φ : Isogeny (W₁⁄K).toAffine (W₂⁄K).toAffine) :
    ∃! ψ : Isogeny W₁.toAffine W₂.toAffine, ψ.map (algebraMap F K) = φ := by
  apply isogeny_descends_of_commutes_frobenius W₁ W₂ φ
  apply Isogeny.Hom.ofIsogeny_injective
  rw [← Isogeny.Hom.ofIsogeny_comp_ofIsogeny,
    ← Isogeny.Hom.ofIsogeny_comp_ofIsogeny, h₁, h₂]
  simp only [Isogeny.Hom.comp_zsmul, Isogeny.Hom.zsmul_comp,
    Isogeny.Hom.comp_id, Isogeny.Hom.id_comp]

/-- Ground-field scalar Frobenius identities suffice for unique descent of
every geometric isogeny. This is directly applicable to the negative scalar
Frobenius furnished by maximal supersingular Montgomery curves. -/
theorem isogeny_descends_of_common_scalar_frobenius_ground_hom
    (W₁ W₂ : WeierstrassCurve F) [W₁.IsElliptic] [W₂.IsElliptic]
    (n : ℤ)
    (h₁ : Isogeny.Hom.ofIsogeny (Isogeny.frobeniusIsogeny W₁.toAffine) =
      n • Isogeny.Hom.id W₁.toAffine)
    (h₂ : Isogeny.Hom.ofIsogeny (Isogeny.frobeniusIsogeny W₂.toAffine) =
      n • Isogeny.Hom.id W₂.toAffine)
    (φ : Isogeny (W₁⁄K).toAffine (W₂⁄K).toAffine) :
    ∃! ψ : Isogeny W₁.toAffine W₂.toAffine, ψ.map (algebraMap F K) = φ := by
  apply isogeny_descends_of_common_scalar_frobenius_hom W₁ W₂ n ?_ ?_ φ
  · have he := congrArg (fun h => Isogeny.Hom.map h (algebraMap F K)) h₁
    simp only [Isogeny.Hom.ofIsogeny_map, Isogeny.Hom.map_zsmul,
      Isogeny.Hom.id_map] at he
    exact he
  · have he := congrArg (fun h => Isogeny.Hom.map h (algebraMap F K)) h₂
    simp only [Isogeny.Hom.ofIsogeny_map, Isogeny.Hom.map_zsmul,
      Isogeny.Hom.id_map] at he
    exact he

end
end IsogenyAttack
