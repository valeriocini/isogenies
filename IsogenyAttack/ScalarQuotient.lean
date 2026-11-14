import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Velu.Exhaustive
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.Separability

/-! Actual algebraic isogenies, their quotient codomains and scalar stripping.
These results concern TauCeti's function-field-defined isogenies, not abstract
point-group homomorphisms. -/
namespace IsogenyAttack.ScalarQuotient
open TauCeti WeierstrassCurve WeierstrassCurve.Affine
variable {F : Type*} [Field F] [DecidableEq F]
variable {W V U : Affine F} [W.IsElliptic] [V.IsElliptic] [U.IsElliptic]

/-- Equal full geometric kernels force equal codomain j-invariants. The cardinal
hypotheses are automatically satisfied by separable isogenies over separably
closed fields. -/
theorem codomain_j_eq_of_ker_eq (φ : Isogeny W V) (ψ : Isogeny W U)
    (hφ : Nat.card φ.ker = φ.degree) (hψ : Nat.card ψ.ker = ψ.degree)
    (hker : φ.ker = ψ.ker) : V.j = U.j := by
  obtain ⟨C, ⟨hC, _⟩, _⟩ :=
    Isogeny.existsUnique_variableChangeIsogeny_comp_eq_of_ker_eq hφ hψ hker
  have hj : (C • V).j = V.j := variableChange_j V C
  simpa only [hC] using hj.symm

/-- A separable isogeny's actual target has the j-invariant of the constructed
Vélu quotient by its actual kernel. -/
theorem quotient_j_eq_codomain [IsSepClosed F] (φ : Isogeny W V)
    [Algebra.IsSeparable φ.fieldPullback.fieldRange W.FunctionField] :
    (veluCurve W φ.ker).j = V.j := by
  apply codomain_j_eq_of_ker_eq (veluIsogeny W φ.ker) φ
  · simp
  · exact φ.card_ker_eq_degree
  · exact ker_veluIsogeny W φ.ker

omit [DecidableEq F] in
/-- Actual multiplication is separable when its scalar does not vanish in F. -/
lemma scalar_separable {m : ℤ} (hm : m ≠ 0) (hchar : (m : F) ≠ 0) :
    Algebra.IsSeparable (Isogeny.mulByIntIsogenyOfNeZero W hm).fieldPullback.fieldRange
      W.FunctionField :=
  (Isogeny.isSeparable_mulByIntIsogeny_iff W _).mpr hchar

omit [V.IsElliptic] in
/-- Strip a scalar factor from an actual isogeny. The remaining isogeny has
exactly the same target curve, and its degree is divided by the square scalar.
The only factorization condition is the actual inclusion of geometric kernels. -/
theorem exists_scalar_component [IsSepClosed F] (φ : Isogeny W V) {m : ℤ}
    (hm : m ≠ 0) (hchar : (m : F) ≠ 0)
    (hle : (Isogeny.mulByIntIsogenyOfNeZero W hm).ker ≤ φ.ker) :
    ∃ χ : Isogeny W V,
      χ.comp (Isogeny.mulByIntIsogenyOfNeZero W hm) = φ ∧
        χ.degree * m.natAbs ^ 2 = φ.degree := by
  let := scalar_separable (W := W) hm hchar
  obtain ⟨χ, hχ, _⟩ := (Isogeny.existsUnique_comp_eq_iff_ker_le
    (Isogeny.mulByIntIsogenyOfNeZero W hm).card_ker_eq_degree φ).mpr hle
  refine ⟨χ, hχ, ?_⟩
  rw [← Isogeny.degree_mulByIntIsogenyOfNeZero W hm, ← Isogeny.degree_comp, hχ]

/-- Scalar stripping preserves the target j-class even after both original and
remaining maps are replaced by the canonical Vélu quotients of their kernels. -/
theorem exists_scalar_component_same_j [IsSepClosed F] (φ : Isogeny W V)
    [Algebra.IsSeparable φ.fieldPullback.fieldRange W.FunctionField] {m : ℤ}
    (hm : m ≠ 0) (hchar : (m : F) ≠ 0)
    (hle : (Isogeny.mulByIntIsogenyOfNeZero W hm).ker ≤ φ.ker) :
    ∃ χ : Isogeny W V,
      χ.comp (Isogeny.mulByIntIsogenyOfNeZero W hm) = φ ∧
        χ.degree * m.natAbs ^ 2 = φ.degree ∧
          (veluCurve W χ.ker).j = (veluCurve W φ.ker).j := by
  obtain ⟨χ, hχ, hdeg⟩ := exists_scalar_component φ hm hchar hle
  have : Algebra.IsSeparable χ.fieldPullback.fieldRange W.FunctionField := by
    have hsep : Algebra.IsSeparable
        (χ.comp (Isogeny.mulByIntIsogenyOfNeZero W hm)).fieldPullback.fieldRange
        W.FunctionField := hχ ▸ inferInstance
    exact (Isogeny.isSeparable_comp_iff χ _).mp hsep |>.1
  exact ⟨χ, hχ, hdeg, (quotient_j_eq_codomain χ).trans (quotient_j_eq_codomain φ).symm⟩

end IsogenyAttack.ScalarQuotient
