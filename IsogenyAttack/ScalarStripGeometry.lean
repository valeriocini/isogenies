import IsogenyAttack.ActualKernelSampler
import IsogenyAttack.VeluQuotient
import IsogenyAttack.ScalarQuotient
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.Surjective

/-!
# Scalar stripping preserves the actual quotient curve

The point subgroup used by the sampler is connected here to the geometric
kernel of the actual scalar-factor isogeny.  In particular, preservation of the
quotient j-invariant is a conclusion, not an assumption on a target map.
-/
namespace IsogenyAttack

open WeierstrassCurve WeierstrassCurve.Affine TauCeti

noncomputable section
open scoped Classical

variable {K : Type*} [Field K] [IsAlgClosed K]
    {W : Affine K} [W.IsElliptic]

private theorem scalar_toPointHom (m : ℕ) (hm : (m : ℤ) ≠ 0)
    (hc : (m : K) ≠ 0) (P : W.Point) :
    (Isogeny.mulByIntIsogenyOfNeZero W hm).toPointHom P = m • P := by
  let := ScalarQuotient.scalar_separable (W := W) hm (by exact_mod_cast hc)
  rw [← Isogeny.Hom.pointMap_ofIsogeny_eq_toPointHom]
  simp only [Isogeny.mulByIntIsogenyOfNeZero, Isogeny.ofIsogeny_mulByIntIsogeny,
    natCast_zsmul, Isogeny.Hom.nsmul_pointMap, Isogeny.Hom.id_pointMap]

instance scalarImage_finite (S : AddSubgroup W.Point) [Finite S] (m : ℕ) :
    Finite (S.map (nsmulAddMonoidHom m)) := by
  apply Finite.of_surjective
    (fun P : S => (⟨m • P.val, ⟨P.val, P.property, rfl⟩⟩ : S.map (nsmulAddMonoidHom m)))
  rintro ⟨Q, P, hP, rfl⟩
  exact ⟨⟨P, hP⟩, rfl⟩

/-- If a finite actual subgroup contains the full m-torsion, its quotient and
the quotient by its scalar image have the same j-invariant. -/
theorem quotientCurve_j_eq_scalar_image (S : AddSubgroup W.Point) [Finite S]
    {m : ℕ} (hm : 0 < m) (hc : (m : K) ≠ 0)
    (ht : AddSubgroup.torsionBy W.Point m ≤ S) :
    (quotientCurve W S).j = (quotientCurve W (S.map (nsmulAddMonoidHom m))).j := by
  have hmz : (m : ℤ) ≠ 0 := by exact_mod_cast hm.ne'
  let μ := Isogeny.mulByIntIsogenyOfNeZero W hmz
  let φ := quotientIsogeny W S
  let : Algebra.IsSeparable μ.fieldPullback.fieldRange W.FunctionField :=
    ScalarQuotient.scalar_separable hmz (by exact_mod_cast hc)
  have hμ : μ.toPointHom.ker = AddSubgroup.torsionBy W.Point m := by
    ext P
    change μ.toPointHom P = 0 ↔ (m : ℤ) • P = 0
    rw [scalar_toPointHom m hmz hc, natCast_zsmul]
  have hle : μ.ker ≤ φ.ker := by
    rw [Isogeny.ker_eq_map_ker_toPointHom, Isogeny.ker_eq_map_ker_toPointHom,
      hμ, quotientIsogeny_point_kernel]
    exact AddSubgroup.map_mono ht
  obtain ⟨χ, hχ, _⟩ := ScalarQuotient.exists_scalar_component φ hmz
    (by exact_mod_cast hc) hle
  have hsep : Algebra.IsSeparable (χ.comp μ).fieldPullback.fieldRange W.FunctionField :=
    hχ ▸ inferInstance
  let : Algebra.IsSeparable χ.fieldPullback.fieldRange W.FunctionField :=
    (Isogeny.isSeparable_comp_iff χ μ).mp hsep |>.1
  have hpoint (P : W.Point) : χ.toPointHom (m • P) = φ.toPointHom P := by
    rw [← scalar_toPointHom m hmz hc P]
    rw [← Isogeny.Hom.pointMap_ofIsogeny_eq_toPointHom,
      ← Isogeny.Hom.pointMap_ofIsogeny_eq_toPointHom,
      ← Isogeny.Hom.comp_pointMap, Isogeny.Hom.ofIsogeny_comp_ofIsogeny,
      hχ, Isogeny.Hom.pointMap_ofIsogeny_eq_toPointHom]
  have hker : χ.toPointHom.ker = S.map (nsmulAddMonoidHom m) := by
    ext Q
    constructor
    · intro hQ
      obtain ⟨P, hP⟩ := W.nsmul_surjective hc Q
      change m • P = Q at hP
      refine ⟨P, ?_, hP⟩
      change P ∈ S
      rw [← quotientIsogeny_point_kernel W S]
      change φ.toPointHom P = 0
      rw [← hpoint, hP]
      exact hQ
    · rintro ⟨P, hP, rfl⟩
      change P ∈ S at hP
      change χ.toPointHom (m • P) = 0
      rw [hpoint]
      exact (show P ∈ φ.toPointHom.ker by
        simpa only [φ, quotientIsogeny_point_kernel] using hP)
  have hgeom : χ.ker = quotientKernel W (S.map (nsmulAddMonoidHom m)) := by
    rw [Isogeny.ker_eq_map_ker_toPointHom, hker]
  exact ScalarQuotient.codomain_j_eq_of_ker_eq χ
    (quotientIsogeny W (S.map (nsmulAddMonoidHom m)))
    χ.card_ker_eq_degree (Isogeny.card_ker_eq_degree _)
    (hgeom.trans (quotientIsogeny_kernel W _).symm)

variable [NeZero (2 : K)]

/-- Actual bounded kernels are finite, since their recorded degree is positive. -/
instance actualKernel_finite {B : ℕ} (S : ActualKernel W.Point B) : Finite S.2.val := by
  apply Nat.finite_of_card_ne_zero
  rw [S.2.property]
  exact Nat.ne_of_gt (Finset.mem_Icc.mp S.1.property).1

instance actualStrip_finite (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0)
    (B : ℕ) (hdeg : ValidDegrees K B) (S : ActualKernel W.Point B) :
    Finite (actualStrip ha₁ ha₃ B hdeg S) := by
  unfold actualStrip
  infer_instance

/-- The HNF content used by the sampler is contained as full actual torsion. -/
theorem actualStrip_full_torsion (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0)
    (B : ℕ) (hdeg : ValidDegrees K B) (S : ActualKernel W.Point B) :
    AddSubgroup.torsionBy W.Point
      (actualKernelEquiv ha₁ ha₃ B hdeg S).val.content ≤ S.2.val := by
  let h := (actualKernelEquiv ha₁ ha₃ B hdeg S).val
  have hd : h.content ∣ S.1.val := by
    rw [← actualKernelEquiv_degree ha₁ ha₃ B hdeg S]
    exact h.content_dvd_a.trans (Nat.dvd_mul_right _ _)
  exact (elliptic_kernel_code_spec ha₁ ha₃
    (hdeg S.1.val (Finset.mem_Icc.mp S.1.property).1
      (Finset.mem_Icc.mp S.1.property).2) S.2.val S.2.property).2.2
        h.content h.content_pos hd |>.mpr (dvd_refl _)

/-- The concrete scalar stripping performed by the sampler preserves the
geometric quotient j-invariant. -/
theorem actualStrip_quotient_j_eq (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0)
    (B : ℕ) (hdeg : ValidDegrees K B) (S : ActualKernel W.Point B) :
    (quotientCurve W S.2.val).j =
      (quotientCurve W (actualStrip ha₁ ha₃ B hdeg S)).j := by
  let h := (actualKernelEquiv ha₁ ha₃ B hdeg S).val
  apply quotientCurve_j_eq_scalar_image S.2.val h.content_pos
  · apply hdeg h.content h.content_pos
    have hd : h.content ∣ h.degree :=
      h.content_dvd_a.trans (Nat.dvd_mul_right _ _)
    exact (Nat.le_of_dvd h.degree_pos hd).trans
      (actualKernelEquiv ha₁ ha₃ B hdeg S).property
  · exact actualStrip_full_torsion ha₁ ha₃ B hdeg S

end
end IsogenyAttack
