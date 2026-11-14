import IsogenyAttack.ScalarStripGeometry

/-!
# The actual cyclic component of a raw isogeny

Factorization is performed on the raw algebraic map and retains its specified
codomain. The residual kernel is the concrete scalar image used by the sampler.
-/
namespace IsogenyAttack

open WeierstrassCurve WeierstrassCurve.Affine TauCeti

noncomputable section
open scoped Classical

variable {K : Type*} [Field K] [IsAlgClosed K]
    {W V : Affine K} [W.IsElliptic] [V.IsElliptic]

/-- Translate a geometric kernel equality into the actual point-group kernel. -/
theorem point_kernel_eq_of_geometric_kernel_eq
    (φ : Isogeny W V)
    [Algebra.IsSeparable φ.fieldPullback.fieldRange W.FunctionField]
    (S : AddSubgroup W.Point) (hker : φ.ker = quotientKernel W S) :
    φ.toPointHom.ker = S := by
  apply AddSubgroup.map_injective
    (f := (Point.equivBaseChangeSelf W).toAddMonoidHom)
    (Point.equivBaseChangeSelf W).injective
  rw [← Isogeny.ker_eq_map_ker_toPointHom]
  exact hker

private theorem scalar_point_apply (m : ℕ) (hm : (m : ℤ) ≠ 0)
    (hc : (m : K) ≠ 0) (P : W.Point) :
    (Isogeny.mulByIntIsogenyOfNeZero W hm).toPointHom P = m • P := by
  let := ScalarQuotient.scalar_separable (W := W) hm (by exact_mod_cast hc)
  rw [← Isogeny.Hom.pointMap_ofIsogeny_eq_toPointHom]
  simp only [Isogeny.mulByIntIsogenyOfNeZero, Isogeny.ofIsogeny_mulByIntIsogeny,
    natCast_zsmul, Isogeny.Hom.nsmul_pointMap, Isogeny.Hom.id_pointMap]

/-- Stripping full scalar torsion from any actual separable isogeny produces
an actual separable isogeny to exactly the same codomain. -/
theorem exists_scalar_component_point_kernel (φ : Isogeny W V)
    [Algebra.IsSeparable φ.fieldPullback.fieldRange W.FunctionField]
    (S : AddSubgroup W.Point) (hker : φ.toPointHom.ker = S)
    (m : ℕ) (hm : 0 < m) (hc : (m : K) ≠ 0)
    (ht : AddSubgroup.torsionBy W.Point m ≤ S) :
    ∃ χ : Isogeny W V,
      χ.comp (Isogeny.mulByIntIsogenyOfNeZero W
        (show (m : ℤ) ≠ 0 by exact_mod_cast hm.ne')) = φ ∧
      χ.degree * m ^ 2 = φ.degree ∧
      χ.toPointHom.ker = S.map (nsmulAddMonoidHom m) ∧
      Algebra.IsSeparable χ.fieldPullback.fieldRange W.FunctionField := by
  have hmz : (m : ℤ) ≠ 0 := by exact_mod_cast hm.ne'
  let μ := Isogeny.mulByIntIsogenyOfNeZero W hmz
  let : Algebra.IsSeparable μ.fieldPullback.fieldRange W.FunctionField :=
    ScalarQuotient.scalar_separable hmz (by exact_mod_cast hc)
  have hμ : μ.toPointHom.ker = AddSubgroup.torsionBy W.Point m := by
    ext P
    change μ.toPointHom P = 0 ↔ (m : ℤ) • P = 0
    rw [scalar_point_apply m hmz hc, natCast_zsmul]
  have hle : μ.ker ≤ φ.ker := by
    rw [Isogeny.ker_eq_map_ker_toPointHom, Isogeny.ker_eq_map_ker_toPointHom, hμ, hker]
    exact AddSubgroup.map_mono ht
  obtain ⟨χ, hχ, hdeg⟩ := ScalarQuotient.exists_scalar_component φ hmz
    (by exact_mod_cast hc) hle
  have hsep : Algebra.IsSeparable (χ.comp μ).fieldPullback.fieldRange W.FunctionField :=
    hχ ▸ inferInstance
  let : Algebra.IsSeparable χ.fieldPullback.fieldRange W.FunctionField :=
    (Isogeny.isSeparable_comp_iff χ μ).mp hsep |>.1
  have hpoint (P : W.Point) : χ.toPointHom (m • P) = φ.toPointHom P := by
    rw [← scalar_point_apply m hmz hc P]
    rw [← Isogeny.Hom.pointMap_ofIsogeny_eq_toPointHom,
      ← Isogeny.Hom.pointMap_ofIsogeny_eq_toPointHom,
      ← Isogeny.Hom.comp_pointMap, Isogeny.Hom.ofIsogeny_comp_ofIsogeny,
      hχ, Isogeny.Hom.pointMap_ofIsogeny_eq_toPointHom]
  refine ⟨χ, hχ, ?_, ?_, inferInstance⟩
  · simpa only [Int.natAbs_natCast] using hdeg
  · ext Q
    constructor
    · intro hQ
      obtain ⟨P, hP⟩ := W.nsmul_surjective hc Q
      change m • P = Q at hP
      refine ⟨P, ?_, hP⟩
      change P ∈ S
      rw [← hker]
      change φ.toPointHom P = 0
      rw [← hpoint, hP]
      exact hQ
    · rintro ⟨P, hP, rfl⟩
      change P ∈ S at hP
      change χ.toPointHom (m • P) = 0
      rw [hpoint]
      exact (show P ∈ φ.toPointHom.ker by rwa [hker])

variable [NeZero (2 : K)]

/-- Complete specification of the cyclic component of a raw bounded isogeny. -/
theorem exists_actual_cyclic_component (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0)
    (B : ℕ) (hdeg : ValidDegrees K B) (S : ActualKernel W.Point B)
    (φ : Isogeny W V)
    [Algebra.IsSeparable φ.fieldPullback.fieldRange W.FunctionField]
    (hker : φ.toPointHom.ker = S.2.val) :
    ∃ χ : Isogeny W V,
      χ.comp (Isogeny.mulByIntIsogenyOfNeZero W
        (show ((actualKernelEquiv ha₁ ha₃ B hdeg S).val.content : ℤ) ≠ 0 by
          exact_mod_cast (actualKernelEquiv ha₁ ha₃ B hdeg S).val.content_pos.ne')) = φ ∧
      χ.degree = Nat.card (actualStrip ha₁ ha₃ B hdeg S) ∧
      χ.degree = (actualKernelEquiv ha₁ ha₃ B hdeg S).val.cyclicDegree ∧
      χ.toPointHom.ker = actualStrip ha₁ ha₃ B hdeg S ∧
      IsAddCyclic χ.toPointHom.ker ∧
      Algebra.IsSeparable χ.fieldPullback.fieldRange W.FunctionField := by
  let h := (actualKernelEquiv ha₁ ha₃ B hdeg S).val
  have hc : (h.content : K) ≠ 0 := by
    apply hdeg h.content h.content_pos
    exact (Nat.le_of_dvd h.degree_pos
      (h.content_dvd_a.trans (Nat.dvd_mul_right _ _))).trans
      (actualKernelEquiv ha₁ ha₃ B hdeg S).property
  obtain ⟨χ, hχ, _, hk, hsep⟩ := exists_scalar_component_point_kernel φ S.2.val hker
    h.content h.content_pos hc (actualStrip_full_torsion ha₁ ha₃ B hdeg S)
  let := hsep
  have hcard : χ.degree = Nat.card (actualStrip ha₁ ha₃ B hdeg S) := by
    rw [← Isogeny.card_ker_toPointHom_eq_degree χ, hk]
    rfl
  refine ⟨χ, hχ, hcard, ?_, hk, ?_, hsep⟩
  · exact hcard.trans (actualStrip_card ha₁ ha₃ B hdeg S)
  · rw [hk]
    exact actualStrip_cyclic ha₁ ha₃ B hdeg S

/-- The actual cyclic component, with the original raw codomain retained. -/
def actualCyclicComponent (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0)
    (B : ℕ) (hdeg : ValidDegrees K B) (S : ActualKernel W.Point B)
    (φ : Isogeny W V)
    [Algebra.IsSeparable φ.fieldPullback.fieldRange W.FunctionField]
    (hker : φ.toPointHom.ker = S.2.val) : Isogeny W V :=
  Classical.choose (exists_actual_cyclic_component ha₁ ha₃ B hdeg S φ hker)

/-- Factorization, exact degree, actual kernel, cyclicity, and separability of
the chosen actual cyclic component. -/
theorem actualCyclicComponent_spec (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0)
    (B : ℕ) (hdeg : ValidDegrees K B) (S : ActualKernel W.Point B)
    (φ : Isogeny W V)
    [Algebra.IsSeparable φ.fieldPullback.fieldRange W.FunctionField]
    (hker : φ.toPointHom.ker = S.2.val) :
    let χ := actualCyclicComponent ha₁ ha₃ B hdeg S φ hker
    χ.comp (Isogeny.mulByIntIsogenyOfNeZero W
      (show ((actualKernelEquiv ha₁ ha₃ B hdeg S).val.content : ℤ) ≠ 0 by
        exact_mod_cast (actualKernelEquiv ha₁ ha₃ B hdeg S).val.content_pos.ne')) = φ ∧
    χ.degree = Nat.card (actualStrip ha₁ ha₃ B hdeg S) ∧
    χ.degree = (actualKernelEquiv ha₁ ha₃ B hdeg S).val.cyclicDegree ∧
    χ.toPointHom.ker = actualStrip ha₁ ha₃ B hdeg S ∧
    IsAddCyclic χ.toPointHom.ker ∧
    Algebra.IsSeparable χ.fieldPullback.fieldRange W.FunctionField :=
  Classical.choose_spec (exists_actual_cyclic_component ha₁ ha₃ B hdeg S φ hker)

@[simp]
theorem actualCyclicComponent_degree (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0)
    (B : ℕ) (hdeg : ValidDegrees K B) (S : ActualKernel W.Point B)
    (φ : Isogeny W V)
    [Algebra.IsSeparable φ.fieldPullback.fieldRange W.FunctionField]
    (hker : φ.toPointHom.ker = S.2.val) :
    (actualCyclicComponent ha₁ ha₃ B hdeg S φ hker).degree =
      (actualKernelEquiv ha₁ ha₃ B hdeg S).val.cyclicDegree :=
  (actualCyclicComponent_spec ha₁ ha₃ B hdeg S φ hker).2.2.1

@[simp]
theorem actualCyclicComponent_point_kernel (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0)
    (B : ℕ) (hdeg : ValidDegrees K B) (S : ActualKernel W.Point B)
    (φ : Isogeny W V)
    [Algebra.IsSeparable φ.fieldPullback.fieldRange W.FunctionField]
    (hker : φ.toPointHom.ker = S.2.val) :
    (actualCyclicComponent ha₁ ha₃ B hdeg S φ hker).toPointHom.ker =
      actualStrip ha₁ ha₃ B hdeg S :=
  (actualCyclicComponent_spec ha₁ ha₃ B hdeg S φ hker).2.2.2.1

instance actualCyclicComponent_separable (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0)
    (B : ℕ) (hdeg : ValidDegrees K B) (S : ActualKernel W.Point B)
    (φ : Isogeny W V)
    [Algebra.IsSeparable φ.fieldPullback.fieldRange W.FunctionField]
    (hker : φ.toPointHom.ker = S.2.val) :
    Algebra.IsSeparable
      (actualCyclicComponent ha₁ ha₃ B hdeg S φ hker).fieldPullback.fieldRange
        W.FunctionField :=
  (actualCyclicComponent_spec ha₁ ha₃ B hdeg S φ hker).2.2.2.2.2

end
end IsogenyAttack
