import IsogenyAttack.VeluQuotient
import IsogenyAttack.GeometricMultiplicity
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Velu.Exhaustive

/-!
The morphism sampler, with genuine isogenies as its outcomes.  Unique Vélu
factorisation identifies a prescribed-kernel isogeny with a coordinate
isomorphism of the quotient.  Consequently the twelve geometric Montgomery
realizations give twelve distinct morphisms per kernel, not merely twelve
formal decorations of a kernel.
-/
namespace IsogenyAttack.IsogenySampler

open WeierstrassCurve WeierstrassCurve.Affine TauCeti
open CurveAutomorphisms GeometricMultiplicity Montgomery

noncomputable section
open scoped Classical

variable {K : Type*} [Field K] [DecidableEq K]
variable (W : Affine K) [W.IsElliptic]

/-- Genuine separable maps with this kernel, expressed by the kernel-degree
equality. Over a separably closed field this equality is equivalent to
separability; below we prove both directions. -/
abbrev FixedKernelMaps (V : WeierstrassCurve K) (S : AddSubgroup W.Point) :=
  {φ : Isogeny W V.toAffine // φ.ker = quotientKernel W S ∧
    Nat.card φ.ker = φ.degree}

theorem ker_variableChange_comp {U V : Affine K} [U.IsElliptic]
    (φ : Isogeny W U) (C : VariableChange K) (hC : C • U = V) :
    ((Isogeny.variableChangeIsogeny C hC).comp φ).ker = φ.ker := by
  apply le_antisymm
  · have hInv : C⁻¹ • V = U := by rw [← hC, inv_smul_smul]
    have h := Isogeny.ker_le_ker_comp
      (Isogeny.variableChangeIsogeny C⁻¹ hInv)
      ((Isogeny.variableChangeIsogeny C hC).comp φ)
    rwa [← Isogeny.comp_assoc, Isogeny.variableChangeIsogeny_inv_comp,
      Isogeny.id_comp] at h
  · exact Isogeny.ker_le_ker_comp _ _

/-- Postcomposing the actual Vélu quotient by an actual coordinate change. -/
def realizeMap (V : WeierstrassCurve K) (S : AddSubgroup W.Point) [Finite S]
    (C : CoordinateIso (quotientCurve W S) V) : FixedKernelMaps W V S :=
  ⟨(Isogeny.variableChangeIsogeny C.val C.property).comp (quotientIsogeny W S), by
    rw [ker_variableChange_comp, quotientIsogeny_kernel]
    refine ⟨rfl, ?_⟩
    rw [Isogeny.degree_comp, Isogeny.degree_variableChangeIsogeny, one_mul,
      quotientIsogeny_degree]
    exact (Nat.card_congr ((Point.equivBaseChangeSelf W).addSubgroupMap S).toEquiv).symm⟩

/-- The coordinate factor is unique; every map with this kernel and separable
degree is obtained. This is a theorem about actual algebraic maps. -/
def coordinateIsoEquivFixedKernelMaps (V : WeierstrassCurve K) [V.IsElliptic]
    (S : AddSubgroup W.Point) [Finite S] :
    CoordinateIso (quotientCurve W S) V ≃ FixedKernelMaps W V S :=
  Equiv.ofBijective (realizeMap W V S) (by
    constructor
    · intro C D h
      apply Subtype.ext
      apply (Isogeny.variableChangeIsogeny_inj C.val D.val C.property D.property).mp
      exact (quotientIsogeny W S).comp_right_injective (congrArg Subtype.val h)
    · intro φ
      obtain ⟨C, ⟨hC, hφ⟩, -⟩ :=
        Isogeny.existsUnique_variableChangeIsogeny_comp_eq_of_ker_eq
          (φ := quotientIsogeny W S) (ψ := φ.val)
          (by simp only [quotientIsogeny, degree_veluIsogeny, ker_veluIsogeny])
          φ.property.2 ((quotientIsogeny_kernel W S).trans φ.property.1.symm)
      exact ⟨⟨C, hC⟩, Subtype.ext hφ⟩)

theorem fixedKernelMaps_degree (V : WeierstrassCurve K) (S : AddSubgroup W.Point)
    (φ : FixedKernelMaps W V S) : φ.val.degree = Nat.card S := by
  rw [← φ.property.2, φ.property.1]
  exact (Nat.card_congr ((Point.equivBaseChangeSelf W).addSubgroupMap S).toEquiv).symm

/-- The target of the raw morphism has the actual quotient's j-invariant. -/
theorem fixedKernelMaps_target_j (V : WeierstrassCurve K) [V.IsElliptic]
    (S : AddSubgroup W.Point) [Finite S] (φ : FixedKernelMaps W V S) :
    (quotientCurve W S).j = V.j := by
  let C := (coordinateIsoEquivFixedKernelMaps W V S).symm φ
  have h := variableChange_j (quotientCurve W S) C.val
  simpa only [C.property] using h.symm

theorem isSeparable_of_card_ker_eq_degree {V : Affine K} (φ : Isogeny W V)
    (hφ : Nat.card φ.ker = φ.degree) :
    Algebra.IsSeparable φ.fieldPullback.fieldRange W.FunctionField := by
  apply (φ.separableDegree_eq_degree_iff_isSeparable).mp
  apply le_antisymm
  · rw [Isogeny.separableDegree_def, Isogeny.degree_def]
    exact Field.finSepDegree_le_finrank _ _
  · rw [← hφ]
    exact φ.card_ker_le_separableDegree

theorem card_ker_eq_degree_iff_separable [IsSepClosed K]
    {V : Affine K} [V.IsElliptic] (φ : Isogeny W V) :
    Nat.card φ.ker = φ.degree ↔
      Algebra.IsSeparable φ.fieldPullback.fieldRange W.FunctionField := by
  constructor
  · exact isSeparable_of_card_ker_eq_degree W φ
  · intro h
    letI := h
    exact φ.card_ker_eq_degree

/-- All nonsingular Montgomery targets, with their coefficients retained. -/
abbrev MontgomeryParameter := {A : K // A ^ 2 ≠ 4}

/-- All genuine isogenies to Montgomery equations with the prescribed kernel.
No condition on the target j-invariant is imposed in this definition. -/
abbrev MontgomeryMapsWithKernel (S : AddSubgroup W.Point) :=
  Σ A : MontgomeryParameter (K := K), FixedKernelMaps W (curve A.val) S

variable [IsAlgClosed K]

/-- Removing the redundant target-j condition from a geometric realization.
The condition follows from the actual coordinate isomorphism. -/
def realizationEquivAllMontgomeryCoordinates (Q : WeierstrassCurve K) [Q.IsElliptic]
    (h2 : (2 : K) ≠ 0) :
    Realization Q ≃ (Σ A : MontgomeryParameter (K := K), CoordinateIso Q (curve A.val)) :=
  Equiv.ofBijective
    (fun r => ⟨⟨r.1.val, (modelFiber_property Q.j h2 r.1).1⟩, r.2⟩) (by
      constructor
      · rintro ⟨a, C⟩ ⟨b, D⟩ h
        have hab : a = b := Subtype.ext (congrArg (fun x => x.1.val) h)
        cases hab
        have hCD : C = D := by simpa only [Sigma.mk.injEq, heq_eq_eq, true_and] using h
        cases hCD
        rfl
      · rintro ⟨A, C⟩
        letI := curve_isElliptic h2 A.property
        have hj : jInvariant A.val = Q.j := by
          rw [← curve_jInvariant]
          simpa only [C.property] using variableChange_j Q C.val
        have hm : A.val ∈ (fiberPolynomial Q.j).roots.toFinset := by
          apply Multiset.mem_toFinset.mpr
          apply (Polynomial.mem_roots (fiberPolynomial_ne_zero Q.j
            (two_pow_eight_ne_zero h2))).mpr
          exact (fiberPolynomial_isRoot_iff (two_pow_eight_ne_zero h2)).mpr ⟨A.property, hj⟩
        exact ⟨⟨⟨A.val, hm⟩, C⟩, rfl⟩)

/-- Every raw morphism, not just a selected representative, occurs exactly
once among the actual coordinate realizations of the Vélu quotient. -/
def realizationEquivMontgomeryMaps (S : AddSubgroup W.Point) [Finite S]
    (h2 : (2 : K) ≠ 0) :
    Realization (quotientCurve W S) ≃ MontgomeryMapsWithKernel W S :=
  (realizationEquivAllMontgomeryCoordinates (quotientCurve W S) h2).trans
    (Equiv.sigmaCongrRight (fun A => by
      letI := curve_isElliptic h2 A.property
      exact coordinateIsoEquivFixedKernelMaps W (curve A.val) S))

/-- Exact multiplicity of genuine separable isogenies with any fixed kernel,
including the exceptional j-invariants 0 and 1728. -/
theorem card_montgomeryMapsWithKernel (S : AddSubgroup W.Point) [Finite S]
    (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) :
    Nat.card (MontgomeryMapsWithKernel W S) = 12 := by
  rw [← Nat.card_congr (realizationEquivMontgomeryMaps W S h2)]
  exact card_realization (quotientCurve W S) h2 h3

lemma montgomeryMapsWithKernel_finite (S : AddSubgroup W.Point) [Finite S]
    (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) :
    Finite (MontgomeryMapsWithKernel W S) :=
  Nat.finite_of_card_ne_zero (by rw [card_montgomeryMapsWithKernel W S h2 h3]; norm_num)

lemma montgomeryMapsWithKernel_nonempty (S : AddSubgroup W.Point) [Finite S]
    (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) :
    Nonempty (MontgomeryMapsWithKernel W S) :=
  (Nat.card_ne_zero.mp (by rw [card_montgomeryMapsWithKernel W S h2 h3]; norm_num)).1

/-- Transport the actual function-field kernel back to the original point
group. The transport is only the canonical identity base-change equivalence. -/
def pointKernel {V : Affine K} (φ : Isogeny W V) : AddSubgroup W.Point :=
  φ.ker.map (Point.equivBaseChangeSelf W).symm.toAddMonoidHom

theorem quotientKernel_pointKernel {V : Affine K} (φ : Isogeny W V) :
    quotientKernel W (pointKernel W φ) = φ.ker := by
  ext P
  constructor
  · rintro ⟨x, ⟨y, hy, rfl⟩, rfl⟩
    simpa using hy
  · intro hp
    exact ⟨(Point.equivBaseChangeSelf W).symm P, ⟨P, hp, rfl⟩,
      (Point.equivBaseChangeSelf W).apply_symm_apply P⟩

theorem pointKernel_card {V : Affine K} (φ : Isogeny W V) :
    Nat.card (pointKernel W φ) = Nat.card φ.ker :=
  (Nat.card_congr ((Point.equivBaseChangeSelf W).symm.addSubgroupMap φ.ker).toEquiv).symm

theorem pointKernel_eq_of_ker_eq {V : Affine K} (φ : Isogeny W V)
    (S : AddSubgroup W.Point) (h : φ.ker = quotientKernel W S) :
    pointKernel W φ = S := by
  apply AddSubgroup.map_injective
    (f := (Point.equivBaseChangeSelf W).toAddMonoidHom)
    (Point.equivBaseChangeSelf W).injective
  exact (quotientKernel_pointKernel W φ).trans h

theorem pointKernel_eq_toPointHom_ker {V : Affine K} [V.IsElliptic]
    (φ : Isogeny W V)
    [Algebra.IsSeparable φ.fieldPullback.fieldRange W.FunctionField] :
    pointKernel W φ = φ.toPointHom.ker :=
  pointKernel_eq_of_ker_eq W φ _ φ.ker_eq_map_ker_toPointHom

/-- The unadorned outcome of the degree-d sampler: a target coefficient and a
genuine separable isogeny of degree d. Kernels are not part of its data. -/
abbrev DegreeMaps (d : ℕ) :=
  Σ A : MontgomeryParameter (K := K),
    {φ : Isogeny W (curve A.val).toAffine //
      φ.degree = d ∧ Nat.card φ.ker = φ.degree}

abbrev DegreeKernel (d : ℕ) := {S : AddSubgroup W.Point // Nat.card S = d}

instance degreeKernel_subgroup_finite {d : ℕ} [NeZero d] (S : DegreeKernel W d) :
    Finite S.val := Nat.finite_of_card_ne_zero (by rw [S.property]; exact NeZero.ne d)

/-- The actual kernel extracted from a raw morphism. -/
def degreeMapKernel {d : ℕ} (φ : DegreeMaps W d) : DegreeKernel W d :=
  ⟨pointKernel W φ.2.val,
    (pointKernel_card W φ.2.val).trans (φ.2.property.2.trans φ.2.property.1)⟩

/-- Classification of every degree-d morphism by its actual subgroup kernel.
Both inverse identities follow from the genuine kernel equation. -/
def degreeMapsEquivKernelMaps (d : ℕ) :
    DegreeMaps W d ≃ (Σ S : DegreeKernel W d, MontgomeryMapsWithKernel W S.val) where
  toFun φ := ⟨degreeMapKernel W φ, φ.1,
    ⟨φ.2.val, (quotientKernel_pointKernel W φ.2.val).symm, φ.2.property.2⟩⟩
  invFun φ := ⟨φ.2.1,
    ⟨φ.2.2.val, (fixedKernelMaps_degree W _ φ.1.val φ.2.2).trans φ.1.property,
      φ.2.2.property.2⟩⟩
  left_inv φ := rfl
  right_inv φ := by
    rcases φ with ⟨⟨S, hS⟩, A, f, hf⟩
    have h : pointKernel W f = S := pointKernel_eq_of_ker_eq W f S hf.1
    subst S
    rfl

/-- Each actual degree-d subgroup has exactly twelve raw morphism preimages. -/
theorem card_degreeMapKernel_fiber (d : ℕ) [NeZero d]
    (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) (S : DegreeKernel W d) :
    Nat.card {φ : DegreeMaps W d // degreeMapKernel W φ = S} = 12 := by
  let e := degreeMapsEquivKernelMaps W d
  let e₁ : {φ : DegreeMaps W d // degreeMapKernel W φ = S} ≃
      {φ : (Σ S : DegreeKernel W d, MontgomeryMapsWithKernel W S.val) // φ.1 = S} :=
    e.subtypeEquiv (fun _ => Iff.rfl)
  rw [Nat.card_congr e₁,
    Nat.card_congr (sigmaFirstFiberEquiv (fun S : DegreeKernel W d =>
      MontgomeryMapsWithKernel W S.val) S)]
  exact card_montgomeryMapsWithKernel W S.val h2 h3

theorem card_degreeMaps (d : ℕ) [NeZero d] [Fintype (DegreeKernel W d)]
    (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) :
    Nat.card (DegreeMaps W d) = Nat.card (DegreeKernel W d) * 12 := by
  letI : ∀ S : DegreeKernel W d, Finite (MontgomeryMapsWithKernel W S.val) :=
    fun S => montgomeryMapsWithKernel_finite W S.val h2 h3
  rw [Nat.card_congr (degreeMapsEquivKernelMaps W d), Nat.card_sigma]
  simp_rw [card_montgomeryMapsWithKernel W _ h2 h3]
  simp [Nat.card_eq_fintype_card]

lemma degreeMaps_finite (d : ℕ) [NeZero d] [Fintype (DegreeKernel W d)]
    (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) : Finite (DegreeMaps W d) := by
  letI : ∀ S : DegreeKernel W d, Finite (MontgomeryMapsWithKernel W S.val) :=
    fun S => montgomeryMapsWithKernel_finite W S.val h2 h3
  exact Finite.of_equiv _ (degreeMapsEquivKernelMaps W d).symm

lemma degreeMaps_nonempty (d : ℕ) [NeZero d] [Nonempty (DegreeKernel W d)]
    (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) : Nonempty (DegreeMaps W d) := by
  obtain ⟨S⟩ := ‹Nonempty (DegreeKernel W d)›
  obtain ⟨φ⟩ := montgomeryMapsWithKernel_nonempty W S.val h2 h3
  exact ⟨(degreeMapsEquivKernelMaps W d).symm ⟨S, φ⟩⟩

/-- Sampling uniformly from all actual degree-d separable morphisms to all
Montgomery equations induces exactly the uniform law on actual order-d
subgroups. This proves the printed morphism/kernel sampler correspondence. -/
theorem uniform_degreeMaps_kernel (d : ℕ) [NeZero d] [Fintype (DegreeKernel W d)]
    [Nonempty (DegreeKernel W d)] (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0)
    (S : DegreeKernel W d) :
    letI : Finite (DegreeMaps W d) := degreeMaps_finite W d h2 h3
    letI : Fintype (DegreeMaps W d) := Fintype.ofFinite _
    letI : Nonempty (DegreeMaps W d) := degreeMaps_nonempty W d h2 h3
    ((FiniteLaw.uniform (DegreeMaps W d)).pushForward (degreeMapKernel W)).mass S =
      (FiniteLaw.uniform (DegreeKernel W d)).mass S := by
  letI : Finite (DegreeMaps W d) := degreeMaps_finite W d h2 h3
  letI : Fintype (DegreeMaps W d) := Fintype.ofFinite _
  letI : Nonempty (DegreeMaps W d) := degreeMaps_nonempty W d h2 h3
  change (FiniteLaw.uniform (DegreeMaps W d)).eventMass
    (fun φ => degreeMapKernel W φ = S) = _
  rw [FiniteLaw.uniform_event]
  simp only [Fintype.card_eq_nat_card]
  rw [card_degreeMapKernel_fiber W d h2 h3 S, card_degreeMaps W d h2 h3]
  simp only [Nat.cast_mul, Nat.cast_ofNat, FiniteLaw.uniform, Fintype.card_eq_nat_card]
  have hc : (Nat.card (DegreeKernel W d) : ℝ) ≠ 0 := by
    rw [Nat.card_eq_fintype_card]
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card (DegreeKernel W d) ≠ 0)
  field_simp

/-- At a fixed target, every connecting kernel has the same actual morphism
multiplicity, including the exceptional automorphism groups. -/
theorem card_fixedKernelMaps (V : WeierstrassCurve K) [V.IsElliptic]
    (S : AddSubgroup W.Point) [Finite S]
    (hj : (quotientCurve W S).j = V.j)
    (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) :
    Nat.card (FixedKernelMaps W V S) =
      if V.j = 0 then 6 else if V.j = 1728 then 4 else 2 := by
  rw [← Nat.card_congr (coordinateIsoEquivFixedKernelMaps W V S),
    card_coordinateIso_by_j (quotientCurve W S) V hj h2 h3, hj]

/-- Raw isogenies to one specified target, restricted to an explicitly given
family of allowed actual kernels. A degree bound can be encoded in that family. -/
abbrev FamilyTargetMaps {ι : Type*} (V : WeierstrassCurve K)
    (S : ι → AddSubgroup W.Point) :=
  {φ : Isogeny W V.toAffine // Nat.card φ.ker = φ.degree ∧
    ∃ i, φ.ker = quotientKernel W (S i)}

/-- Forgetting the indexed kernel is bijective because the genuine morphism
determines its kernel. No selected map or assumed count enters this equivalence. -/
def familyTargetMapsEquiv {ι : Type*} (V : WeierstrassCurve K)
    (S : ι → AddSubgroup W.Point) (hS : Function.Injective S) :
    (Σ i, FixedKernelMaps W V (S i)) ≃ FamilyTargetMaps W V S :=
  Equiv.ofBijective (fun x => ⟨x.2.val, x.2.property.2, x.1, x.2.property.1⟩) (by
    constructor
    · rintro ⟨i, φ⟩ ⟨j, ψ⟩ h
      have hφ : φ.val = ψ.val := congrArg Subtype.val h
      have hij : i = j := by
        apply hS
        apply AddSubgroup.map_injective
          (f := (Point.equivBaseChangeSelf W).toAddMonoidHom)
          (Point.equivBaseChangeSelf W).injective
        exact φ.property.1.symm.trans ((congrArg Isogeny.ker hφ).trans ψ.property.1)
      cases hij
      exact Sigma.ext rfl (heq_of_eq (Subtype.ext hφ))
    · rintro ⟨φ, hφ, i, hi⟩
      exact ⟨⟨i, φ, hi, hφ⟩, rfl⟩)

def familyTargetMapKernel {ι : Type*} (V : WeierstrassCurve K)
    (S : ι → AddSubgroup W.Point) (hS : Function.Injective S)
    (φ : FamilyTargetMaps W V S) : ι :=
  ((familyTargetMapsEquiv W V S hS).symm φ).1

theorem familyTargetMapKernel_spec {ι : Type*} (V : WeierstrassCurve K)
    (S : ι → AddSubgroup W.Point) (hS : Function.Injective S)
    (φ : FamilyTargetMaps W V S) :
    φ.val.ker = quotientKernel W (S (familyTargetMapKernel W V S hS φ)) := by
  have h := ((familyTargetMapsEquiv W V S hS).symm φ).2.property.1
  have hφ := congrArg Subtype.val ((familyTargetMapsEquiv W V S hS).apply_symm_apply φ)
  exact hφ.symm ▸ h

lemma fixedKernelMaps_finite (V : WeierstrassCurve K) [V.IsElliptic]
    (S : AddSubgroup W.Point) [Finite S] (hj : (quotientCurve W S).j = V.j)
    (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) : Finite (FixedKernelMaps W V S) :=
  Nat.finite_of_card_ne_zero (by
    rw [card_fixedKernelMaps W V S hj h2 h3]; split_ifs <;> norm_num)

lemma fixedKernelMaps_nonempty (V : WeierstrassCurve K) [V.IsElliptic]
    (S : AddSubgroup W.Point) [Finite S] (hj : (quotientCurve W S).j = V.j)
    (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) : Nonempty (FixedKernelMaps W V S) :=
  (Nat.card_ne_zero.mp (by
    rw [card_fixedKernelMaps W V S hj h2 h3]; split_ifs <;> norm_num)).1

lemma familyTargetMaps_finite {ι : Type*} [Finite ι]
    (V : WeierstrassCurve K) [V.IsElliptic]
    (S : ι → AddSubgroup W.Point) [∀ i, Finite (S i)]
    (hS : Function.Injective S) (hj : ∀ i, (quotientCurve W (S i)).j = V.j)
    (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) : Finite (FamilyTargetMaps W V S) := by
  letI : ∀ i, Finite (FixedKernelMaps W V (S i)) :=
    fun i => fixedKernelMaps_finite W V (S i) (hj i) h2 h3
  exact Finite.of_equiv _ (familyTargetMapsEquiv W V S hS)

lemma familyTargetMaps_nonempty {ι : Type*} [Nonempty ι]
    (V : WeierstrassCurve K) [V.IsElliptic]
    (S : ι → AddSubgroup W.Point) [∀ i, Finite (S i)]
    (hS : Function.Injective S) (hj : ∀ i, (quotientCurve W (S i)).j = V.j)
    (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) : Nonempty (FamilyTargetMaps W V S) := by
  obtain ⟨i⟩ := ‹Nonempty ι›
  obtain ⟨φ⟩ := fixedKernelMaps_nonempty W V (S i) (hj i) h2 h3
  exact ⟨familyTargetMapsEquiv W V S hS ⟨i, φ⟩⟩

/-- Uniform distributions are invariant under an actual bijection, also
after observing any deterministic statistic. -/
theorem uniform_equiv_projection {α β ι : Type*}
    [Fintype α] [Nonempty α] [Fintype β] [Nonempty β] [Fintype ι]
    (e : α ≃ β) (f : β → ι) (i : ι) :
    ((FiniteLaw.uniform α).pushForward (f ∘ e)).mass i =
      ((FiniteLaw.uniform β).pushForward f).mass i := by
  change (FiniteLaw.uniform α).eventMass (fun a => f (e a) = i) =
    (FiniteLaw.uniform β).eventMass (fun b => f b = i)
  let e' : {a : α // f (e a) = i} ≃ {b : β // f b = i} :=
    e.subtypeEquiv (fun _ => Iff.rfl)
  rw [FiniteLaw.uniform_event, FiniteLaw.uniform_event,
    Fintype.card_congr e', Fintype.card_congr e]

/-- Conditional on a fixed target equation, uniform sampling from all its
connecting morphisms induces exactly the uniform law on connecting kernels.
The family may mix degrees: the common factor is the target automorphism count. -/
theorem uniform_familyTargetMaps_kernel {ι : Type*} [Fintype ι] [Nonempty ι]
    (V : WeierstrassCurve K) [V.IsElliptic]
    (S : ι → AddSubgroup W.Point) [∀ i, Finite (S i)]
    (hS : Function.Injective S) (hj : ∀ i, (quotientCurve W (S i)).j = V.j)
    (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0)
    [Fintype (FamilyTargetMaps W V S)] [Nonempty (FamilyTargetMaps W V S)] (i : ι) :
    ((FiniteLaw.uniform (FamilyTargetMaps W V S)).pushForward
      (familyTargetMapKernel W V S hS)).mass i = (FiniteLaw.uniform ι).mass i := by
  letI : ∀ i, Finite (FixedKernelMaps W V (S i)) :=
    fun i => fixedKernelMaps_finite W V (S i) (hj i) h2 h3
  letI : ∀ i, Fintype (FixedKernelMaps W V (S i)) := fun _ => Fintype.ofFinite _
  letI : Nonempty (Σ i, FixedKernelMaps W V (S i)) := by
    obtain ⟨i⟩ := ‹Nonempty ι›
    obtain ⟨φ⟩ := fixedKernelMaps_nonempty W V (S i) (hj i) h2 h3
    exact ⟨⟨i, φ⟩⟩
  change ((FiniteLaw.uniform (FamilyTargetMaps W V S)).pushForward
    (Sigma.fst ∘ (familyTargetMapsEquiv W V S hS).symm)).mass i = _
  rw [uniform_equiv_projection (familyTargetMapsEquiv W V S hS).symm Sigma.fst i]
  apply uniform_sigma_first (fun i => FixedKernelMaps W V (S i))
    (if V.j = 0 then 6 else if V.j = 1728 then 4 else 2) _ _ i
  · split_ifs <;> norm_num
  · intro i
    rw [Fintype.card_eq_nat_card, card_fixedKernelMaps W V (S i) (hj i) h2 h3]

end
end IsogenyAttack.IsogenySampler
