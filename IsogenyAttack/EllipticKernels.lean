import IsogenyAttack.FiniteTorsionKernels
import IsogenyAttack.TorsionStructure

/-! Exact finite-subgroup counting for the full point group of actual
elliptic curves. The torsion basis is derived by division polynomials and
finite abelian group structure, rather than supplied as an assumption. -/
namespace IsogenyAttack

/-- Every subgroup of cardinal d lies in full d-torsion. This includes the
infinite-cardinality convention d=0, where full 0-torsion is the whole group. -/
theorem subgroup_le_torsionBy_card {G : Type*} [AddCommGroup G]
    (S : AddSubgroup G) : S ≤ AddSubgroup.torsionBy G (Nat.card S) := by
  intro x hx
  apply AddSubgroup.torsionBy.nsmul_iff.mpr
  exact congrArg Subtype.val (card_nsmul_eq_zero' (x := (⟨x,hx⟩ : S)))

/-- Actual order-d subgroups of the whole group and of its full d-torsion
are equivalent, by inclusion and restriction of the ambient group. -/
noncomputable def orderSubgroupTorsionEquiv (G : Type*) [AddCommGroup G] (d : ℕ) :
    {S : AddSubgroup G // Nat.card S = d} ≃
    {S : AddSubgroup (AddSubgroup.torsionBy G d) // Nat.card S = d} where
  toFun S := ⟨S.val.addSubgroupOf (AddSubgroup.torsionBy G d), by
    have hle : S.val ≤ AddSubgroup.torsionBy G d := by
      simpa only [S.property] using subgroup_le_torsionBy_card S.val
    exact (Nat.card_congr (AddSubgroup.addSubgroupOfEquivOfLe hle).toEquiv).trans S.property⟩
  invFun S := ⟨S.val.map (AddSubgroup.torsionBy G d).subtype,
    (Nat.card_congr (S.val.equivMapOfInjective _ Subtype.val_injective).toEquiv).symm.trans S.property⟩
  left_inv S := by
    apply Subtype.ext
    change (S.val.addSubgroupOf (AddSubgroup.torsionBy G d)).map _ = S.val
    apply AddSubgroup.map_addSubgroupOf_eq_of_le
    simpa only [S.property] using subgroup_le_torsionBy_card S.val
  right_inv S := by
    apply Subtype.ext
    change (S.val.map (AddSubgroup.torsionBy G d).subtype).comap _ = S.val
    exact AddSubgroup.comap_map_eq_self_of_injective Subtype.val_injective S.val

/-- An actual rank-two torsion basis classifies finite subgroups of the entire
ambient group, not merely subgroups already assumed to be torsion. -/
noncomputable def ambientHNFEquiv {G : Type*} [AddCommGroup G] {d : ℕ}
    (hd : 0 < d) (basis : AddSubgroup.torsionBy G d ≃+ (ZMod d × ZMod d)) :
    {S : AddSubgroup G // Nat.card S = d} ≃ {h : HNF // h.degree = d} :=
  (orderSubgroupTorsionEquiv G d).trans
    ((orderSubgroupEquiv basis d).trans (torsionHNFEquiv d hd))

/-- The actual embedding of a torsion coordinate group into the ambient group. -/
def torsionCoordinateEmbedding {G : Type*} [AddCommGroup G] {d : ℕ}
    (basis : AddSubgroup.torsionBy G d ≃+ (ZMod d × ZMod d)) :
    (ZMod d × ZMod d) →+ G :=
  (AddSubgroup.torsionBy G d).subtype.comp basis.symm.toAddMonoidHom

theorem torsionCoordinateEmbedding_injective {G : Type*} [AddCommGroup G] {d : ℕ}
    (basis : AddSubgroup.torsionBy G d ≃+ (ZMod d × ZMod d)) :
    Function.Injective (torsionCoordinateEmbedding basis) :=
  Subtype.val_injective.comp basis.symm.injective

theorem ambientHNFEquiv_symm_value {G : Type*} [AddCommGroup G] (h : HNF)
    (basis : AddSubgroup.torsionBy G h.degree ≃+ (ZMod h.degree × ZMod h.degree)) :
    ((ambientHNFEquiv h.degree_pos basis).symm ⟨h,rfl⟩).val =
      h.finiteKernel.map (torsionCoordinateEmbedding basis) := by
  change (h.finiteKernel.map basis.symm.toAddMonoidHom).map _ = _
  exact AddSubgroup.map_map _ _ _

/-- Scalar multiplication commutes with transporting a subgroup along an
additive homomorphism. -/
theorem scalarImage_map {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (S : AddSubgroup A) (f : A →+ B) (n : ℕ) :
    (S.map (nsmulAddMonoidHom n)).map f = (S.map f).map (nsmulAddMonoidHom n) := by
  rw [AddSubgroup.map_map,AddSubgroup.map_map]
  congr 1
  ext x
  exact f.map_nsmul n x

/-- The finite coordinate torsion subgroup becomes the complete m-torsion
subgroup of the ambient group whenever m divides d. -/
theorem fullTorsion_map_coordinateEmbedding {G : Type*} [AddCommGroup G] {d m : ℕ}
    (basis : AddSubgroup.torsionBy G d ≃+ (ZMod d × ZMod d)) (hmd : m ∣ d) :
    (fullTorsion d m).map (torsionCoordinateEmbedding basis) = AddSubgroup.torsionBy G m := by
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    apply AddSubgroup.torsionBy.nsmul_iff.mpr
    have hx0 : m • x = 0 := hx
    rw [← map_nsmul,hx0,map_zero]
  · intro hy
    have hym : m • y = 0 := AddSubgroup.torsionBy.nsmul_iff.mp hy
    have hyd : d • y = 0 := by
      obtain ⟨k,rfl⟩ := hmd
      rw [mul_nsmul,hym,nsmul_zero]
    let z : AddSubgroup.torsionBy G d := ⟨y,AddSubgroup.torsionBy.nsmul_iff.mpr hyd⟩
    refine ⟨basis z,?_,?_⟩
    · change m • basis z = 0
      rw [← map_nsmul]
      have hz : m • z = 0 := Subtype.ext hym
      rw [hz,map_zero]
    · change ((basis.symm (basis z) : AddSubgroup.torsionBy G d) : G) = y
      simp [z]

/-- Cardinality and cyclicity are attached to the exact code used by the
classification, not merely to some existential HNF witness. -/
theorem ambientHNF_inverse_code_spec {G : Type*} [AddCommGroup G] {d : ℕ}
    (hd : 0 < d) (basis : AddSubgroup.torsionBy G d ≃+ (ZMod d × ZMod d))
    (code : {h : HNF // h.degree = d}) :
    let S := ((ambientHNFEquiv hd basis).symm code).val
    Nat.card (S.map (nsmulAddMonoidHom code.val.content)) = code.val.cyclicDegree ∧
      IsAddCyclic (S.map (nsmulAddMonoidHom code.val.content)) ∧
      (∀ m : ℕ, 0 < m → m ∣ d →
        (AddSubgroup.torsionBy G m ≤ S ↔ m ∣ code.val.content)) := by
  obtain ⟨h,hdeg⟩ := code
  cases hdeg
  dsimp only
  rw [ambientHNFEquiv_symm_value]
  have hinj := torsionCoordinateEmbedding_injective basis
  have hscalar : (h.finiteKernel.map (torsionCoordinateEmbedding basis)).map
      (nsmulAddMonoidHom h.content) =
      (h.scalarImage h.content).map (torsionCoordinateEmbedding basis) := by
    rw [← scalarImage_map]
    rfl
  let e := (h.scalarImage h.content).equivMapOfInjective
    (torsionCoordinateEmbedding basis) hinj
  refine ⟨?_,?_,?_⟩
  · rw [hscalar,← Nat.card_congr e.toEquiv]
    exact h.stripped_finiteKernel_card
  · rw [hscalar]
    haveI := h.stripped_finiteKernel_isAddCyclic
    exact isAddCyclic_of_surjective e e.surjective
  · intro m hm hmd
    rw [← fullTorsion_map_coordinateEmbedding basis hmd,
      AddSubgroup.map_le_map_iff_of_injective hinj]
    exact h.fullTorsion_le_finiteKernel_iff hm (Nat.mul_div_cancel' hmd)

theorem ambientHNF_code_spec {G : Type*} [AddCommGroup G] {d : ℕ}
    (hd : 0 < d) (basis : AddSubgroup.torsionBy G d ≃+ (ZMod d × ZMod d))
    (S : AddSubgroup G) (hS : Nat.card S = d) :
    let h := ((ambientHNFEquiv hd basis) ⟨S,hS⟩).val
    Nat.card (S.map (nsmulAddMonoidHom h.content)) = h.cyclicDegree ∧
      IsAddCyclic (S.map (nsmulAddMonoidHom h.content)) ∧
      (∀ m : ℕ, 0 < m → m ∣ d →
        (AddSubgroup.torsionBy G m ≤ S ↔ m ∣ h.content)) := by
  have hh := ambientHNF_inverse_code_spec hd basis ((ambientHNFEquiv hd basis) ⟨S,hS⟩)
  dsimp only at hh ⊢
  rw [Equiv.symm_apply_apply] at hh
  exact hh

/-- Every finite subgroup admits an HNF whose scalar content is intrinsic,
and maximal scalar stripping gives an actual cyclic subgroup of the stated
order. Nothing about the subgroup is assumed beyond its cardinality and the
ambient rank-two torsion structure. -/
theorem ambient_scalar_stripping {G : Type*} [AddCommGroup G] {d : ℕ}
    (hd : 0 < d) (basis : AddSubgroup.torsionBy G d ≃+ (ZMod d × ZMod d))
    (S : AddSubgroup G) (hS : Nat.card S = d) :
    ∃ h : HNF, h.degree = d ∧
      Nat.card (S.map (nsmulAddMonoidHom h.content)) = h.cyclicDegree ∧
      IsAddCyclic (S.map (nsmulAddMonoidHom h.content)) ∧
      (∀ m : ℕ, 0 < m → m ∣ d →
        (AddSubgroup.torsionBy G m ≤ S ↔ m ∣ h.content)) := by
  obtain ⟨⟨h,hdeg⟩,heq⟩ := (ambientHNFEquiv hd basis).symm.surjective ⟨S,hS⟩
  cases hdeg
  have hreal : S = h.finiteKernel.map (torsionCoordinateEmbedding basis) := by
    exact (congrArg Subtype.val heq).symm.trans (ambientHNFEquiv_symm_value h basis)
  have hinj := torsionCoordinateEmbedding_injective basis
  have hscalar : S.map (nsmulAddMonoidHom h.content) =
      (h.scalarImage h.content).map (torsionCoordinateEmbedding basis) := by
    rw [hreal,← scalarImage_map]
    rfl
  let e := (h.scalarImage h.content).equivMapOfInjective
    (torsionCoordinateEmbedding basis) hinj
  refine ⟨h,rfl,?_,?_,?_⟩
  · rw [hscalar,← Nat.card_congr e.toEquiv]
    exact h.stripped_finiteKernel_card
  · rw [hscalar]
    haveI := h.stripped_finiteKernel_isAddCyclic
    exact isAddCyclic_of_surjective e e.surjective
  · intro m hm hmd
    rw [← fullTorsion_map_coordinateEmbedding basis hmd,hreal,
      AddSubgroup.map_le_map_iff_of_injective hinj]
    exact h.fullTorsion_le_finiteKernel_iff hm (Nat.mul_div_cancel' hmd)

open WeierstrassCurve WeierstrassCurve.Affine

variable {K : Type*} [Field K] [NeZero (2 : K)] [IsAlgClosed K]
    {W : Affine K} [W.IsElliptic]

open scoped Classical in
/-- Exact HNF classification for ALL finite subgroups of order d of the actual
elliptic-curve point group, at every degree nonzero in the field. -/
noncomputable def ellipticKernelHNFEquiv (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0)
    {d : ℕ} (hd : (d : K) ≠ 0) :
    {S : AddSubgroup W.Point // Nat.card S = d} ≃ {h : HNF // h.degree = d} :=
  ambientHNFEquiv (Nat.pos_of_ne_zero (by rintro rfl; exact hd (by simp)))
    (Classical.choice (elliptic_torsion_rank_two ha₁ ha₃ hd))

open scoped Classical in
/-- Scalar stripping of the exact HNF code assigned to an actual elliptic
subgroup. Bases at different degrees need not be compatible. -/
theorem elliptic_kernel_code_spec (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0)
    {d : ℕ} (hd : (d : K) ≠ 0) (S : AddSubgroup W.Point) (hS : Nat.card S = d) :
    let h := ((ellipticKernelHNFEquiv ha₁ ha₃ hd) ⟨S,hS⟩).val
    Nat.card (S.map (nsmulAddMonoidHom h.content)) = h.cyclicDegree ∧
      IsAddCyclic (S.map (nsmulAddMonoidHom h.content)) ∧
      (∀ m : ℕ, 0 < m → m ∣ d →
        (AddSubgroup.torsionBy W.Point m ≤ S ↔ m ∣ h.content)) := by
  exact ambientHNF_code_spec _ _ S hS

open scoped Classical in
/-- The classical sigma_1 kernel count for actual elliptic curves, with all
torsion-structure and lattice-classification ingredients formally proved. -/
theorem elliptic_kernel_count (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0)
    {d : ℕ} (hd : (d : K) ≠ 0) :
    Nat.card {S : AddSubgroup W.Point // Nat.card S = d} = kernelCount d := by
  rw [Nat.card_congr (ellipticKernelHNFEquiv ha₁ ha₃ hd),Nat.card_eq_fintype_card,degree_card]

open scoped Classical in
/-- Scalar stripping for every actual elliptic-curve subgroup of degree d.
The full torsion content is maximal with respect to divisibility; after
applying multiplication by that content, the image is cyclic of order d/m².
The conclusion is derived from the elliptic curve, with no torsion-basis or
kernel-count assumption. -/
theorem elliptic_scalar_stripping (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0)
    {d : ℕ} (hd : (d : K) ≠ 0) (S : AddSubgroup W.Point) (hS : Nat.card S = d) :
    ∃ m c : ℕ, 0 < m ∧ 0 < c ∧ d = m^2*c ∧
      AddSubgroup.torsionBy W.Point m ≤ S ∧
      (∀ r : ℕ, 0 < r → r ∣ d →
        (AddSubgroup.torsionBy W.Point r ≤ S ↔ r ∣ m)) ∧
      Nat.card (S.map (nsmulAddMonoidHom m)) = c ∧
      IsAddCyclic (S.map (nsmulAddMonoidHom m)) := by
  have hd0 : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; exact hd (by simp))
  obtain ⟨basis⟩ := elliptic_torsion_rank_two ha₁ ha₃ hd
  obtain ⟨h,hdeg,hcard,hcyc,hcontent⟩ := ambient_scalar_stripping hd0 basis S hS
  have hmc : h.content ∣ d := by
    rw [← hdeg]
    exact h.content_dvd_a.trans (Nat.dvd_mul_right _ _)
  refine ⟨h.content,h.cyclicDegree,h.content_pos,h.cyclicDegree_pos,?_,?_,
    hcontent,hcard,hcyc⟩
  · rw [← hdeg,← h.strip_degree]
    exact h.degree_eq_content_sq_mul_strip
  · exact (hcontent h.content h.content_pos hmc).mpr (dvd_refl _)

end IsogenyAttack
