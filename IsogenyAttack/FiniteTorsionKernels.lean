import IsogenyAttack.LatticeKernels
import Mathlib.Data.ZMod.Basic

/-! Exact subgroup counting for the actual finite rank-two torsion group.
This is group theory; identifying elliptic-curve torsion with this group is a
separate algebraic-geometric theorem. -/
namespace IsogenyAttack

/-- Reduction of an integral vector modulo d. -/
def reduction (d : ℕ) : ℤ × ℤ →+ ZMod d × ZMod d :=
  (Int.castAddHom (ZMod d)).prodMap (Int.castAddHom (ZMod d))

theorem reduction_surjective (d : ℕ) : Function.Surjective (reduction d) := by
  rintro ⟨x,y⟩
  obtain ⟨a,ha⟩ := ZMod.intCast_surjective x
  obtain ⟨b,hb⟩ := ZMod.intCast_surjective y
  exact ⟨(a,b),Prod.ext ha hb⟩

/-- Genuine order-d subgroups of the rank-two d-torsion group. -/
abbrev TorsionKernel (d : ℕ) :=
  {K : AddSubgroup (ZMod d × ZMod d) // Nat.card K = d}

theorem torsion_card_eq_index (d : ℕ) (hd : 0 < d)
    (K : AddSubgroup (ZMod d × ZMod d)) : Nat.card K = d ↔ K.index = d := by
  have hh := K.card_mul_index
  rw [Nat.card_prod, Nat.card_zmod] at hh
  constructor
  · intro hc
    rw [hc] at hh
    exact Nat.eq_of_mul_eq_mul_left hd hh
  · intro hi
    rw [hi] at hh
    exact Nat.eq_of_mul_eq_mul_right hd hh

/-- An index-d lattice contains the full scalar sublattice d Z². -/
theorem reduction_ker_le (d : ℕ) (L : IndexLattice d) :
    (reduction d).ker ≤ L.val := by
  intro x hx
  have hx0 : reduction d x = 0 := hx
  have h1 : (d : ℤ) ∣ x.1 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd x.1 d).mp (congrArg Prod.fst hx0)
  have h2 : (d : ℤ) ∣ x.2 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd x.2 d).mp (congrArg Prod.snd hx0)
  obtain ⟨u,hu⟩ := h1
  obtain ⟨v,hv⟩ := h2
  have hh := L.val.nsmul_index_mem (u,v)
  convert hh using 1
  apply Prod.ext <;> simp [L.property,hu,hv]

/-- Order-d subgroups and index-d integral lattices correspond by reduction
and inverse image. Both inverse identities are genuine subgroup equalities. -/
noncomputable def torsionLatticeEquiv (d : ℕ) (hd : 0 < d) :
    TorsionKernel d ≃ IndexLattice d where
  toFun K := ⟨K.val.comap (reduction d), by
    rw [K.val.index_comap_of_surjective (reduction_surjective d)]
    exact (torsion_card_eq_index d hd K.val).mp K.property⟩
  invFun L := ⟨L.val.map (reduction d), by
    apply (torsion_card_eq_index d hd _).mpr
    have hh := (L.val.map (reduction d)).index_comap_of_surjective (reduction_surjective d)
    rw [AddSubgroup.comap_map_eq_self (reduction_ker_le d L)] at hh
    exact hh.symm.trans L.property⟩
  left_inv K := by
    apply Subtype.ext
    apply AddSubgroup.map_comap_eq_self
    rw [AddMonoidHom.range_eq_top.mpr (reduction_surjective d)]
    exact le_top
  right_inv L := by
    apply Subtype.ext
    exact AddSubgroup.comap_map_eq_self (reduction_ker_le d L)

/-- Exact classification of rank-two torsion subgroups by the already checked
HNF codes, with no subgroup-counting hypothesis. -/
noncomputable def torsionHNFEquiv (d : ℕ) (hd : 0 < d) :
    TorsionKernel d ≃ {h : HNF // h.degree = d} :=
  (torsionLatticeEquiv d hd).trans (degreeLatticeEquiv d hd).symm

/-- The classical sigma_1 count, proved for actual finite subgroups. -/
theorem torsionKernel_card (d : ℕ) (hd : 0 < d) :
    Nat.card (TorsionKernel d) = kernelCount d := by
  rw [Nat.card_congr (torsionHNFEquiv d hd), Nat.card_eq_fintype_card, degree_card]


/-- The full m-torsion as the kernel of scalar multiplication in the actual
finite additive group. -/
def fullTorsion (d m : ℕ) : AddSubgroup (ZMod d × ZMod d) :=
  (nsmulAddMonoidHom (α := ZMod d × ZMod d) m).ker

/-- The preimage of full m-torsion consists of coordinate multiples of d/m. -/
theorem reduction_mem_fullTorsion {d m k : ℕ} (hm : 0 < m) (hmk : m*k=d) (z : ℤ×ℤ) :
    reduction d z ∈ fullTorsion d m ↔ (k : ℤ) ∣ z.1 ∧ (k : ℤ) ∣ z.2 := by
  have hm0 : (m : ℤ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  have hd : (d : ℤ) = (m : ℤ)*(k : ℤ) := by exact_mod_cast hmk.symm
  change ((m • (z.1 : ZMod d)), (m • (z.2 : ZMod d))) = (0,0) ↔ _
  rw [Prod.mk.injEq]
  simp only [nsmul_eq_mul]
  have h1 : (m : ZMod d)*(z.1 : ZMod d)=0 ↔ (k : ℤ) ∣ z.1 := by
    have hh : (((m : ℤ)*z.1 : ℤ) : ZMod d)=0 ↔ (k : ℤ) ∣ z.1 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd,hd,Int.mul_dvd_mul_iff_left hm0]
    simpa using hh
  have h2 : (m : ZMod d)*(z.2 : ZMod d)=0 ↔ (k : ℤ) ∣ z.2 := by
    have hh : (((m : ℤ)*z.2 : ℤ) : ZMod d)=0 ↔ (k : ℤ) ∣ z.2 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd,hd,Int.mul_dvd_mul_iff_left hm0]
    simpa using hh
  exact and_congr h1 h2

/-- Containment of full torsion is determined by its two coordinate generators. -/
theorem fullTorsion_le_iff {d m k : ℕ} (hm : 0 < m) (hmk : m*k=d)
    (K : AddSubgroup (ZMod d × ZMod d)) :
    fullTorsion d m ≤ K ↔
      reduction d ((k : ℤ),0) ∈ K ∧ reduction d ((0 : ℤ),(k : ℤ)) ∈ K := by
  constructor
  · intro hh
    exact ⟨hh ((reduction_mem_fullTorsion hm hmk _).mpr ⟨dvd_refl _,dvd_zero _⟩),
      hh ((reduction_mem_fullTorsion hm hmk _).mpr ⟨dvd_zero _,dvd_refl _⟩)⟩
  · rintro ⟨h1,h2⟩ x hx
    obtain ⟨z,rfl⟩ := reduction_surjective d x
    obtain ⟨⟨u,hu⟩,⟨v,hv⟩⟩ := (reduction_mem_fullTorsion hm hmk z).mp hx
    have hh := K.add_mem (K.zsmul_mem h1 u) (K.zsmul_mem h2 v)
    convert hh using 1
    apply Prod.ext <;> simp [reduction,hu,hv,zsmul_eq_mul,mul_comm]

/-- Full m-torsion has exactly m² elements when m divides the ambient modulus. -/
theorem fullTorsion_card {d m : ℕ} (hd : 0 < d) (hdiv : m ∣ d) :
    Nat.card (fullTorsion d m) = m ^ 2 := by
  letI : NeZero d := ⟨Nat.ne_of_gt hd⟩
  let A : AddSubgroup (ZMod d) := (nsmulAddMonoidHom m).ker
  have heq : fullTorsion d m = A.prod A := by
    ext x
    change m • x = 0 ↔ m • x.1 = 0 ∧ m • x.2 = 0
    exact Prod.ext_iff
  have hc : Nat.card A = m := by
    have hh := IsAddCyclic.card_nsmulAddMonoidHom_ker (ZMod d) m
    simpa [A,Nat.card_zmod,Nat.gcd_eq_right hdiv] using hh
  rw [heq,Nat.card_congr (A.prodEquiv A).toEquiv,Nat.card_prod,hc]
  ring

namespace HNF

/-- The actual finite subgroup associated with an HNF code. -/
def finiteKernel (h : HNF) : AddSubgroup (ZMod h.degree × ZMod h.degree) :=
  h.lattice.map (reduction h.degree)

/-- Its cardinality is the degree, not merely the cardinality of a set of codes. -/
theorem finiteKernel_card (h : HNF) : Nat.card h.finiteKernel = h.degree := by
  exact ((torsionLatticeEquiv h.degree h.degree_pos).symm
    ⟨h.lattice,h.lattice_index⟩).property

@[simp] theorem reduction_mem_finiteKernel (h : HNF) (z : ℤ × ℤ) :
    reduction h.degree z ∈ h.finiteKernel ↔ z ∈ h.lattice := by
  change z ∈ (h.lattice.map (reduction h.degree)).comap (reduction h.degree) ↔ _
  rw [AddSubgroup.comap_map_eq_self (reduction_ker_le h.degree ⟨h.lattice,h.lattice_index⟩)]

/-- The integer gcd called scalar content is precisely the intrinsic full-torsion
content of the associated finite subgroup. -/
theorem fullTorsion_le_finiteKernel_iff (h : HNF) {m k : ℕ}
    (hm : 0 < m) (hmk : m*k = h.degree) :
    fullTorsion h.degree m ≤ h.finiteKernel ↔ m ∣ h.content := by
  rw [fullTorsion_le_iff hm hmk, reduction_mem_finiteKernel, reduction_mem_finiteKernel]
  exact h.coordinate_multiples_mem_iff hm hmk


/-- Killing the first HNF generator leaves a cyclic image, proved for arbitrary
additive homomorphisms. -/
theorem lattice_map_cyclic {G : Type*} [AddCommGroup G] (h : HNF)
    (f : ℤ × ℤ →+ G) (hkill : f ((h.a : ℤ),0) = 0) :
    h.lattice.map f = AddSubgroup.zmultiples (f ((h.b : ℤ),(h.e : ℤ))) := by
  ext y
  constructor
  · rintro ⟨z,⟨u,v,rfl⟩,rfl⟩
    apply AddSubgroup.mem_zmultiples_iff.mpr
    refine ⟨v,?_⟩
    have hz : ((h.a : ℤ)*u + (h.b : ℤ)*v,(h.e : ℤ)*v) =
        u • ((h.a : ℤ),0) + v • ((h.b : ℤ),(h.e : ℤ)) := by
      ext <;> simp [mul_comm]
    rw [hz,map_add,map_zsmul,map_zsmul,hkill,zsmul_zero,zero_add]
  · intro hy
    obtain ⟨v,rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hy
    refine ⟨v • ((h.b : ℤ),(h.e : ℤ)), h.lattice.zsmul_mem h.second_generator_mem v, ?_⟩
    exact f.map_zsmul v _

/-- Image after scalar multiplication, as an actual finite subgroup. -/
def scalarImage (h : HNF) (m : ℕ) : AddSubgroup (ZMod h.degree × ZMod h.degree) :=
  h.finiteKernel.map (nsmulAddMonoidHom m)

theorem scalarImage_e_eq (h : HNF) :
    h.scalarImage h.e = AddSubgroup.zmultiples
      ((nsmulAddMonoidHom h.e).comp (reduction h.degree) ((h.b : ℤ),(h.e : ℤ))) := by
  rw [scalarImage,finiteKernel,AddSubgroup.map_map]
  apply h.lattice_map_cyclic
  have hh : h.e*h.a = h.degree := by unfold degree; ring
  change h.e • reduction h.degree ((h.a : ℤ),0) = 0
  simp [reduction,nsmul_eq_mul,← Nat.cast_mul,hh]

/-- Scalar stripping also has the certified cardinality for the actual subgroup.
The hypothesis merely says m is a scalar factor, characterized intrinsically above. -/
theorem scalarImage_card (h : HNF) {m : ℕ} (hm : 0 < m) (hdiv : m ∣ h.content) :
    Nat.card (h.scalarImage m) = h.degree / m ^ 2 := by
  have hmd : m ∣ h.degree := (hdiv.trans h.content_dvd_a).trans (Nat.dvd_mul_right _ _)
  have hmk : m * (h.degree / m) = h.degree := Nat.mul_div_cancel' hmd
  have hinc := (h.fullTorsion_le_finiteKernel_iff hm hmk).mpr hdiv
  have hh := AddSubgroup.relIndex_mul_relIndex
    (H := (⊥ : AddSubgroup (ZMod h.degree × ZMod h.degree)))
    (K := fullTorsion h.degree m) (L := h.finiteKernel) bot_le hinc
  rw [AddSubgroup.relIndex_bot_left,AddSubgroup.relIndex_bot_left] at hh
  have hrel : (fullTorsion h.degree m).relIndex h.finiteKernel = Nat.card (h.scalarImage m) :=
    AddSubgroup.relIndex_ker _ _
  rw [hrel, fullTorsion_card h.degree_pos hmd,h.finiteKernel_card] at hh
  calc
    Nat.card (h.scalarImage m) = (m^2 * Nat.card (h.scalarImage m)) / m^2 :=
      (Nat.mul_div_cancel_left _ (pow_pos hm 2)).symm
    _ = h.degree / m^2 := congrArg (fun n : ℕ => n / m^2) hh

theorem stripped_finiteKernel_card (h : HNF) :
    Nat.card (h.scalarImage h.content) = h.cyclicDegree :=
  h.scalarImage_card h.content_pos (dvd_refl _)

/-- The exact exponent divisibility relation for every actual kernel subgroup. -/
theorem finiteKernel_annihilated_iff (h : HNF) (n : ℕ) :
    (∀ y ∈ h.finiteKernel, n • y = 0) ↔ h.degree ∣ n * h.content := by
  have hg : (n*h.a).gcd ((n*h.e).gcd (n*h.b)) = n*h.content := by
    rw [Nat.gcd_mul_left,Nat.gcd_mul_left]
    rfl
  have hcast (x : ℕ) : n • (x : ZMod h.degree) = 0 ↔ h.degree ∣ n*x := by
    simp only [nsmul_eq_mul,← Nat.cast_mul,ZMod.natCast_eq_zero_iff]
  constructor
  · intro hann
    have h1 := hann (reduction h.degree ((h.a : ℤ),0))
      (AddSubgroup.mem_map.mpr ⟨_,h.first_generator_mem,rfl⟩)
    have h2 := hann (reduction h.degree ((h.b : ℤ),(h.e : ℤ)))
      (AddSubgroup.mem_map.mpr ⟨_,h.second_generator_mem,rfl⟩)
    have hda : h.degree ∣ n*h.a := (hcast h.a).mp (by simpa [reduction] using congrArg Prod.fst h1)
    have hdb : h.degree ∣ n*h.b := (hcast h.b).mp (by simpa [reduction] using congrArg Prod.fst h2)
    have hde : h.degree ∣ n*h.e := (hcast h.e).mp (by simpa [reduction] using congrArg Prod.snd h2)
    rw [← hg]
    exact Nat.dvd_gcd hda (Nat.dvd_gcd hde hdb)
  · intro hdiv
    rw [← hg,Nat.dvd_gcd_iff,Nat.dvd_gcd_iff] at hdiv
    let f := (nsmulAddMonoidHom (α := ZMod h.degree × ZMod h.degree) n).comp (reduction h.degree)
    have hf1 : f ((h.a : ℤ),0) = 0 := by
      apply Prod.ext
      · simpa [f,reduction] using (hcast h.a).mpr hdiv.1
      · simp [f,reduction]
    have hf2 : f ((h.b : ℤ),(h.e : ℤ)) = 0 := by
      apply Prod.ext
      · simpa [f,reduction] using (hcast h.b).mpr hdiv.2.2
      · simpa [f,reduction] using (hcast h.e).mpr hdiv.2.1
    rintro y ⟨z,⟨u,v,rfl⟩,rfl⟩
    change f ((h.a : ℤ)*u + (h.b : ℤ)*v,(h.e : ℤ)*v) = 0
    have hz : ((h.a : ℤ)*u + (h.b : ℤ)*v,(h.e : ℤ)*v) =
        u • ((h.a : ℤ),0) + v • ((h.b : ℤ),(h.e : ℤ)) := by
      ext <;> simp [mul_comm]
    rw [hz,map_add,map_zsmul,map_zsmul,hf1,hf2]
    simp

/-- Scalar images have the expected annihilator in the actual group. -/
theorem scalarImage_annihilated_iff (h : HNF) (m n : ℕ) :
    (∀ y ∈ h.scalarImage m, n • y = 0) ↔ h.degree ∣ (m*n)*h.content := by
  have hh : (∀ y ∈ h.scalarImage m, n • y = 0) ↔
      ∀ x ∈ h.finiteKernel, (m*n) • x = 0 := by
    constructor
    · intro ha x hx
      have hy := ha (m • x) (AddSubgroup.mem_map.mpr ⟨x,hx,rfl⟩)
      rw [mul_nsmul]
      exact hy
    · intro ha y hy
      obtain ⟨x,hx,rfl⟩ := hy
      change n • (m • x) = 0
      rw [← mul_nsmul]
      exact ha x hx
  exact hh.trans (h.finiteKernel_annihilated_iff (m*n))

/-- After removing maximal full torsion, annihilation is exactly divisibility
by the arithmetic cyclic degree. -/
theorem stripped_annihilated_iff (h : HNF) (n : ℕ) :
    (∀ y ∈ h.scalarImage h.content, n • y = 0) ↔ h.cyclicDegree ∣ n := by
  rw [h.scalarImage_annihilated_iff]
  have hd : h.degree = h.content ^ 2 * h.cyclicDegree := by
    rw [← h.strip_degree]
    exact h.degree_eq_content_sq_mul_strip
  have hm : (h.content*n)*h.content = h.content^2*n := by ring
  rw [hd,hm,Nat.mul_dvd_mul_iff_left (pow_pos h.content_pos 2)]

/-- Full scalar stripping really yields a cyclic finite subgroup for EVERY
HNF, proved using the exact annihilator and cardinality. -/
theorem stripped_finiteKernel_isAddCyclic (h : HNF) :
    IsAddCyclic (h.scalarImage h.content) := by
  letI : NeZero h.degree := ⟨Nat.ne_of_gt h.degree_pos⟩
  apply IsAddCyclic.iff_exponent_eq_card.mpr
  rw [h.stripped_finiteKernel_card]
  have hh (n : ℕ) : AddMonoid.exponent (h.scalarImage h.content) ∣ n ↔ h.cyclicDegree ∣ n := by
    rw [AddMonoid.exponent_dvd]
    simp only [addOrderOf_dvd_iff_nsmul_eq_zero]
    have hsub : (∀ y : h.scalarImage h.content, n • y = 0) ↔
        ∀ y ∈ h.scalarImage h.content, n • y = 0 := by
      constructor
      · intro ha y hy
        exact congrArg Subtype.val (ha ⟨y,hy⟩)
      · intro ha y
        exact Subtype.ext (ha y.val y.property)
    exact hsub.trans (h.stripped_annihilated_iff n)
  exact Nat.dvd_antisymm ((hh h.cyclicDegree).mpr (dvd_refl _))
    ((hh _).mp (dvd_refl _))

/-- In particular every favorable scalar lift really has a cyclic stripped
image, not just an arithmetic degree labeled 'cyclic'. -/
theorem lift_scalarImage_isAddCyclic (m c t : ℕ) (hm : 0 < m) (hc : 0 < c) (ht : t < c) :
    IsAddCyclic ((lift m c t hm hc ht).scalarImage m) := by
  change IsAddCyclic ((lift m c t hm hc ht).scalarImage (lift m c t hm hc ht).e)
  rw [scalarImage_e_eq]
  infer_instance

/-- Every favorable lift has an actual cyclic scalar-stripped subgroup of order c. -/
theorem lift_scalarImage_card (m c t : ℕ) (hm : 0 < m) (hc : 0 < c) (ht : t < c) :
    Nat.card ((lift m c t hm hc ht).scalarImage m) = c := by
  have hh := (lift m c t hm hc ht).stripped_finiteKernel_card
  simpa using hh

end HNF

/-- Transport of actual order-d subgroups under an additive group isomorphism. -/
noncomputable def orderSubgroupEquiv {G H : Type*} [AddGroup G] [AddGroup H]
    (e : G ≃+ H) (d : ℕ) :
    {K : AddSubgroup G // Nat.card K = d} ≃ {K : AddSubgroup H // Nat.card K = d} where
  toFun K := ⟨K.val.map e.toAddMonoidHom,
    (Nat.card_congr (e.addSubgroupMap K.val).toEquiv).symm.trans K.property⟩
  invFun K := ⟨K.val.map e.symm.toAddMonoidHom,
    (Nat.card_congr (e.symm.addSubgroupMap K.val).toEquiv).symm.trans K.property⟩
  left_inv K := by
    apply Subtype.ext
    change (K.val.map e.toAddMonoidHom).map e.symm.toAddMonoidHom = K.val
    rw [AddSubgroup.map_map]
    have hh : e.symm.toAddMonoidHom.comp e.toAddMonoidHom = AddMonoidHom.id G := by ext; simp
    rw [hh,AddSubgroup.map_id]
  right_inv K := by
    apply Subtype.ext
    change (K.val.map e.symm.toAddMonoidHom).map e.toAddMonoidHom = K.val
    rw [AddSubgroup.map_map]
    have hh : e.toAddMonoidHom.comp e.symm.toAddMonoidHom = AddMonoidHom.id H := by ext; simp
    rw [hh,AddSubgroup.map_id]

/-- The actual kernel count for any group equipped with a rank-two torsion
basis. The basis is the only structural input; the counting theorem is derived. -/
theorem rankTwoTorsion_kernel_count {G : Type*} [AddGroup G] {d : ℕ}
    (hd : 0 < d) (basis : G ≃+ (ZMod d × ZMod d)) :
    Nat.card {K : AddSubgroup G // Nat.card K = d} = kernelCount d := by
  rw [Nat.card_congr (orderSubgroupEquiv basis d)]
  exact torsionKernel_card d hd

end IsogenyAttack
