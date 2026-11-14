import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
Coprime pushing on actual additive subgroups. These are group-theoretic
statements, not postulated facts about elliptic curves. They prove the algebraic
part of pushing prime-to-challenge kernels. An application to geometric
isogenies still has to construct the point homomorphisms, their duals, and the
identification between separable degree and kernel cardinality.
-/

namespace IsogenyAttack
namespace Pushforward

variable {G H : Type*} [AddCommGroup G] [AddCommGroup H]

/-- A homomorphism is injective on a subgroup whose order is coprime to its
kernel order. This uses genuine additive subgroups and their cardinalities. -/
theorem injective_restriction_of_coprime (f : G →+ H) (K : AddSubgroup G)
    (hcop : (Nat.card K).Coprime (Nat.card f.ker)) :
    Function.Injective (f.comp K.subtype) := by
  intro x y hxy
  have hbot : K ⊓ f.ker = ⊥ := AddSubgroup.inf_eq_bot_of_coprime hcop
  have hmem : (x.val - y.val) ∈ K ⊓ f.ker := by
    constructor
    · exact K.sub_mem x.property y.property
    · change f (x.val - y.val) = 0
      simp only [map_sub]
      exact sub_eq_zero.mpr hxy
  rw [hbot] at hmem
  exact Subtype.ext (sub_eq_zero.mp (AddSubgroup.mem_bot.mp hmem))

/-- Exact subgroup isomorphism induced by a coprime push. -/
noncomputable def coprimePushEquiv (f : G →+ H) (K : AddSubgroup G)
    (hcop : (Nat.card K).Coprime (Nat.card f.ker)) :
    K ≃+ K.map f :=
  AddEquiv.ofBijective (f.addSubgroupMap K)
    ⟨fun _ _ h => injective_restriction_of_coprime f K hcop
      (congrArg Subtype.val h), f.addSubgroupMap_surjective K⟩

theorem card_push_of_coprime (f : G →+ H) (K : AddSubgroup G)
    (hcop : (Nat.card K).Coprime (Nat.card f.ker)) :
    Nat.card (K.map f) = Nat.card K :=
  (Nat.card_congr (coprimePushEquiv f K hcop).toEquiv).symm

/-- Pushing a cyclic kernel preserves cyclicity. -/
theorem cyclic_push (f : G →+ H) (K : AddSubgroup G) [IsAddCyclic K] :
    IsAddCyclic (K.map f) :=
  isAddCyclic_of_surjective (f.addSubgroupMap K) (f.addSubgroupMap_surjective K)

/-- Multiplication by a natural number, as a point-group homomorphism. -/
def scalarHom (n : ℕ) : G →+ G where
  toFun x := n • x
  map_zero' := nsmul_zero n
  map_add' x y := by simp only [smul_add]

@[simp] theorem scalarHom_apply (n : ℕ) (x : G) : scalarHom n x = n • x := rfl

/-- On a subgroup of coprime order, multiplying every point by n preserves
exactly the subgroup, not merely its order. -/
theorem map_scalar_eq_self (K : AddSubgroup G) (n : ℕ)
    (hcop : (Nat.card K).Coprime n) : K.map (scalarHom n) = K := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact K.nsmul_mem hx n
  · intro hy
    obtain ⟨x, hx⟩ := (hcop.nsmul_right_bijective (G := K)).surjective ⟨y, hy⟩
    exact ⟨x.val, x.property, congrArg Subtype.val hx⟩

/-- The duality relation already proves injectivity on prime-to-n kernels;
no global injectivity of an isogeny is asserted. -/
theorem injective_restriction_of_dual (f : G →+ H) (g : H →+ G) (n : ℕ)
    (hdual : ∀ x, g (f x) = n • x) (K : AddSubgroup G)
    (hcop : (Nat.card K).Coprime n) :
    Function.Injective (f.comp K.subtype) := by
  intro x y hxy
  apply (hcop.nsmul_right_bijective (G := K)).injective
  apply Subtype.ext
  change n • x.val = n • y.val
  rw [← hdual, ← hdual]
  exact congrArg g hxy

noncomputable def dualPushEquiv (f : G →+ H) (g : H →+ G) (n : ℕ)
    (hdual : ∀ x, g (f x) = n • x) (K : AddSubgroup G)
    (hcop : (Nat.card K).Coprime n) : K ≃+ K.map f :=
  AddEquiv.ofBijective (f.addSubgroupMap K)
    ⟨fun _ _ h => injective_restriction_of_dual f g n hdual K hcop
      (congrArg Subtype.val h), f.addSubgroupMap_surjective K⟩

theorem card_push_of_dual (f : G →+ H) (g : H →+ G) (n : ℕ)
    (hdual : ∀ x, g (f x) = n • x) (K : AddSubgroup G)
    (hcop : (Nat.card K).Coprime n) :
    Nat.card (K.map f) = Nat.card K :=
  (Nat.card_congr (dualPushEquiv f g n hdual K hcop).toEquiv).symm

/-- Push by f and then by its dual returns the same prime-to-n kernel. -/
theorem push_dual_cancel (f : G →+ H) (g : H →+ G) (n : ℕ)
    (hdual : ∀ x, g (f x) = n • x) (K : AddSubgroup G)
    (hcop : (Nat.card K).Coprime n) : (K.map f).map g = K := by
  rw [AddSubgroup.map_map]
  have heq : g.comp f = scalarHom n := AddMonoidHom.ext hdual
  rw [heq]
  exact map_scalar_eq_self K n hcop

/-- Kernels of a fixed cardinality, as actual subgroups of the point group. -/
def KernelsOfOrder (m : ℕ) (G : Type*) [AddCommGroup G] :=
  {K : AddSubgroup G // Nat.card K = m}

noncomputable def pushKernel (m n : ℕ) (f : G →+ H) (g : H →+ G)
    (hdual : ∀ x, g (f x) = n • x) (hcop : m.Coprime n) :
    KernelsOfOrder m G → KernelsOfOrder m H := fun K =>
  ⟨K.val.map f, (card_push_of_dual f g n hdual K.val (by simpa [K.property] using hcop)).trans K.property⟩

/-- Dual homomorphisms induce a bijection on kernels of every order coprime
to their scalar composition. This is the kernel-level correspondence behind
odd-degree pushing through a power-of-two challenge. -/
noncomputable def kernelPushBijection (m n : ℕ) (f : G →+ H) (g : H →+ G)
    (hgf : ∀ x, g (f x) = n • x) (hfg : ∀ y, f (g y) = n • y)
    (hcop : m.Coprime n) : KernelsOfOrder m G ≃ KernelsOfOrder m H where
  toFun := pushKernel m n f g hgf hcop
  invFun := pushKernel m n g f hfg hcop
  left_inv K := by
    apply Subtype.ext
    exact push_dual_cancel f g n hgf K.val (by simpa [K.property] using hcop)
  right_inv K := by
    apply Subtype.ext
    exact push_dual_cancel g f n hfg K.val (by simpa [K.property] using hcop)


/-- In the presence of coprime duality, cyclicity is preserved in both directions. -/
theorem cyclic_push_iff_of_dual (f : G →+ H) (g : H →+ G) (n : ℕ)
    (hdual : ∀ x, g (f x) = n • x) (K : AddSubgroup G)
    (hcop : (Nat.card K).Coprime n) :
    IsAddCyclic K ↔ IsAddCyclic (K.map f) := by
  constructor
  · intro h
    letI := h
    exact cyclic_push f K
  · intro h
    letI := h
    exact isAddCyclic_of_surjective (dualPushEquiv f g n hdual K hcop).symm
      (dualPushEquiv f g n hdual K hcop).symm.surjective

/-- The correspondence also restricts to cyclic kernels. -/
noncomputable def cyclicKernelPushBijection (m n : ℕ) (f : G →+ H) (g : H →+ G)
    (hgf : ∀ x, g (f x) = n • x) (hfg : ∀ y, f (g y) = n • y)
    (hcop : m.Coprime n) :
    {K : KernelsOfOrder m G // IsAddCyclic K.val} ≃
      {K : KernelsOfOrder m H // IsAddCyclic K.val} :=
  (kernelPushBijection m n f g hgf hfg hcop).subtypeEquiv fun K =>
    cyclic_push_iff_of_dual f g n hgf K.val (by simpa [K.property] using hcop)

/-- Specialization used by Algorithm 6: odd-degree kernels can be pushed
bijectively through a challenge whose dual composition is multiplication by 2^k. -/
noncomputable def oddKernelPushBijection (m k : ℕ) (f : G →+ H) (g : H →+ G)
    (hgf : ∀ x, g (f x) = (2 ^ k) • x) (hfg : ∀ y, f (g y) = (2 ^ k) • y)
    (hm : Odd m) : KernelsOfOrder m G ≃ KernelsOfOrder m H :=
  kernelPushBijection m (2 ^ k) f g hgf hfg
    (Nat.Coprime.pow_right k hm.coprime_two_right)


@[simp] theorem scalarHom_eq_nsmulAddMonoidHom (n : ℕ) :
    (scalarHom n : G →+ G) = nsmulAddMonoidHom n := by
  ext x
  rfl

/-- A finite cyclic kernel has a subgroup of every order dividing its order. -/
theorem cyclic_torsion_card [Finite G] [IsAddCyclic G] (d : ℕ)
    (hd : d ∣ Nat.card G) : Nat.card (scalarHom d : G →+ G).ker = d := by
  rw [scalarHom_eq_nsmulAddMonoidHom,
    IsAddCyclic.card_nsmulAddMonoidHom_ker G d, Nat.gcd_eq_right hd]

/-- The subgroup used to split a cyclic map at a specified degree is unique.
This supplies the finite-group part of Algorithm 6, line 6. -/
theorem existsUnique_cyclic_subgroup [Finite G] [IsAddCyclic G] (d : ℕ)
    (hd : d ∣ Nat.card G) : ∃! K : AddSubgroup G, Nat.card K = d := by
  let T : AddSubgroup G := (scalarHom d).ker
  have hT : Nat.card T = d := cyclic_torsion_card d hd
  refine ⟨T, hT, ?_⟩
  intro K hK
  apply AddSubgroup.eq_of_le_of_card_ge
  · intro x hx
    have hz : (Nat.card K) • (⟨x, hx⟩ : K) = 0 := card_nsmul_eq_zero'
    have hz' := congrArg Subtype.val hz
    change d • x = 0
    simpa [hK] using hz'
  · exact hT.trans hK.symm |>.le

end Pushforward
end IsogenyAttack
