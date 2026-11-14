import IsogenyAttack.RawTargetSampler
import IsogenyAttack.CyclicComponent

/-!
# All raw maps and their genuine cyclic components

The prime-to-characteristic degree restriction makes separability automatic.
The target-first sampler therefore contains every raw connecting isogeny in
the stated degree range, and its observed degree is the degree of an actual
cyclic component to the original target equation.
-/
namespace IsogenyAttack

open WeierstrassCurve WeierstrassCurve.Affine TauCeti

noncomputable section
open scoped Classical

variable {K : Type*} [Field K] [IsAlgClosed K]
    {W V : Affine K} [W.IsElliptic] [V.IsElliptic]

omit [IsAlgClosed K] [W.IsElliptic] [V.IsElliptic] in
/-- An isogeny whose degree is nonzero in the coefficient field is separable. -/
theorem isogeny_separable_of_degree_nonzero (p : ℕ) [Fact p.Prime] [CharP K p]
    (φ : Isogeny W V) (hc : (φ.degree : K) ≠ 0) :
    Algebra.IsSeparable φ.fieldPullback.fieldRange W.FunctionField := by
  apply (φ.inseparableDegree_eq_one_iff_isSeparable).mp
  obtain ⟨r, hr⟩ : ∃ r : ℕ, φ.inseparableDegree = p ^ r :=
    φ.inseparableDegree_def ▸ finInsepDegree_eq_pow _ _ p
  by_cases h : r = 0
  · simpa only [h, pow_zero] using hr
  · exfalso
    have hpd : p ∣ φ.degree := by
      rw [← φ.separableDegree_mul_inseparableDegree, hr]
      exact (dvd_pow_self p h).trans (Nat.dvd_mul_left _ _)
    exact hc ((CharP.cast_eq_zero_iff K p _).mpr hpd)

omit [IsAlgClosed K] [W.IsElliptic] [V.IsElliptic] in
/-- All raw isogenies up to a valid cutoff are automatically separable. -/
theorem bounded_isogeny_separable (p : ℕ) [Fact p.Prime] [CharP K p]
    {B : ℕ} (hdeg : ValidDegrees K B) (φ : Isogeny W V) (hφ : φ.degree ≤ B) :
    Algebra.IsSeparable φ.fieldPullback.fieldRange W.FunctionField :=
  isogeny_separable_of_degree_nonzero p φ (hdeg φ.degree φ.degree_pos hφ)

theorem bounded_isogeny_card_ker (p : ℕ) [Fact p.Prime] [CharP K p]
    {B : ℕ} (hdeg : ValidDegrees K B) (φ : Isogeny W V) (hφ : φ.degree ≤ B) :
    Nat.card φ.ker = φ.degree := by
  let := bounded_isogeny_separable p hdeg φ hφ
  exact φ.card_ker_eq_degree

namespace IsogenySampler

/-- Literally every degree-d isogeny to a nonsingular Montgomery equation. -/
abbrev AllDegreeMaps (W : Affine K) (d : ℕ) :=
  Σ A : MontgomeryParameter (K := K),
    {φ : Isogeny W (Montgomery.curve A.val).toAffine // φ.degree = d}

/-- At invertible degree the kernel-cardinality restriction in DegreeMaps
removes no raw isogeny. The equivalence preserves every actual map. -/
def allDegreeMapsEquiv (p : ℕ) [Fact p.Prime] [CharP K p]
    (d : ℕ) (hd : (d : K) ≠ 0) (h2 : (2 : K) ≠ 0) :
    AllDegreeMaps W d ≃ DegreeMaps W d where
  toFun x := by
    let := Montgomery.curve_isElliptic h2 x.1.property
    let := isogeny_separable_of_degree_nonzero p x.2.val (by rwa [x.2.property])
    exact ⟨x.1, x.2.val, x.2.property, x.2.val.card_ker_eq_degree⟩
  invFun x := ⟨x.1, x.2.val, x.2.property.1⟩
  left_inv _ := rfl
  right_inv _ := rfl

end IsogenySampler

namespace RawTargetSampler

variable [NeZero (2 : K)]
variable (p : ℕ) [Fact p.Prime] [CharP K p]
    [Algebra (ZMod p) K] [Algebra.IsAlgebraic (ZMod p) K]

/-- Every raw isogeny to the specified target satisfying the strict bound. -/
abbrev AllConnectingMaps (B : ℕ) (a : Target (K := K) p) :=
  {φ : Isogeny W (targetCurve p a).toAffine // φ.degree < B}

theorem connectingMaps_condition_iff_degree_lt (B : ℕ) (hdeg : ValidDegrees K B)
    (a : Target (K := K) p) (φ : Isogeny W (targetCurve p a).toAffine) :
    (Nat.card φ.ker = φ.degree ∧
      ∃ S : ConnectingKernel (W := W) p B a,
        φ.ker = quotientKernel W (kernelFamily p B a S)) ↔ φ.degree < B := by
  constructor
  · intro h
    exact connectingMaps_degree_lt p B a ⟨φ, h⟩
  · intro hφ
    let := bounded_isogeny_separable p hdeg φ hφ.le
    let S : ActualKernel W.Point B :=
      ⟨⟨φ.degree, Finset.mem_Icc.mpr ⟨φ.degree_pos, hφ.le⟩⟩,
        ⟨φ.toPointHom.ker, φ.card_ker_toPointHom_eq_degree⟩⟩
    have hk : φ.ker = quotientKernel W S.2.val := φ.ker_eq_map_ker_toPointHom
    have hj : (quotientCurve W S.2.val).j = (targetCurve p a).j :=
      IsogenySampler.fixedKernelMaps_target_j W (targetCurve p a) S.2.val
        ⟨φ, hk, φ.card_ker_eq_degree⟩
    exact ⟨φ.card_ker_eq_degree, ⟨⟨S, hφ, hj⟩, hk⟩⟩

/-- The connecting sampler's outcomes are exactly all raw isogenies below
the strict cutoff, with no omitted inseparable or exceptional-target cases. -/
def connectingMapsEquivAll (B : ℕ) (hdeg : ValidDegrees K B)
    (a : Target (K := K) p) :
    ConnectingMaps (W := W) p B a ≃ AllConnectingMaps (W := W) p B a :=
  Equiv.subtypeEquivRight (connectingMaps_condition_iff_degree_lt p B hdeg a)

instance connectingMap_separable (B : ℕ) (a : Target (K := K) p)
    (φ : ConnectingMaps (W := W) p B a) :
    Algebra.IsSeparable φ.val.fieldPullback.fieldRange W.FunctionField :=
  IsogenySampler.isSeparable_of_card_ker_eq_degree W φ.val φ.property.1

theorem mapKernel_point_kernel (B : ℕ) (a : Target (K := K) p)
    (φ : ConnectingMaps (W := W) p B a) :
    φ.val.toPointHom.ker = (mapKernel p B a φ).val.2.val :=
  point_kernel_eq_of_geometric_kernel_eq φ.val _ (mapKernel_spec p B a φ)

/-- The cyclic component of a sampled raw map, with precisely its original
target equation retained. -/
def connectingCyclicComponent (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0)
    (B : ℕ) (hdeg : ValidDegrees K B) (a : Target (K := K) p)
    (φ : ConnectingMaps (W := W) p B a) : Isogeny W (targetCurve p a).toAffine :=
  actualCyclicComponent ha₁ ha₃ B hdeg (mapKernel p B a φ).val φ.val
    (mapKernel_point_kernel p B a φ)

/-- The degree reported by the target-first observer is the genuine degree
of the cyclic component of the sampled raw map. -/
theorem observedDegree_eq_component_degree (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0)
    (B : ℕ) (hdeg : ValidDegrees K B) (a : Target (K := K) p)
    (φ : ConnectingMaps (W := W) p B a) :
    observedDegree p ha₁ ha₃ B hdeg ⟨a, some φ⟩ =
      some (connectingCyclicComponent p ha₁ ha₃ B hdeg a φ).degree := by
  simp only [observedDegree, sampledKernel, Option.map_some, quotientIsogeny_degree]
  exact congrArg some
    (actualCyclicComponent_spec ha₁ ha₃ B hdeg (mapKernel p B a φ).val φ.val
      (mapKernel_point_kernel p B a φ)).2.1.symm

/-- Actual cyclic-component output, retaining the selected target even when
the connecting fiber is empty and the result is failure. -/
def sampledCyclicComponent (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0)
    (B : ℕ) (hdeg : ValidDegrees K B) (x : Outcome (W := W) p B) :
    Option (Isogeny W (targetCurve p x.1).toAffine) :=
  x.2.map (connectingCyclicComponent p ha₁ ha₃ B hdeg x.1)

/-- On every outcome, including failure, the formal observer is exactly the
degree of the actual algebraic cyclic-component output. -/
theorem observedDegree_eq_sampledCyclicComponent (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0)
    (B : ℕ) (hdeg : ValidDegrees K B) (x : Outcome (W := W) p B) :
    observedDegree p ha₁ ha₃ B hdeg x =
      (sampledCyclicComponent p ha₁ ha₃ B hdeg x).map Isogeny.degree := by
  rcases x with ⟨a, x⟩
  cases x with
  | none => rfl
  | some φ => exact observedDegree_eq_component_degree p ha₁ ha₃ B hdeg a φ

/-- The sampled map factors through multiplication and the actual cyclic
component; the component's point kernel is the computed scalar strip. -/
theorem connectingCyclicComponent_spec (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0)
    (B : ℕ) (hdeg : ValidDegrees K B) (a : Target (K := K) p)
    (φ : ConnectingMaps (W := W) p B a) :
    let S := (mapKernel p B a φ).val
    let χ := connectingCyclicComponent p ha₁ ha₃ B hdeg a φ
    χ.comp (Isogeny.mulByIntIsogenyOfNeZero W
      (show ((actualKernelEquiv ha₁ ha₃ B hdeg S).val.content : ℤ) ≠ 0 by
        exact_mod_cast (actualKernelEquiv ha₁ ha₃ B hdeg S).val.content_pos.ne')) = φ.val ∧
    χ.toPointHom.ker = actualStrip ha₁ ha₃ B hdeg S ∧
    IsAddCyclic χ.toPointHom.ker ∧
    Algebra.IsSeparable χ.fieldPullback.fieldRange W.FunctionField := by
  have hs := actualCyclicComponent_spec ha₁ ha₃ B hdeg (mapKernel p B a φ).val φ.val
    (mapKernel_point_kernel p B a φ)
  exact ⟨hs.1, hs.2.2.2.1, hs.2.2.2.2⟩

end RawTargetSampler
end
end IsogenyAttack
