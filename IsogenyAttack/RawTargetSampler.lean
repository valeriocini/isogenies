import IsogenyAttack.GenuineAttack
import IsogenyAttack.IsogenySampler
import IsogenyAttack.FiniteMontgomerySampler

/-! The target-first sampler on actual finite-field Montgomery coefficients
and actual connecting algebraic maps. Empty connecting fibers return failure
without resampling their target. -/
namespace IsogenyAttack.RawTargetSampler

open WeierstrassCurve WeierstrassCurve.Affine TauCeti
open IsogenySampler
open scoped BigOperators

noncomputable section
open scoped Classical

variable {K : Type*} [Field K] [IsAlgClosed K] [NeZero (2 : K)]
    {W : Affine K} [W.IsElliptic]

theorem actualKernel_subgroup_injective (B : ℕ) :
    Function.Injective (fun S : ActualKernel W.Point B => S.2.val) := by
  rintro ⟨⟨d, hd⟩, ⟨S, hS⟩⟩ ⟨⟨e, he⟩, ⟨T, hT⟩⟩ h
  dsimp at h
  subst T
  have hde : d = e := hS.symm.trans hT
  subst e
  rfl

variable (p : ℕ) [Fact p.Prime] [CharP K p]
    [Algebra (ZMod p) K] [Algebra.IsAlgebraic (ZMod p) K]

abbrev Target := FiniteMontgomerySampler.Parameters (K := K) p

abbrev targetCurve (a : Target (K := K) p) := Montgomery.curve (a.val : K)

instance targetCurve_elliptic (a : Target (K := K) p) : (targetCurve p a).IsElliptic := by
  apply Montgomery.curve_isElliptic (NeZero.ne (2 : K))
  intro h
  apply a.property.1
  exact (frobeniusFixedField (K := K) p 2).subtype.injective h

/-- All bounded subgroup kernels whose genuine quotient has the specified target. -/
abbrev ConnectingKernel (B : ℕ) (a : Target (K := K) p) :=
  {S : ActualKernel W.Point B // S.1.val < B ∧ (quotientCurve W S.2.val).j = (targetCurve p a).j}

def kernelFamily (B : ℕ) (a : Target (K := K) p)
    (S : ConnectingKernel (W := W) p B a) : AddSubgroup W.Point := S.val.2.val

theorem kernelFamily_injective (B : ℕ) (a : Target (K := K) p) :
    Function.Injective (kernelFamily (W := W) p B a) := by
  intro S T h
  exact Subtype.ext (actualKernel_subgroup_injective B h)

instance kernelFamily_finite (B : ℕ) (a : Target (K := K) p)
    (S : ConnectingKernel (W := W) p B a) : Finite (kernelFamily p B a S) := by
  exact actualKernel_finite S.val

/-- Unadorned genuine separable maps to the fixed target whose kernels occur
in the connecting family. The kernel index is recovered from the map. -/
abbrev ConnectingMaps (B : ℕ) (a : Target (K := K) p) :=
  FamilyTargetMaps W (targetCurve p a) (kernelFamily (W := W) p B a)

@[reducible] def connectingMapsFintype (hp : 3 < p) (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0)
    (B : ℕ) (hdeg : ValidDegrees K B) (a : Target (K := K) p) :
    Fintype (ConnectingMaps (W := W) p B a) := by
  letI := actualKernelFintype ha₁ ha₃ B hdeg
  letI : Finite (ConnectingMaps (W := W) p B a) :=
    familyTargetMaps_finite W (targetCurve p a) (kernelFamily p B a)
      (kernelFamily_injective p B a) (fun S => S.property.2)
      (NeZero.ne (2 : K)) (Legendre.small_natCast_ne_zero p (by decide) hp)
  exact Fintype.ofFinite _

def mapKernel (B : ℕ) (a : Target (K := K) p)
    (φ : ConnectingMaps (W := W) p B a) : ConnectingKernel (W := W) p B a :=
  familyTargetMapKernel W (targetCurve p a) (kernelFamily p B a)
    (kernelFamily_injective p B a) φ

theorem mapKernel_spec (B : ℕ) (a : Target (K := K) p)
    (φ : ConnectingMaps (W := W) p B a) :
    φ.val.ker = quotientKernel W (mapKernel p B a φ).val.2.val :=
  familyTargetMapKernel_spec W (targetCurve p a) (kernelFamily p B a)
    (kernelFamily_injective p B a) φ

theorem connectingMaps_degree_lt (B : ℕ) (a : Target (K := K) p)
    (φ : ConnectingMaps (W := W) p B a) : φ.val.degree < B := by
  rw [← φ.property.1, mapKernel_spec p B a φ]
  have hc := (Nat.card_congr ((Point.equivBaseChangeSelf W).addSubgroupMap
    (mapKernel p B a φ).val.2.val).toEquiv).symm
  change Nat.card (quotientKernel W (mapKernel p B a φ).val.2.val) = _ at hc
  rw [hc, (mapKernel p B a φ).val.2.property]
  exact (mapKernel p B a φ).property.1

abbrev Outcome (B : ℕ) := Σ a : Target (K := K) p, Option (ConnectingMaps (W := W) p B a)

@[reducible] def outcomeFintype (hp : 3 < p) (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0)
    (B : ℕ) (hdeg : ValidDegrees K B) : Fintype (Outcome (W := W) p B) := by
  letI (a : Target (K := K) p) := connectingMapsFintype p hp ha₁ ha₃ B hdeg a
  infer_instance

def law (hp : 3 < p) (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0)
    (B : ℕ) (hdeg : ValidDegrees K B) :
    @FiniteLaw (Outcome (W := W) p B) (outcomeFintype p hp ha₁ ha₃ B hdeg) := by
  letI (a : Target (K := K) p) := connectingMapsFintype p hp ha₁ ha₃ B hdeg a
  exact (FiniteMontgomerySampler.parameterLaw (K := K) p hp).dependentBind
    (fun a => Option (ConnectingMaps (W := W) p B a))
    (fun a => FiniteLaw.uniformOrFailure (ConnectingMaps (W := W) p B a))

/-- The sampled target class has the exact stationary law, even for empty
fibers, since the original target is never resampled. -/
theorem target_marginal (hp : 3 < p) (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0)
    (B : ℕ) (hdeg : ValidDegrees K B) (j : Legendre.HasseJClass (K := K) ((p-1)/2)) :
    letI := outcomeFintype p hp ha₁ ha₃ B hdeg
    (law p hp ha₁ ha₃ B hdeg).eventMass
      (fun x => FiniteMontgomerySampler.jMap p hp x.1 = j) =
      (Legendre.hasseInvariantLaw (K := K) p (by omega)).mass j := by
  letI (a : Target (K := K) p) := connectingMapsFintype p hp ha₁ ha₃ B hdeg a
  rw [law, FiniteLaw.dependentBind_eventMass]
  have h (a : Target (K := K) p) :
      (FiniteLaw.uniformOrFailure (ConnectingMaps (W := W) p B a)).eventMass
        (fun _ => FiniteMontgomerySampler.jMap p hp a = j) =
        if FiniteMontgomerySampler.jMap p hp a = j then 1 else 0 := by
    split_ifs with ha <;> simp [ha]
  simp_rw [h, mul_ite, mul_one, mul_zero]
  exact (FiniteLaw.eventMass_eq_sum _ _).symm.trans
    (FiniteMontgomerySampler.parameterLaw_j_mass p hp j)

/-- The actual bounded source kernel, if the connecting step succeeds. -/
def sampledKernel (B : ℕ) (x : Outcome (W := W) p B) : Option (ActualKernel W.Point B) :=
  x.2.map (fun φ => (mapKernel p B x.1 φ).val)

def componentCode (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0)
    (B : ℕ) (hdeg : ValidDegrees K B) (x : Outcome (W := W) p B) : Option HNF :=
  (sampledKernel p B x).map (recodedStrip ha₁ ha₃ B hdeg)

def observedDegree (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0)
    (B : ℕ) (hdeg : ValidDegrees K B) (x : Outcome (W := W) p B) : Option ℕ :=
  (sampledKernel p B x).map (fun S => (quotientIsogeny W (actualStrip ha₁ ha₃ B hdeg S)).degree)

@[simp] theorem componentCode_degree (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0)
    (B : ℕ) (hdeg : ValidDegrees K B) (x : Outcome (W := W) p B) :
    (componentCode p ha₁ ha₃ B hdeg x).map HNF.degree = observedDegree p ha₁ ha₃ B hdeg x := by
  simp only [componentCode, observedDegree, Option.map_map, Function.comp_def,
    recodedStrip_degree, quotientIsogeny_degree]

theorem componentCode_target (hp : 3 < p) (hW : W.IsSupersingular p)
    (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0) (B : ℕ) (hdeg : ValidDegrees K B)
    (x : Outcome (W := W) p B) (h : HNF) (hx : componentCode p ha₁ ha₃ B hdeg x = some h) :
    FiniteMontgomerySampler.jMap p hp x.1 =
      actualCodomainCode ha₁ ha₃ B hdeg (geometricTarget p (by omega) hW) h := by
  rcases x with ⟨a, x⟩
  cases x with
  | none => simp [componentCode, sampledKernel] at hx
  | some φ =>
    simp only [componentCode, sampledKernel, Option.map_some, Option.some.injEq] at hx
    rw [← hx, actualCodomainCode_recodedStrip, ← geometricTarget_actualStrip]
    apply Subtype.ext
    rw [geometricTarget_val p (by omega) hW _
      (actualKernel_coprime p hdeg (mapKernel p B a φ).val)]
    rw [(mapKernel p B a φ).property.2]
    exact (FiniteMontgomerySampler.jMap_val p hp a).trans
      (Montgomery.curve_jInvariant (a.val : K)).symm

end
end IsogenyAttack.RawTargetSampler
