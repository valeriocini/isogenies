import IsogenyAttack.MontgomeryMorphismDescent
import IsogenyAttack.IsogenySampler
import IsogenyAttack.FiniteMontgomerySampler
import IsogenyAttack.TargetSampler
import IsogenyAttack.RawTargetGeometry
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.BaseChange.Separability
import Mathlib.FieldTheory.IntermediateField.Algebraic
import Mathlib.Algebra.Algebra.ZMod

/-! Actual finite-field and geometric isogeny sample spaces are bijective.
The bijections are base change, preserve degree and separability, and transport
uniform finite-family laws exactly, including empty-fiber failure. -/

namespace IsogenyAttack

namespace FiniteLaw

/-- Uniform sampling with an explicit empty-type failure is invariant under a
bijection. No nonemptiness hypothesis or rejection of the initial target is used. -/
theorem uniformOrFailure_event_equiv {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (E : Option β → Prop) :
    (uniformOrFailure α).eventMass (fun x => E (x.map e)) =
      (uniformOrFailure β).eventMass E := by
  classical
  rw [eventMass_eq_sum, eventMass_eq_sum]
  apply Fintype.sum_equiv (Equiv.optionCongr e)
  intro x
  cases x <;> simp [uniformOrFailure, Fintype.card_congr e]

end FiniteLaw

namespace RationalMapSampler

open WeierstrassCurve WeierstrassCurve.Affine TauCeti

noncomputable section
open scoped Classical

variable {F K : Type*} [Field F] [Fintype F] [Field K] [Algebra F K]
  [Algebra.IsAlgebraic F K] [IsGalois F K]

abbrev GroundMaps (A B : F) :=
  Isogeny (Montgomery.curve A).toAffine (Montgomery.curve B).toAffine

abbrev GeometricMaps (A B : F) :=
  Isogeny ((Montgomery.curve A).baseChange K).toAffine
    ((Montgomery.curve B).baseChange K).toAffine

variable (A B : F) (h2 : (2 : F) ≠ 0) (hA : A ^ 2 ≠ 4) (hB : B ^ 2 ≠ 4)
  (p : ℕ) [ExpChar F p] (hp : 0 < p) (hp4 : p % 4 = 3) (hcard : Nat.card F = p ^ 2)
  (hssA : (Montgomery.curve A).IsSupersingular p)
  (hssB : (Montgomery.curve B).IsSupersingular p)

/-- Base change is a bijection on actual isogenies between these supersingular
Montgomery curves. Surjectivity is proved descent, not a sampling assumption. -/
def baseChangeEquiv : GroundMaps A B ≃ GeometricMaps (K := K) A B :=
  Equiv.ofBijective (fun φ => φ.map (algebraMap F K)) (by
    constructor
    · intro φ ψ h
      exact (Montgomery.isogeny_descends A B h2 hA hB p hp hp4 hcard hssA hssB
        (φ.map (algebraMap F K))).unique rfl h.symm
    · intro φ
      exact (Montgomery.isogeny_descends A B h2 hA hB p hp hp4 hcard hssA hssB φ).exists)

@[simp] theorem baseChangeEquiv_apply (φ : GroundMaps A B) :
    baseChangeEquiv (K := K) A B h2 hA hB p hp hp4 hcard hssA hssB φ =
      φ.map (algebraMap F K) := rfl

@[simp] theorem baseChangeEquiv_degree (φ : GroundMaps A B) :
    (baseChangeEquiv (K := K) A B h2 hA hB p hp hp4 hcard hssA hssB φ).degree =
      φ.degree := Isogeny.degree_map φ _

theorem baseChangeEquiv_separable_iff (φ : GroundMaps A B) :
    Algebra.IsSeparable
      (baseChangeEquiv (K := K) A B h2 hA hB p hp hp4 hcard hssA hssB φ).fieldPullback.fieldRange
      ((Montgomery.curve A).baseChange K).toAffine.FunctionField ↔
    Algebra.IsSeparable φ.fieldPullback.fieldRange (Montgomery.curve A).toAffine.FunctionField := by
  let := Montgomery.curve_isElliptic h2 hA
  let := Montgomery.curve_isElliptic h2 hB
  exact Isogeny.isSeparable_map_iff φ (algebraMap F K)

/-- Any geometric family restricts to exactly the same family of finite-field
maps, with no stored geometric representative on the finite-field side. -/
def restrictedEquiv (P : GeometricMaps (K := K) A B → Prop) :
    {φ : GroundMaps A B // P (φ.map (algebraMap F K))} ≃
      {φ : GeometricMaps (K := K) A B // P φ} :=
  (baseChangeEquiv (K := K) A B h2 hA hB p hp hp4 hcard hssA hssB).subtypeEquiv
    (fun _ => Iff.rfl)

/-- Degree restrictions and separability are intrinsic on both sides. -/
def separableDegreesEquiv (D : Set ℕ) :
    {φ : GroundMaps A B //
      Algebra.IsSeparable φ.fieldPullback.fieldRange (Montgomery.curve A).toAffine.FunctionField ∧
      φ.degree ∈ D} ≃
    {φ : GeometricMaps (K := K) A B //
      Algebra.IsSeparable φ.fieldPullback.fieldRange
        ((Montgomery.curve A).baseChange K).toAffine.FunctionField ∧ φ.degree ∈ D} :=
  (baseChangeEquiv (K := K) A B h2 hA hB p hp hp4 hcard hssA hssB).subtypeEquiv (by
    intro φ
    rw [baseChangeEquiv_separable_iff, baseChangeEquiv_degree])

/-- Any finite geometric restricted family gives a finite family of actual
ground-field isogenies, by the proved equivalence. -/
@[reducible] def restrictedFintype (P : GeometricMaps (K := K) A B → Prop)
    [Fintype {φ : GeometricMaps (K := K) A B // P φ}] :
    Fintype {φ : GroundMaps A B // P (φ.map (algebraMap F K))} :=
  Fintype.ofEquiv _ (restrictedEquiv A B h2 hA hB p hp hp4 hcard hssA hssB P).symm

/-- Uniform conditional sampling, including failure on an empty family, has
exactly the same event probabilities before and after base change. -/
theorem restricted_uniformOrFailure_event (P : GeometricMaps (K := K) A B → Prop)
    [Fintype {φ : GeometricMaps (K := K) A B // P φ}]
    (E : Option {φ : GeometricMaps (K := K) A B // P φ} → Prop) :
    letI := restrictedFintype A B h2 hA hB p hp hp4 hcard hssA hssB P
    (FiniteLaw.uniformOrFailure {φ : GroundMaps A B // P (φ.map (algebraMap F K))}).eventMass
        (fun x => E (x.map (restrictedEquiv A B h2 hA hB p hp hp4 hcard hssA hssB P))) =
      (FiniteLaw.uniformOrFailure {φ : GeometricMaps (K := K) A B // P φ}).eventMass E := by
  let := restrictedFintype A B h2 hA hB p hp hp4 hcard hssA hssB P
  exact FiniteLaw.uniformOrFailure_event_equiv _ E

section KernelFamilies

variable [IsAlgClosed K] [(Montgomery.curve A).IsElliptic] [(Montgomery.curve B).IsElliptic]
  {ι : Type*} [Fintype ι]
  (S : ι → AddSubgroup ((Montgomery.curve A).baseChange K).toAffine.Point)
  [∀ i, Finite (S i)]

/-- A finite-field isogeny whose geometric kernel belongs to the specified
actual family. The data stored is just the finite-field rational map. -/
abbrev GroundFamilyMaps := {φ : GroundMaps A B //
  Nat.card (φ.map (algebraMap F K)).ker = (φ.map (algebraMap F K)).degree ∧
  ∃ i, (φ.map (algebraMap F K)).ker =
    quotientKernel ((Montgomery.curve A).baseChange K).toAffine (S i)}

/-- Forgetting the field of definition gives precisely the raw geometric
connecting-map family used by the sampler. -/
def familyEquiv : GroundFamilyMaps A B S ≃
    IsogenySampler.FamilyTargetMaps ((Montgomery.curve A).baseChange K).toAffine
      ((Montgomery.curve B).baseChange K) S :=
  restrictedEquiv (K := K) A B h2 hA hB p hp hp4 hcard hssA hssB
    (fun φ => Nat.card φ.ker = φ.degree ∧ ∃ i,
      φ.ker = quotientKernel ((Montgomery.curve A).baseChange K).toAffine (S i))

omit [IsAlgClosed K] [(Montgomery.curve B).IsElliptic] [Fintype ι] [∀ i, Finite (S i)] in
@[simp] theorem familyEquiv_map (φ : GroundFamilyMaps A B S) :
    (familyEquiv A B h2 hA hB p hp hp4 hcard hssA hssB S φ).val =
      φ.val.map (algebraMap F K) := rfl

omit [IsAlgClosed K] [(Montgomery.curve B).IsElliptic] [Fintype ι] [∀ i, Finite (S i)] in
@[simp] theorem familyEquiv_degree (φ : GroundFamilyMaps A B S) :
    (familyEquiv A B h2 hA hB p hp hp4 hcard hssA hssB S φ).val.degree =
      φ.val.degree := Isogeny.degree_map φ.val _

variable (hS : Function.Injective S)
  (hj : ∀ i, (quotientCurve ((Montgomery.curve A).baseChange K).toAffine (S i)).j =
    ((Montgomery.curve B).baseChange K).j)
  (h2K : (2 : K) ≠ 0) (h3K : (3 : K) ≠ 0)

/-- Finiteness is proved by the actual fixed-kernel map counts. -/
@[reducible] def familyGeometricFintype :
    Fintype (IsogenySampler.FamilyTargetMaps ((Montgomery.curve A).baseChange K).toAffine
      ((Montgomery.curve B).baseChange K) S) := by
  letI := IsogenySampler.familyTargetMaps_finite
    ((Montgomery.curve A).baseChange K).toAffine ((Montgomery.curve B).baseChange K)
    S hS hj h2K h3K
  exact Fintype.ofFinite _

/-- Thus the corresponding finite-field rational maps form a finite sample
space, without a separately assumed finite map space. -/
@[reducible] def familyGroundFintype : Fintype (GroundFamilyMaps A B S) := by
  letI := familyGeometricFintype A B S hS hj h2K h3K
  exact Fintype.ofEquiv _ (familyEquiv A B h2 hA hB p hp hp4 hcard hssA hssB S).symm

/-- Exact transfer of every event for the actual finite connecting-map
families. Empty families fail on both sides, preserving the chosen target. -/
theorem family_uniformOrFailure_event
    (E : Option (IsogenySampler.FamilyTargetMaps ((Montgomery.curve A).baseChange K).toAffine
      ((Montgomery.curve B).baseChange K) S) → Prop) :
    letI := familyGeometricFintype A B S hS hj h2K h3K
    letI := familyGroundFintype A B h2 hA hB p hp hp4 hcard hssA hssB S hS hj h2K h3K
    (FiniteLaw.uniformOrFailure (GroundFamilyMaps A B S)).eventMass
      (fun x => E (x.map (familyEquiv A B h2 hA hB p hp hp4 hcard hssA hssB S))) =
    (FiniteLaw.uniformOrFailure
      (IsogenySampler.FamilyTargetMaps ((Montgomery.curve A).baseChange K).toAffine
        ((Montgomery.curve B).baseChange K) S)).eventMass E := by
  let := familyGeometricFintype A B S hS hj h2K h3K
  let := familyGroundFintype A B h2 hA hB p hp hp4 hcard hssA hssB S hS hj h2K h3K
  exact FiniteLaw.uniformOrFailure_event_equiv _ E

end KernelFamilies

end

noncomputable section
open scoped Classical

/-- Transport of an actual isogeny along equality of its two curve equations. -/
def curveEquiv {L : Type*} [Field L] {U U' V V' : Affine L}
    (hU : U = U') (hV : V = V') : Isogeny U V ≃ Isogeny U' V' := by
  subst U'
  subst V'
  exact Equiv.refl _

@[simp] theorem curveEquiv_degree {L : Type*} [Field L] {U U' V V' : Affine L}
    (hU : U = U') (hV : V = V') (φ : Isogeny U V) :
    (curveEquiv hU hV φ).degree = φ.degree := by
  subst U'
  subst V'
  rfl

theorem curveEquiv_separable_iff {L : Type*} [Field L] {U U' V V' : Affine L}
    (hU : U = U') (hV : V = V') (φ : Isogeny U V) :
    Algebra.IsSeparable (curveEquiv hU hV φ).fieldPullback.fieldRange U'.FunctionField ↔
    Algebra.IsSeparable φ.fieldPullback.fieldRange U.FunctionField := by
  subst U'
  subst V'
  rfl

variable {K : Type*} [Field K] (p : ℕ) [Fact p.Prime] [CharP K p]

instance quadraticFieldFintype : Fintype (frobeniusFixedField (K := K) p 2) := by
  have := finite_frobeniusFixedField (K := K) p 2 (by decide)
  exact Fintype.ofFinite _

variable [IsAlgClosed K] [Algebra (ZMod p) K] [Algebra.IsAlgebraic (ZMod p) K]

instance quadraticFieldIsAlgebraic :
    Algebra.IsAlgebraic (frobeniusFixedField (K := K) p 2) K := by
  let F := frobeniusFixedField (K := K) p 2
  let := ZMod.algebra F p
  let : SMul (ZMod p) F := (inferInstance : Algebra (ZMod p) F).toSMul
  let : SMul F K := (inferInstance : Algebra F K).toSMul
  have : IsScalarTower (ZMod p) F K := IsScalarTower.of_algebraMap_eq
    (fun x => RingHom.congr_fun (Subsingleton.elim (algebraMap (ZMod p) K)
      ((algebraMap F K).comp (algebraMap (ZMod p) F))) x)
  exact Algebra.IsAlgebraic.tower_top (K := ZMod p) F

instance quadraticFieldIsGalois : IsGalois (frobeniusFixedField (K := K) p 2) K := by
  have : IsAlgClosure (frobeniusFixedField (K := K) p 2) K := ⟨inferInstance, inferInstance⟩
  exact IsGalois.mk

/-- The map-space equivalence over the explicit quadratic subfield, with
geometric curves written in exactly the coefficient form used by the raw
samplers. Algebraicity and the Galois condition are proved instances above. -/
def quadraticFieldEquiv (hp : 2 < p) (hp4 : p % 4 = 3)
    (a b : FiniteMontgomerySampler.Parameters (K := K) p) :
    GroundMaps a.val b.val ≃
      Isogeny (Montgomery.curve (a.val : K)).toAffine (Montgomery.curve (b.val : K)).toAffine :=
  (baseChangeEquiv (K := K) a.val b.val
    (Legendre.small_natCast_ne_zero p (k := 2) (by decide) (by omega))
    a.property.1 b.property.1 p (Fact.out : p.Prime).pos hp4
    (card_frobeniusFixedField (K := K) p 2 (by decide)) a.property.2 b.property.2).trans
  (curveEquiv
    (congrArg WeierstrassCurve.toAffine (Montgomery.curve_map (algebraMap _ K) a.val))
    (congrArg WeierstrassCurve.toAffine (Montgomery.curve_map (algebraMap _ K) b.val)))

@[simp] theorem quadraticFieldEquiv_degree (hp : 2 < p) (hp4 : p % 4 = 3)
    (a b : FiniteMontgomerySampler.Parameters (K := K) p) (φ : GroundMaps a.val b.val) :
    (quadraticFieldEquiv p hp hp4 a b φ).degree = φ.degree := by
  simp only [quadraticFieldEquiv, Equiv.trans_apply, curveEquiv_degree, baseChangeEquiv_degree]

theorem quadraticFieldEquiv_separable_iff (hp : 2 < p) (hp4 : p % 4 = 3)
    (a b : FiniteMontgomerySampler.Parameters (K := K) p) (φ : GroundMaps a.val b.val) :
    Algebra.IsSeparable (quadraticFieldEquiv p hp hp4 a b φ).fieldPullback.fieldRange
      (Montgomery.curve (a.val : K)).toAffine.FunctionField ↔
    Algebra.IsSeparable φ.fieldPullback.fieldRange (Montgomery.curve a.val).toAffine.FunctionField := by
  dsimp only [quadraticFieldEquiv, Equiv.trans_apply]
  exact (curveEquiv_separable_iff _ _ _).trans
    (baseChangeEquiv_separable_iff _ _ _ _ _ _ _ _ _ _ _ _)

variable [NeZero (2 : K)]

/-- Literally every finite-field rational map to the selected target whose
degree is strictly below the response bound. -/
abbrev QuadraticConnectingMaps (a b : FiniteMontgomerySampler.Parameters (K := K) p) (bound : ℕ) :=
  {φ : GroundMaps a.val b.val // φ.degree < bound}

/-- The target-first geometric connecting space is exactly all bounded
finite-field rational maps. The degree restriction makes separability automatic. -/
def quadraticConnectingEquiv (hp : 2 < p) (hp4 : p % 4 = 3)
    (a b : FiniteMontgomerySampler.Parameters (K := K) p) (bound : ℕ)
    (hdeg : ValidDegrees K bound) :
    QuadraticConnectingMaps p a b bound ≃
      RawTargetSampler.ConnectingMaps (W := (Montgomery.curve (a.val : K)).toAffine) p bound b :=
  ((quadraticFieldEquiv p hp hp4 a b).subtypeEquiv
    (fun φ => by rw [quadraticFieldEquiv_degree])).trans
      (RawTargetSampler.connectingMapsEquivAll
        (W := (Montgomery.curve (a.val : K)).toAffine) p bound hdeg b).symm

@[simp] theorem quadraticConnectingEquiv_degree (hp : 2 < p) (hp4 : p % 4 = 3)
    (a b : FiniteMontgomerySampler.Parameters (K := K) p) (bound : ℕ)
    (hdeg : ValidDegrees K bound) (φ : QuadraticConnectingMaps p a b bound) :
    (quadraticConnectingEquiv p hp hp4 a b bound hdeg φ).val.degree = φ.val.degree := by
  exact quadraticFieldEquiv_degree p hp hp4 a b φ.val

/-- Finiteness of the full bounded rational connecting-map space is derived
from the exact geometric sample space and its proved kernel multiplicities. -/
@[reducible] def quadraticConnectingFintype (hp : 3 < p) (hp4 : p % 4 = 3)
    (a b : FiniteMontgomerySampler.Parameters (K := K) p) (bound : ℕ)
    (hdeg : ValidDegrees K bound) : Fintype (QuadraticConnectingMaps p a b bound) := by
  letI := RawTargetSampler.connectingMapsFintype
    (W := (Montgomery.curve (a.val : K)).toAffine) p hp rfl rfl bound hdeg b
  exact Fintype.ofEquiv _ (quadraticConnectingEquiv p (by omega) hp4 a b bound hdeg).symm

/-- Uniform sampling among all actual bounded rational maps to a target,
with failure on an empty set, is exactly the raw target-first conditional law.
This is an equality for every event, rather than an assumed kernel law. -/
theorem quadraticConnecting_uniform_event (hp : 3 < p) (hp4 : p % 4 = 3)
    (a b : FiniteMontgomerySampler.Parameters (K := K) p) (bound : ℕ)
    (hdeg : ValidDegrees K bound)
    (E : Option (RawTargetSampler.ConnectingMaps
      (W := (Montgomery.curve (a.val : K)).toAffine) p bound b) → Prop) :
    letI := RawTargetSampler.connectingMapsFintype
      (W := (Montgomery.curve (a.val : K)).toAffine) p hp rfl rfl bound hdeg b
    letI := quadraticConnectingFintype p hp hp4 a b bound hdeg
    (FiniteLaw.uniformOrFailure (QuadraticConnectingMaps p a b bound)).eventMass
      (fun x => E (x.map (quadraticConnectingEquiv p (by omega) hp4 a b bound hdeg))) =
      (FiniteLaw.uniformOrFailure (RawTargetSampler.ConnectingMaps
        (W := (Montgomery.curve (a.val : K)).toAffine) p bound b)).eventMass E := by
  let := RawTargetSampler.connectingMapsFintype
    (W := (Montgomery.curve (a.val : K)).toAffine) p hp rfl rfl bound hdeg b
  let := quadraticConnectingFintype p hp hp4 a b bound hdeg
  exact FiniteLaw.uniformOrFailure_event_equiv _ E

/-- The target-first experiment written entirely with finite-field rational
maps. The chosen target is retained even when its connecting set is empty. -/
abbrev QuadraticTargetOutcome (a : FiniteMontgomerySampler.Parameters (K := K) p) (bound : ℕ) :=
  Σ b : FiniteMontgomerySampler.Parameters (K := K) p,
    Option (QuadraticConnectingMaps p a b bound)

def quadraticTargetOutcomeEquiv (hp : 2 < p) (hp4 : p % 4 = 3)
    (a : FiniteMontgomerySampler.Parameters (K := K) p) (bound : ℕ)
    (hdeg : ValidDegrees K bound) :
    QuadraticTargetOutcome p a bound ≃
      RawTargetSampler.Outcome (W := (Montgomery.curve (a.val : K)).toAffine) p bound :=
  Equiv.sigmaCongrRight (fun b => Equiv.optionCongr
    (quadraticConnectingEquiv p hp hp4 a b bound hdeg))

@[reducible] def quadraticTargetFintype (hp : 3 < p) (hp4 : p % 4 = 3)
    (a : FiniteMontgomerySampler.Parameters (K := K) p) (bound : ℕ)
    (hdeg : ValidDegrees K bound) : Fintype (QuadraticTargetOutcome p a bound) := by
  letI (b : FiniteMontgomerySampler.Parameters (K := K) p) :=
    quadraticConnectingFintype p hp hp4 a b bound hdeg
  infer_instance

def quadraticTargetLaw (hp : 3 < p) (hp4 : p % 4 = 3)
    (a : FiniteMontgomerySampler.Parameters (K := K) p) (bound : ℕ)
    (hdeg : ValidDegrees K bound) :
    @FiniteLaw (QuadraticTargetOutcome p a bound)
      (quadraticTargetFintype p hp hp4 a bound hdeg) := by
  letI (b : FiniteMontgomerySampler.Parameters (K := K) p) :=
    quadraticConnectingFintype p hp hp4 a b bound hdeg
  exact (FiniteMontgomerySampler.parameterLaw (K := K) p hp).dependentBind
    (fun b => Option (QuadraticConnectingMaps p a b bound))
    (fun b => FiniteLaw.uniformOrFailure (QuadraticConnectingMaps p a b bound))

/-- Every event of the entire target-first finite-field rational-map game
has exactly the probability computed by the raw geometric game. -/
theorem quadraticTargetLaw_event (hp : 3 < p) (hp4 : p % 4 = 3)
    (a : FiniteMontgomerySampler.Parameters (K := K) p) (bound : ℕ)
    (hdeg : ValidDegrees K bound)
    (E : RawTargetSampler.Outcome (W := (Montgomery.curve (a.val : K)).toAffine) p bound → Prop) :
    letI := quadraticTargetFintype p hp hp4 a bound hdeg
    letI := RawTargetSampler.outcomeFintype
      (W := (Montgomery.curve (a.val : K)).toAffine) p hp rfl rfl bound hdeg
    (quadraticTargetLaw p hp hp4 a bound hdeg).eventMass
      (fun x => E (quadraticTargetOutcomeEquiv p (by omega) hp4 a bound hdeg x)) =
      (RawTargetSampler.law
        (W := (Montgomery.curve (a.val : K)).toAffine) p hp rfl rfl bound hdeg).eventMass E := by
  let (b : FiniteMontgomerySampler.Parameters (K := K) p) :=
    quadraticConnectingFintype p hp hp4 a b bound hdeg
  let (b : FiniteMontgomerySampler.Parameters (K := K) p) :=
    RawTargetSampler.connectingMapsFintype
      (W := (Montgomery.curve (a.val : K)).toAffine) p hp rfl rfl bound hdeg b
  unfold quadraticTargetLaw RawTargetSampler.law
  rw [FiniteLaw.dependentBind_eventMass, FiniteLaw.dependentBind_eventMass]
  apply Finset.sum_congr rfl
  intro b _
  congr 1
  exact quadraticConnecting_uniform_event p hp hp4 a b bound hdeg (fun x => E ⟨b,x⟩)

end
end RationalMapSampler
end IsogenyAttack
