import IsogenyAttack.MontgomeryDescent
import IsogenyAttack.MontgomeryStationary
import IsogenyAttack.HasseSupersingular

/-! The sampler on actual supersingular Montgomery coefficients over the quadratic finite
field, with its explicit bijection to the geometric stationary parameter set. -/
namespace IsogenyAttack
open WeierstrassCurve

namespace FiniteLaw
/-- Uniform sampling is preserved by a bijection, for every event. -/
theorem uniform_event_equiv {α β : Type*} [Fintype α] [Fintype β]
    [Nonempty α] [Nonempty β] (e : α ≃ β) (E : β → Prop) :
    (uniform α).eventMass (fun a => E (e a)) = (uniform β).eventMass E := by
  classical
  rw [uniform_event, uniform_event,
    Fintype.card_congr (e.subtypeEquiv (fun _ => Iff.rfl)), Fintype.card_congr e]
end FiniteLaw

namespace Montgomery
@[simp] theorem curve_map {K L : Type*} [Field K] [Field L]
    (f : K →+* L) (a : K) : (curve a).map f = curve (f a) := by
  ext <;> simp [curve]
end Montgomery

namespace FiniteMontgomerySampler
open Montgomery Legendre

variable {K : Type*} [Field K] (p : ℕ) [Fact p.Prime] [CharP K p]

/-- Actual coefficients in the explicit field with `p²` elements, satisfying nonzero
discriminant and the geometric definition of supersingularity. -/
abbrev Parameters :=
  {a : frobeniusFixedField (K := K) p 2 //
    a^2 ≠ 4 ∧ (Montgomery.curve a).IsSupersingular p}

noncomputable instance parametersFintype : Fintype (Parameters (K := K) p) := by
  classical
  have := finite_frobeniusFixedField (K := K) p 2 (by decide)
  exact Fintype.ofFinite _

/-- The same coefficient locus over the algebraically closed ambient field. -/
abbrev GeometricParameters :=
  {a : K // a^2 ≠ 4 ∧ (Montgomery.curve a).IsSupersingular p}

theorem coefficient_isSupersingular_iff (hp : 2 < p)
    (a : frobeniusFixedField (K := K) p 2) (ha : a^2 ≠ 4) :
    (Montgomery.curve (a : K)).IsSupersingular p ↔
      (Montgomery.curve a).IsSupersingular p := by
  have := Montgomery.curve_isElliptic
    (small_natCast_ne_zero p (K := frobeniusFixedField (K := K) p 2)
      (k := 2) (by decide) hp) ha
  have hb : (Montgomery.curve a).baseChange K = Montgomery.curve (a : K) :=
    Montgomery.curve_map _ _
  rw [← hb, WeierstrassCurve.isSupersingular_baseChange_iff (Fact.out : p.Prime).ne_zero]

/-- Inclusion of the finite field is a bijection on supersingular normalized Montgomery
parameters; surjectivity is the marked-point descent theorem. -/
noncomputable def parametersEquivGeometric [IsAlgClosed K] (hp : 2 < p) :
    Parameters (K := K) p ≃ GeometricParameters (K := K) p :=
  Equiv.ofBijective
    (fun a => ⟨a.val.val,
      fun h => a.property.1 ((frobeniusFixedField (K := K) p 2).subtype.injective
        (by change a.val.val^2 = (4 : K); exact h)),
      (coefficient_isSupersingular_iff p hp a.val a.property.1).mpr a.property.2⟩)
    ⟨by
      intro a b h
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun x : GeometricParameters (K := K) p => x.val) h,
    by
      intro a
      have := Montgomery.curve_isElliptic
        (small_natCast_ne_zero p (k := 2) (by decide) hp) a.property.1
      let a₀ : frobeniusFixedField (K := K) p 2 :=
        ⟨a.val, Montgomery.supersingular_parameter_mem_quadraticField p
          (by omega) a.val a.property.2⟩
      have ha₀ : a₀^2 ≠ 4 := by
        intro h
        exact a.property.1 (congrArg Subtype.val h)
      exact ⟨⟨a₀, ha₀, (coefficient_isSupersingular_iff p hp a₀ ha₀).mp a.property.2⟩,
        Subtype.ext rfl⟩⟩

variable [IsAlgClosed K] [DecidableEq K]
  [Algebra (ZMod p) K] [Algebra.IsAlgebraic (ZMod p) K]

/-- Genuine supersingularity identifies this coefficient locus with the explicit Hasse
polynomial j-locus; no supersingularity assumption is hidden in the bijection. -/
noncomputable def geometricEquivLocus (hp : 2 < p) :
    GeometricParameters (K := K) p ≃
      MontgomeryStationary.ParameterLocus (K := K) ((p-1)/2) :=
  Equiv.subtypeEquivRight (by
    intro a
    apply and_congr_right
    intro ha
    have := Montgomery.curve_isElliptic
      (small_natCast_ne_zero p (k := 2) (by decide) hp) ha
    simpa only [Montgomery.curve_jInvariant] using
      Legendre.isSupersingular_iff_j_mem_hasse p hp (Montgomery.curve a))

/-- Explicit identification with the finite parameter set used by the stationary law. -/
noncomputable def parametersEquivStationary (hp : 3 < p) :
    Parameters (K := K) p ≃ MontgomeryStationary.Parameters (K := K) ((p-1)/2) :=
  (parametersEquivGeometric p (by omega)).trans
    ((geometricEquivLocus p (by omega)).trans
      (MontgomeryStationary.parametersEquivLocus ((p-1)/2)
        (small_natCast_ne_zero p (k := 2) (by decide) (by omega))).symm)

theorem card_parameters (hp : 3 < p) :
    Fintype.card (Parameters (K := K) p) = (p-1)/2 := by
  rw [Fintype.card_congr (parametersEquivStationary p hp),
    MontgomeryStationary.card_parameters p hp]

theorem parameters_nonempty (hp : 3 < p) : Nonempty (Parameters (K := K) p) :=
  Fintype.card_pos_iff.mp (by rw [card_parameters p hp]; omega)

theorem parametersEquivStationary_coefficient (hp : 3 < p)
    (a : Parameters (K := K) p) :
    (parametersEquivStationary p hp a).2.val = a.val.val := by
  let e := MontgomeryStationary.parametersEquivLocus (K := K) ((p-1)/2)
    (small_natCast_ne_zero p (k := 2) (by decide) (by omega))
  have h := congrArg Subtype.val (e.apply_symm_apply
    (geometricEquivLocus p (by omega) (parametersEquivGeometric p (by omega) a)))
  exact h

/-- The j-class map records the actual j-invariant of the finite-field coefficient. -/
noncomputable def jMap (hp : 3 < p) (a : Parameters (K := K) p) :
    HasseJClass (K := K) ((p-1)/2) := (parametersEquivStationary p hp a).1

theorem jMap_val (hp : 3 < p) (a : Parameters (K := K) p) :
    (jMap p hp a).val = Montgomery.jInvariant a.val.val := by
  have h := GeometricMultiplicity.modelFiber_property
    (parametersEquivStationary p hp a).1.val
    (small_natCast_ne_zero p (k := 2) (by decide) (by omega))
    (parametersEquivStationary p hp a).2
  rw [parametersEquivStationary_coefficient] at h
  exact h.2.symm

/-- Uniform sampling of actual supersingular Montgomery coefficients over the field of
`p²` elements. -/
noncomputable def parameterLaw (hp : 3 < p) : FiniteLaw (Parameters (K := K) p) := by
  letI := parameters_nonempty (K := K) p hp
  exact FiniteLaw.uniform _

/-- The finite-field sampler has exactly the stationary Hasse j-marginal, including
both exceptional j-invariants. -/
theorem parameterLaw_j_mass (hp : 3 < p) (j : HasseJClass (K := K) ((p-1)/2)) :
    ((parameterLaw (K := K) p hp).pushForward (jMap p hp)).mass j =
      (hasseInvariantLaw (K := K) p (by omega)).mass j := by
  let := parameters_nonempty (K := K) p hp
  let := MontgomeryStationary.parameters_nonempty (K := K) p hp
  change (FiniteLaw.uniform (Parameters (K := K) p)).eventMass
    (fun a => (parametersEquivStationary p hp a).1 = j) = _
  rw [FiniteLaw.uniform_event_equiv (parametersEquivStationary p hp)
    (fun a => a.1 = j)]
  exact MontgomeryStationary.parameterLaw_j_mass p hp j

end FiniteMontgomerySampler
end IsogenyAttack
