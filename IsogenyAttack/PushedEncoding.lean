import IsogenyAttack.PublicFullAttack

/-!
Valid public encodings of the concrete Algorithm 6 output instantiate the
public attack's encoding channels. Degree preservation is derived from the
actual geometric construction; it is not a field of the encoding witness.
-/
namespace IsogenyAttack.PushedEncoding

open WeierstrassCurve WeierstrassCurve.Affine TauCeti
open IsogenyPush PublicObservation PublicFullAttack

noncomputable section
open scoped Classical
attribute [local instance] Isogeny.isSeparable_comp

variable {K : Type*} [Field K] [IsAlgClosed K]
    {W M : Affine K} [W.IsElliptic] [M.IsElliptic]

/-- A string represents the actual first map produced by Algorithm 6 from
`first`. The witness consists of actual elliptic curves and isogenies, the
allowed fresh cyclic two-primary draw, and the public representation validator.
In particular, it contains no equality between the output degree and the input
degree. -/
def RepresentsPush (E : PolynomialDegreeDecoder) (first : Isogeny W M)
    [Algebra.IsSeparable first.fieldPullback.fieldRange W.FunctionField]
    (D : List Bool) : Prop :=
  ∃ (U V : Affine K) (hU : U.IsElliptic) (hV : V.IsElliptic),
    letI := hU
    letI := hV
    ∃ (second : Isogeny M U) (σ : Isogeny W V),
      ∃ hsep : Algebra.IsSeparable second.fieldPullback.fieldRange M.FunctionField,
        letI := hsep
        ∃ (_ : IsAddCyclic second.toPointHom.ker)
          (_ : first.degree.Coprime second.degree)
          (k n d : ℕ) (_ : σ.degree = 2 ^ k) (_ : Odd d)
          (_ : (second.comp first).degree = 2 ^ n * d)
          (R : AddSubgroup (quotientCurve V
            ((degreeSubgroup (second.comp first).toPointHom.ker d).map
              (pointHom σ))).toAffine.Point),
          ∃ hfin : Finite R,
            letI := hfin
            ∃ (_ : IsAddCyclic R) (_ : Nat.card R = 2 ^ n),
              E.toDegreeDecoder.Represents D
                (algorithm6First σ (degreeSubgroup (second.comp first).toPointHom.ker d)
                  R first.degree)

/-- Validation of the concrete pushed representation yields the original
actual first-map degree, by the proved Algorithm 6 degree theorem. -/
theorem representsPush_degree (E : PolynomialDegreeDecoder) (first : Isogeny W M)
    [Algebra.IsSeparable first.fieldPullback.fieldRange W.FunctionField]
    [IsAddCyclic first.toPointHom.ker]
    (D : List Bool) (hD : RepresentsPush E first D) :
    E.degree D = some first.degree := by
  rcases hD with ⟨U, V, hU, hV, second, σ, hsep, hcyc, hcop,
    k, n, d, hσ, hd, hφ, R, hfin, hRcyc, hR, hrepr⟩
  let := hU
  let := hV
  let := hsep
  let := hcyc
  let := hfin
  let := hRcyc
  have : IsAddCyclic (second.comp first).toPointHom.ker :=
    cyclic_isogeny_comp second first hcop
  have hc : first.degree ∣ (second.comp first).degree := by
    rw [Isogeny.degree_comp]
    exact Nat.dvd_mul_left _ _
  have hdegree := algorithm6First_degree_of_input (second.comp first) σ
    k n d first.degree hσ hd hφ hc R hR
  change E.degree D = some
    (algorithm6First σ (degreeSubgroup (second.comp first).toPointHom.ker d)
      R first.degree).degree at hrepr
  rw [hdegree] at hrepr
  exact hrepr

theorem decoded_push (E : PolynomialDegreeDecoder) (first : Isogeny W M)
    [Algebra.IsSeparable first.fieldPullback.fieldRange W.FunctionField]
    [IsAddCyclic first.toPointHom.ker]
    (D : List Bool) (hD : RepresentsPush E first D) :
    decoded E (some D) = some first.degree :=
  representsPush_degree E first D hD

@[simp] theorem decoded_failure (E : PolynomialDegreeDecoder) : decoded E none = none := rfl

section DegreeFirst
variable [NeZero (2 : K)]

/-- The degree-first experiment returns failure at its specified endpoint;
otherwise the public string represents the actual pushed cyclic component. -/
def DegreeOutput (E : PolynomialDegreeDecoder) (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0)
    (B : ℕ) (hdeg : ValidDegrees K B) (x : RawDegreeSampler.Outcome W B)
    (code : Option (List Bool)) : Prop :=
  if x.1.val < B then
    ∃ D, code = some D ∧ RepresentsPush E (RawDegreeGeometry.component ha₁ ha₃ B hdeg x) D
  else code = none

/-- The encoding contract required by the finite attack theorem is a
consequence of the actual Algorithm 6 construction and failure convention. -/
theorem degreeOutput_decoded (E : PolynomialDegreeDecoder)
    (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0) (B : ℕ) (hdeg : ValidDegrees K B)
    (x : RawDegreeSampler.Outcome W B) (code : Option (List Bool))
    (hcode : DegreeOutput E ha₁ ha₃ B hdeg x code) :
    decoded E code = RawDegreeGeometry.observation ha₁ ha₃ B hdeg x := by
  by_cases hx : x.1.val < B
  · obtain ⟨D, rfl, hD⟩ := (show ∃ D, code = some D ∧
        RepresentsPush E (RawDegreeGeometry.component ha₁ ha₃ B hdeg x) D by
      simpa only [DegreeOutput, hx, ↓reduceIte] using hcode)
    have : IsAddCyclic (RawDegreeGeometry.component ha₁ ha₃ B hdeg x).toPointHom.ker :=
      RawDegreeGeometry.component_cyclic ha₁ ha₃ B hdeg x
    simpa only [RawDegreeGeometry.observation, hx, ↓reduceIte] using
      decoded_push E (RawDegreeGeometry.component ha₁ ha₃ B hdeg x) D hD
  · have hc : code = none := by simpa only [DegreeOutput, hx, ↓reduceIte] using hcode
    simp only [hc, decoded_failure, RawDegreeGeometry.observation, hx, ↓reduceIte]

/-- Any finite randomization of the complement, challenge, fresh kernel, and
valid actual-output representation produces an admissible encoding channel.
Only the semantic actual-output witnesses are supplied by the caller. -/
def degreeChannel (E : PolynomialDegreeDecoder)
    (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0) (B : ℕ) (hdeg : ValidDegrees K B)
    (coins : RawDegreeSampler.Outcome W B → Type)
    [∀ x, Fintype (coins x)] (law : ∀ x, FiniteLaw (coins x))
    (encode : ∀ x, coins x → Option (List Bool))
    (hencode : ∀ x r, DegreeOutput E ha₁ ha₃ B hdeg x (encode x r)) :
    EncodingChannel E (RawDegreeGeometry.observation ha₁ ha₃ B hdeg) where
  coins := coins
  finite _ := inferInstance
  law := law
  encode := encode
  valid x r := degreeOutput_decoded E ha₁ ha₃ B hdeg x (encode x r) (hencode x r)

/-- The literal Algorithm 5 completion: success is decided by the actual
cyclic-component degree. Thus a noncyclic raw endpoint map remains successful
when its stripped component has degree below B. -/
def SourceDegreeOutput (E : PolynomialDegreeDecoder)
    (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0)
    (B : ℕ) (hdeg : ValidDegrees K B) (x : RawDegreeSampler.Outcome W B)
    (code : Option (List Bool)) : Prop :=
  if (RawDegreeGeometry.component ha₁ ha₃ B hdeg x).degree < B then
    ∃ D, code = some D ∧ RepresentsPush E (RawDegreeGeometry.component ha₁ ha₃ B hdeg x) D
  else code = none

theorem sourceDegreeOutput_decoded (E : PolynomialDegreeDecoder)
    (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0) (B : ℕ) (hdeg : ValidDegrees K B)
    (x : RawDegreeSampler.Outcome W B) (code : Option (List Bool))
    (hcode : SourceDegreeOutput E ha₁ ha₃ B hdeg x code) :
    decoded E code = if (RawDegreeGeometry.component ha₁ ha₃ B hdeg x).degree < B then
      some (RawDegreeGeometry.component ha₁ ha₃ B hdeg x).degree else none := by
  by_cases hx : (RawDegreeGeometry.component ha₁ ha₃ B hdeg x).degree < B
  · obtain ⟨D, rfl, hD⟩ := (show ∃ D, code = some D ∧
        RepresentsPush E (RawDegreeGeometry.component ha₁ ha₃ B hdeg x) D by
      simpa only [SourceDegreeOutput, hx, ↓reduceIte] using hcode)
    have : IsAddCyclic (RawDegreeGeometry.component ha₁ ha₃ B hdeg x).toPointHom.ker :=
      RawDegreeGeometry.component_cyclic ha₁ ha₃ B hdeg x
    simpa only [hx, ↓reduceIte] using
      decoded_push E (RawDegreeGeometry.component ha₁ ha₃ B hdeg x) D hD
  · have hc : code = none := by simpa only [SourceDegreeOutput, hx, ↓reduceIte] using hcode
    simp only [hc, decoded_failure, hx, ↓reduceIte]

/-- The channel for the source's completed Algorithm 5 distribution. Its
degree function is definitionally `SourceEndpoint.sourceObservation`; writing
the expression here keeps the geometry/encoding construction independent of
the subsequent endpoint probability comparison. -/
def sourceDegreeChannel (E : PolynomialDegreeDecoder)
    (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0) (B : ℕ) (hdeg : ValidDegrees K B)
    (coins : RawDegreeSampler.Outcome W B → Type)
    [∀ x, Fintype (coins x)] (law : ∀ x, FiniteLaw (coins x))
    (encode : ∀ x, coins x → Option (List Bool))
    (hencode : ∀ x r, SourceDegreeOutput E ha₁ ha₃ B hdeg x (encode x r)) :
    EncodingChannel E (fun x : RawDegreeSampler.Outcome W B =>
      if (RawDegreeGeometry.component ha₁ ha₃ B hdeg x).degree < B then
        some (RawDegreeGeometry.component ha₁ ha₃ B hdeg x).degree else none) where
  coins := coins
  finite _ := inferInstance
  law := law
  encode := encode
  valid x r := sourceDegreeOutput_decoded E ha₁ ha₃ B hdeg x (encode x r) (hencode x r)

end DegreeFirst

section TargetFirst
variable [NeZero (2 : K)] (p : ℕ) [Fact p.Prime] [CharP K p]
    [Algebra (ZMod p) K] [Algebra.IsAlgebraic (ZMod p) K]

/-- The target-first experiment preserves failure, and otherwise encodes
the actual pushed cyclic component of its sampled connecting isogeny. -/
def TargetOutput (E : PolynomialDegreeDecoder) (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0)
    (B : ℕ) (hdeg : ValidDegrees K B) (x : RawTargetSampler.Outcome (W := W) p B)
    (code : Option (List Bool)) : Prop :=
  match x.2 with
  | none => code = none
  | some φ =>
    letI := (RawTargetSampler.connectingCyclicComponent_spec p ha₁ ha₃ B hdeg x.1 φ).2.2.2
    ∃ D, code = some D ∧
      RepresentsPush E (RawTargetSampler.connectingCyclicComponent p ha₁ ha₃ B hdeg x.1 φ) D

theorem targetOutput_decoded (E : PolynomialDegreeDecoder)
    (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0) (B : ℕ) (hdeg : ValidDegrees K B)
    (x : RawTargetSampler.Outcome (W := W) p B) (code : Option (List Bool))
    (hcode : TargetOutput p E ha₁ ha₃ B hdeg x code) :
    decoded E code = RawTargetSampler.observedDegree p ha₁ ha₃ B hdeg x := by
  rcases x with ⟨a, x⟩
  cases x with
  | none =>
    change code = none at hcode
    rw [hcode]
    rfl
  | some φ =>
    have hs := RawTargetSampler.connectingCyclicComponent_spec p ha₁ ha₃ B hdeg a φ
    let := hs.2.2.2
    let := hs.2.2.1
    obtain ⟨D, rfl, hD⟩ := hcode
    rw [RawTargetSampler.observedDegree_eq_component_degree]
    exact decoded_push E (RawTargetSampler.connectingCyclicComponent p ha₁ ha₃ B hdeg a φ) D hD

def targetChannel (E : PolynomialDegreeDecoder)
    (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0) (B : ℕ) (hdeg : ValidDegrees K B)
    (coins : RawTargetSampler.Outcome (W := W) p B → Type)
    [∀ x, Fintype (coins x)] (law : ∀ x, FiniteLaw (coins x))
    (encode : ∀ x, coins x → Option (List Bool))
    (hencode : ∀ x r, TargetOutput p E ha₁ ha₃ B hdeg x (encode x r)) :
    EncodingChannel E (RawTargetSampler.observedDegree p ha₁ ha₃ B hdeg) where
  coins := coins
  finite _ := inferInstance
  law := law
  encode := encode
  valid x r := targetOutput_decoded p E ha₁ ha₃ B hdeg x (encode x r) (hencode x r)

end TargetFirst

end
end IsogenyAttack.PushedEncoding
