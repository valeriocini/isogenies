import IsogenyAttack.IsogenyPush
import IsogenyAttack.Experiments

/-! Public degree observation, including the representation decoder's running
cost and arbitrary randomized valid encodings. The decoder assumptions are the
public representation specification; no probability or distinguishing premise
is included in them. Work uses the explicit Boolean/list charge of BitComplexity. -/

namespace IsogenyAttack
namespace PublicObservation

open BitComplexity

/-- A degree validator with a polynomial work guarantee. Emitting an output
bit costs at least one unit, so its output length is bounded by its charged work.
The exponent is positive without loss of generality for polynomial bounds. -/
structure PolynomialDegreeDecoder where
  decode : List Bool → BitComplexity.Computation (Option (List Bool))
  coefficient : ℕ
  exponent : ℕ
  work_le : ∀ D, (decode D).work ≤ coefficient * (D.length + 1) ^ (exponent + 1)
  output_length_le_work : ∀ D,
    ((decode D).result.map List.length).getD 0 ≤ (decode D).work

def PolynomialDegreeDecoder.toDegreeDecoder (E : PolynomialDegreeDecoder) :
    IsogenyPush.DegreeDecoder := ⟨fun D => (E.decode D).result⟩

def PolynomialDegreeDecoder.degree (E : PolynomialDegreeDecoder) (D : List Bool) : Option ℕ :=
  (E.decode D).result.map value

/-- The public adversary first validates/decodes, then performs the certified
binary threshold test. Its work includes both calls and the sequencing charge. -/
def program (E : PolynomialDegreeDecoder) (B s D : List Bool) : BitComplexity.Computation Bool :=
  let decoded := E.decode D
  let tested := testBitsOption B s decoded.result
  ⟨tested.result, decoded.work + tested.work + 1⟩

theorem program_correct (E : PolynomialDegreeDecoder) (B s D : List Bool)
    (hs : 0 < value s) :
    (program E B s D).result = publicTest (value B) (value s) (E.degree D) :=
  testBitsOption_correct B s _ hs

theorem program_rejects_failure (E : PolynomialDegreeDecoder) (B s D : List Bool)
    (hD : (E.decode D).result = none) : (program E B s D).result = false := by
  simp [program, hD, testBitsOption]

theorem program_of_representation {K : Type*} [Field K]
    {W V : WeierstrassCurve.Affine K}
    (E : PolynomialDegreeDecoder) (B s D : List Bool)
    (φ : TauCeti.Isogeny W V) (hD : E.toDegreeDecoder.Represents D φ)
    (hs : 0 < value s) :
    (program E B s D).result = publicTest (value B) (value s) (some φ.degree) := by
  rw [program_correct E B s D hs]
  exact congrArg (publicTest (value B) (value s)) hD

/-- A direct composed bound, retaining the decoder's precise input length. -/
theorem program_work_le (E : PolynomialDegreeDecoder) (B s D : List Bool) :
    (program E B s D).work ≤
      E.coefficient * (D.length + 1) ^ (E.exponent + 1) +
      8192 * (B.length + s.length +
        E.coefficient * (D.length + 1) ^ (E.exponent + 1) + 1) ^ 2 + 2 := by
  have hw := E.work_le D
  have hl := (E.output_length_le_work D).trans hw
  have ht := testBitsOption_work_le B s (E.decode D).result
  have hm := Nat.pow_le_pow_left (show
      B.length + s.length + ((E.decode D).result.map List.length).getD 0 + 1 ≤
      B.length + s.length + E.coefficient * (D.length + 1) ^ (E.exponent + 1) + 1
      by omega) 2
  dsimp only [program]
  omega

/-- A single monomial bound in the total public input length. In particular,
the decoder's polynomial cost and the quadratic arithmetic test compose to
polynomial cost without assuming that an encoded degree has bounded value. -/
theorem program_work_polynomial (E : PolynomialDegreeDecoder) (B s D : List Bool) :
    (program E B s D).work ≤
      (E.coefficient + 8192 * (E.coefficient + 1) ^ 2 + 2) *
      (B.length + s.length + D.length + 1) ^ (2 * (E.exponent + 1)) := by
  let L := B.length + s.length + D.length + 1
  let N := L ^ (E.exponent + 1)
  have hL : 1 ≤ L := by dsimp [L]; omega
  have hLpow : 1 ≤ L ^ E.exponent := one_le_pow₀ hL
  have hLN : L ≤ N := by dsimp [N]; rw [pow_succ]; nlinarith
  have hN : 1 ≤ N := hL.trans hLN
  have hNN : N ≤ N ^ 2 := by nlinarith
  have hd : (D.length + 1) ^ (E.exponent + 1) ≤ N :=
    Nat.pow_le_pow_left (by dsimp [L]; omega) _
  have hc := Nat.mul_le_mul_left E.coefficient hd
  have hh : B.length + s.length + E.coefficient * (D.length + 1) ^ (E.exponent + 1) + 1 ≤
      (E.coefficient + 1) * N := by dsimp [L] at hLN; nlinarith
  have hsquare := Nat.pow_le_pow_left hh 2
  have hwork := program_work_le E B s D
  have hCN := Nat.mul_le_mul_left E.coefficient hNN
  have hN2 : 1 ≤ N ^ 2 := by nlinarith
  have he : L ^ (2 * (E.exponent + 1)) = N ^ 2 := by
    dsimp [N]
    rw [Nat.mul_comm 2, pow_mul]
  change (program E B s D).work ≤
    (E.coefficient + 8192 * (E.coefficient + 1) ^ 2 + 2) * L ^ (2 * (E.exponent + 1))
  rw [he]
  nlinarith

end PublicObservation

namespace FiniteLaw

open scoped BigOperators

/-- Arbitrary dependent randomization preserving an observed optional degree
preserves every Boolean test on that degree exactly. Failure is the `none`
observation and requires no conditioning or resampling. -/
theorem dependentBind_degree_observation {α : Type*} [Fintype α]
    (P : FiniteLaw α) (β : α → Type*) [∀ a, Fintype (β a)]
    (Q : ∀ a, FiniteLaw (β a)) (degree : α → Option ℕ)
    (observed : (Sigma β) → Option ℕ) (test : Option ℕ → Bool)
    (hdegree : ∀ a b, observed ⟨a,b⟩ = degree a) :
    (P.dependentBind β Q).eventMass (fun x => test (observed x) = true) =
      P.eventMass (fun a => test (degree a) = true) := by
  classical
  rw [dependentBind_eventMass, eventMass_eq_sum]
  apply Finset.sum_congr rfl
  intro a _
  have hc : (Q a).eventMass (fun b => test (observed ⟨a,b⟩) = true) =
      if test (degree a) = true then 1 else 0 := by
    simp_rw [hdegree a]
    by_cases h : test (degree a) = true <;> simp [h]
  rw [hc]
  split_ifs <;> simp

/-- Any finite randomized encoding whose decoder returns the actual optional
degree leaves the public program's acceptance probability exactly unchanged. -/
theorem dependentBind_public_program {α : Type*} [Fintype α]
    (P : FiniteLaw α) (β : α → Type*) [∀ a, Fintype (β a)]
    (Q : ∀ a, FiniteLaw (β a)) (degree : α → Option ℕ)
    (E : PublicObservation.PolynomialDegreeDecoder)
    (encode : (a : α) → β a → List Bool) (B s : List Bool)
    (hs : 0 < BitComplexity.value s)
    (hdegree : ∀ a b, E.degree (encode a b) = degree a) :
    (P.dependentBind β Q).eventMass
        (fun x => (PublicObservation.program E B s (encode x.1 x.2)).result = true) =
      P.eventMass (fun a => publicTest (BitComplexity.value B) (BitComplexity.value s)
        (degree a) = true) := by
  have he := dependentBind_degree_observation P β Q degree
    (fun x => E.degree (encode x.1 x.2))
    (publicTest (BitComplexity.value B) (BitComplexity.value s)) hdegree
  rw [← he]
  apply eventMass_congr
  intro x
  rw [PublicObservation.program_correct E B s _ hs]

end FiniteLaw
end IsogenyAttack
