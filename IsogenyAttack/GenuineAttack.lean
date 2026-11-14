import IsogenyAttack.ScalarStripGeometry
import IsogenyAttack.FullArithmeticAttack

/-!
# The attack with genuine algebraic quotient targets

The target map here is the j-invariant of the actual Vélu quotient. Scalar
stripping preserves this target by `actualStrip_quotient_j_eq`. Thus no
unspecified map from subgroups to target classes occurs in these experiments.
-/
namespace IsogenyAttack

open WeierstrassCurve WeierstrassCurve.Affine TauCeti
open scoped BigOperators

noncomputable section
open scoped Classical

variable {K : Type*} [Field K] [IsAlgClosed K]
    [NeZero (2 : K)] {W : Affine K} [W.IsElliptic]

theorem actualKernel_card_pos {B : ℕ} (S : ActualKernel W.Point B) :
    0 < Nat.card S.2.val := by
  rw [S.2.property]
  exact (Finset.mem_Icc.mp S.1.property).1

theorem actualKernel_coprime (p : ℕ) [Fact p.Prime] [CharP K p]
    {B : ℕ} (hdeg : ValidDegrees K B) (S : ActualKernel W.Point B) :
    Nat.Coprime p (Nat.card S.2.val) := by
  rw [S.2.property, (Fact.out : p.Prime).coprime_iff_not_dvd]
  intro hd
  exact hdeg S.1.val (Finset.mem_Icc.mp S.1.property).1
    (Finset.mem_Icc.mp S.1.property).2 ((CharP.cast_eq_zero_iff K p _).mpr hd)

/-- Actual quotient j-class. The fallback only makes the function total on
infinite or characteristic-divisible subgroups, which never occur in the
bounded experiments. -/
def geometricTarget (p : ℕ) [Fact p.Prime] [CharP K p]
    [Algebra (ZMod p) K] [Algebra.IsAlgebraic (ZMod p) K]
    (hp : 2 < p) (hW : W.IsSupersingular p) (S : AddSubgroup W.Point) :
    Legendre.HasseJClass (K := K) ((p-1)/2) :=
  if h : Nat.card S ≠ 0 ∧ Nat.Coprime p (Nat.card S) then
    letI : Finite S := Nat.finite_of_card_ne_zero h.1
    quotientJClass W p hp hW S h.2
  else
    ⟨W.j, (Legendre.isSupersingular_iff_j_mem_hasse p hp W).mp hW⟩

theorem geometricTarget_val (p : ℕ) [Fact p.Prime] [CharP K p]
    [Algebra (ZMod p) K] [Algebra.IsAlgebraic (ZMod p) K]
    (hp : 2 < p) (hW : W.IsSupersingular p)
    (S : AddSubgroup W.Point) [Finite S] (hcop : Nat.Coprime p (Nat.card S)) :
    (geometricTarget p hp hW S).val = (quotientCurve W S).j := by
  rw [geometricTarget, dif_pos ⟨Nat.card_ne_zero.mpr ⟨inferInstance, inferInstance⟩, hcop⟩]
  rfl

/-- The target checked before stripping is exactly the target after stripping. -/
theorem geometricTarget_actualStrip (p : ℕ) [Fact p.Prime] [CharP K p]
    [Algebra (ZMod p) K] [Algebra.IsAlgebraic (ZMod p) K]
    (hp : 2 < p) (hW : W.IsSupersingular p)
    (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0) (B : ℕ) (hdeg : ValidDegrees K B)
    (S : ActualKernel W.Point B) :
    geometricTarget p hp hW S.2.val =
      geometricTarget p hp hW (actualStrip ha₁ ha₃ B hdeg S) := by
  apply Subtype.ext
  have hcop : Nat.Coprime p (Nat.card (actualStrip ha₁ ha₃ B hdeg S)) :=
    actualKernel_coprime p hdeg (actualStripBounded ha₁ ha₃ B hdeg S)
  rw [geometricTarget_val p hp hW _ (actualKernel_coprime p hdeg S),
    geometricTarget_val p hp hW _ hcop]
  exact actualStrip_quotient_j_eq ha₁ ha₃ B hdeg S

/-- A target-first connecting fiber can equivalently be tested on the
unstripped algebraic quotient, exactly as in the original sampling order. -/
theorem genuine_connecting_iff (p : ℕ) [Fact p.Prime] [CharP K p]
    [Algebra (ZMod p) K] [Algebra.IsAlgebraic (ZMod p) K]
    (hp : 2 < p) (hW : W.IsSupersingular p)
    (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0) (B : ℕ) (hdeg : ValidDegrees K B)
    (t : Legendre.HasseJClass (K := K) ((p-1)/2)) (S : ActualKernel W.Point B) :
    (S.1.val < B ∧ geometricTarget p hp hW (actualStrip ha₁ ha₃ B hdeg S) = t) ↔
      (S.1.val < B ∧ (quotientCurve W S.2.val).j = t.val) := by
  rw [← geometricTarget_actualStrip p hp hW ha₁ ha₃ B hdeg S]
  have h := geometricTarget_val p hp hW S.2.val (actualKernel_coprime p hdeg S)
  constructor
  · rintro ⟨hd, ht⟩
    exact ⟨hd, h.symm.trans (congrArg Subtype.val ht)⟩
  · rintro ⟨hd, ht⟩
    exact ⟨hd, Subtype.ext (h.trans ht)⟩

/-- Publicly exposed degree, with failure at the printed endpoint d = B.
All interior outputs are degrees of genuine cyclic quotient isogenies. -/
def genuineDegreeObservation (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0)
    (B : ℕ) (hdeg : ValidDegrees K B) (S : ActualKernel W.Point B) : Option ℕ :=
  if S.1.val < B then some (quotientIsogeny W (actualStrip ha₁ ha₃ B hdeg S)).degree
  else none

theorem genuineDegreeObservation_interior (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0)
    (B : ℕ) (hdeg : ValidDegrees K B) (S : ActualKernel W.Point B)
    (hS : S.1.val < B) :
    genuineDegreeObservation ha₁ ha₃ B hdeg S =
      some (actualKernelEquiv ha₁ ha₃ B hdeg S).val.cyclicDegree := by
  simp only [genuineDegreeObservation, if_pos hS, quotientIsogeny_degree, actualStrip_card]

theorem genuineDegreeObservation_le (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0)
    (B : ℕ) (hdeg : ValidDegrees K B) (S : ActualKernel W.Point B) (c : ℕ)
    (hc : genuineDegreeObservation ha₁ ha₃ B hdeg S = some c) : c ≤ B := by
  unfold genuineDegreeObservation at hc
  split_ifs at hc with hS
  · simp only [Option.some.injEq, quotientIsogeny_degree, actualStrip_card] at hc
    rw [← hc]
    exact (actualKernelEquiv ha₁ ha₃ B hdeg S).val.cyclicDegree_le_degree.trans
      (actualKernelEquiv ha₁ ha₃ B hdeg S).property

/-- The exact finite theorem for genuine elliptic quotient targets. The target
law is constructed, all kernel counts are proved, scalar stripping is geometric,
and the decision is the verified bit-list program. -/
theorem genuine_attack_signed (p : ℕ) [Fact p.Prime] [CharP K p]
    [Algebra (ZMod p) K] [Algebra.IsAlgebraic (ZMod p) K]
    (hW : W.IsSupersingular p) (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0)
    {B s : ℕ} (hs : 784 ≤ s) (hp : 49 ≤ p) (hB : 8*s^2 ≤ B)
    (hcut : (B : ℝ)^2 < 4*(p : ℝ)) :
    let hdeg := validDegrees_of_cutoff (K := K) p B hp hcut
    letI := actualKernelFintype ha₁ ha₃ B hdeg
    let codomain := geometricTarget (W := W) p (by omega) hW
    letI := actualTargetFintype ha₁ ha₃ B hdeg codomain
    1/(1024*(s : ℝ)^3) ≤
      (actualPrintedLaw ha₁ ha₃ B hdeg (cutoff_positive hs hB)).eventMass
        (fun S => (ArithmeticAttack.decision B s
          (genuineDegreeObservation ha₁ ha₃ B hdeg S)).result = true) -
      (actualTargetFirstLaw (Legendre.hasseInvariantLaw (K := K) p (by omega))
        ha₁ ha₃ B hdeg codomain).eventMass
        (fun x => (ArithmeticAttack.decision B s
          (actualTargetDegree ha₁ ha₃ B hdeg codomain x)).result = true) := by
  dsimp only
  let hdeg := validDegrees_of_cutoff (K := K) p B hp hcut
  letI := actualKernelFintype ha₁ ha₃ B hdeg
  let codomain := geometricTarget (W := W) p (by omega) hW
  letI := actualTargetFintype ha₁ ha₃ B hdeg codomain
  simp only [ArithmeticAttack.decision_correct B s _ (by omega : 0 < s)]
  rw [actualPrintedLaw, FiniteLaw.pushForward_event]
  have h := attack_correct_signed
    (actualTargetFirstLaw (Legendre.hasseInvariantLaw (K := K) p (by omega))
      ha₁ ha₃ B hdeg codomain) Sigma.fst
    (actualCodomainCode ha₁ ha₃ B hdeg codomain)
    (actualTargetCode ha₁ ha₃ B hdeg codomain)
    (fun k => genuineDegreeObservation ha₁ ha₃ B hdeg
      ((actualKernelEquiv ha₁ ha₃ B hdeg).symm k))
    p hs (by exact_mod_cast hp) hB hcut
    (actualTargetCode_codomain ha₁ ha₃ B hdeg codomain)
    (fun t => (actualTargetFirstLaw_marginal _ ha₁ ha₃ B hdeg codomain t).trans_le
      (Legendre.hasseInvariantLaw_mass_le p (by omega) t))
    (by
      intro k hk
      rw [genuineDegreeObservation_interior, Equiv.apply_symm_apply]
      have hd := actualKernelEquiv_degree ha₁ ha₃ B hdeg
        ((actualKernelEquiv ha₁ ha₃ B hdeg).symm k)
      rw [Equiv.apply_symm_apply] at hd
      exact hd ▸ hk)
  simpa only [actualTargetCode_degree] using h

end
end IsogenyAttack
