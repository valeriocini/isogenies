import IsogenyAttack.GenuineAttack

/-! Context averaging, repeated hints and asymptotic efficiency for genuine
elliptic quotient experiments. Every target is `geometricTarget`. -/

namespace IsogenyAttack.GenuineExperiment

open WeierstrassCurve WeierstrassCurve.Affine
open scoped BigOperators
noncomputable section
open scoped Classical

/-- A genuine supersingular source in the equation form used by the sampler. -/
structure Source (K : Type*) [Field K] (p : ℕ) where
  curve : Affine K
  elliptic : curve.IsElliptic
  supersingular : curve.IsSupersingular p
  a₁_zero : curve.a₁ = 0
  a₃_zero : curve.a₃ = 0

attribute [instance] Source.elliptic

variable {K : Type*} [Field K] [IsAlgClosed K] [NeZero (2 : K)]
    {p : ℕ} [Fact p.Prime] [CharP K p]
    [Algebra (ZMod p) K] [Algebra.IsAlgebraic (ZMod p) K]

def degreeAcceptance (C : Source K p) (B s : ℕ)
    (hdeg : ValidDegrees K B) (hB : 0 < B) : ℝ :=
  letI := actualKernelFintype C.a₁_zero C.a₃_zero B hdeg
  (actualPrintedLaw C.a₁_zero C.a₃_zero B hdeg hB).eventMass
    (fun x => (ArithmeticAttack.decision B s
      (genuineDegreeObservation C.a₁_zero C.a₃_zero B hdeg x)).result = true)

def targetAcceptance (C : Source K p) (hp : 2 < p) (B s : ℕ)
    (hdeg : ValidDegrees K B) : ℝ :=
  let target := geometricTarget (W := C.curve) p hp C.supersingular
  letI := actualTargetFintype C.a₁_zero C.a₃_zero B hdeg target
  (actualTargetFirstLaw (Legendre.hasseInvariantLaw (K := K) p hp)
    C.a₁_zero C.a₃_zero B hdeg target).eventMass
    (fun x => (ArithmeticAttack.decision B s
      (actualTargetDegree C.a₁_zero C.a₃_zero B hdeg target x)).result = true)

/-- The signed acceptance difference, averaging the same public source law
in both games before taking an absolute value. -/
def signedGap {ι : Type*} [Fintype ι] (P : FiniteLaw ι)
    (C : ι → Source K p) (hp : 2 < p) (B s : ℕ)
    (hdeg : ValidDegrees K B) (hB : 0 < B) : ℝ :=
  ∑ i, P.mass i * (degreeAcceptance (C i) B s hdeg hB -
    targetAcceptance (C i) hp B s hdeg)

/-- This is the exact difference of the two context-conditioned finite
experiments, not an average of absolute conditional advantages. -/
theorem signedGap_eq_joint {ι : Type*} [Fintype ι] (P : FiniteLaw ι)
    (C : ι → Source K p) (hp : 2 < p) (B s : ℕ)
    (hdeg : ValidDegrees K B) (hB : 0 < B) :
    let target i := geometricTarget (W := (C i).curve) p hp (C i).supersingular
    letI := fun i => actualKernelFintype (C i).a₁_zero (C i).a₃_zero B hdeg
    letI := fun i => actualTargetFintype (C i).a₁_zero (C i).a₃_zero B hdeg (target i)
    signedGap P C hp B s hdeg hB =
      (P.dependentBind (fun i => ActualKernel (C i).curve.Point B)
        (fun i => actualPrintedLaw (C i).a₁_zero (C i).a₃_zero B hdeg hB)).eventMass
        (fun x => (ArithmeticAttack.decision B s
          (genuineDegreeObservation (C x.1).a₁_zero (C x.1).a₃_zero B hdeg x.2)).result = true) -
      (P.dependentBind (fun i => ActualTargetOutcome (C i).a₁_zero (C i).a₃_zero B hdeg (target i))
        (fun i => actualTargetFirstLaw (Legendre.hasseInvariantLaw (K := K) p hp)
          (C i).a₁_zero (C i).a₃_zero B hdeg (target i))).eventMass
        (fun x => (ArithmeticAttack.decision B s
          (actualTargetDegree (C x.1).a₁_zero (C x.1).a₃_zero B hdeg (target x.1) x.2)).result = true) := by
  dsimp only
  rw [FiniteLaw.dependentBind_eventMass, FiniteLaw.dependentBind_eventMass,
    ← Finset.sum_sub_distrib]
  simp only [signedGap, degreeAcceptance, targetAcceptance, mul_sub]

/-- The fully geometric fixed-source bound survives arbitrary common finite
randomization of the source and every public context included in its index. -/
theorem signedGap_lower {ι : Type*} [Fintype ι] (P : FiniteLaw ι)
    (C : ι → Source K p) {B s : ℕ}
    (hs : 784 ≤ s) (hp : 49 ≤ p) (hB : 8 * s ^ 2 ≤ B)
    (hcut : (B : ℝ) ^ 2 < 4 * (p : ℝ)) :
    1 / (1024 * (s : ℝ) ^ 3) ≤
      signedGap P C (by omega) B s (validDegrees_of_cutoff p B hp hcut)
        (cutoff_positive hs hB) := by
  calc
    _ = ∑ i, P.mass i * (1 / (1024 * (s : ℝ) ^ 3)) := by
      rw [← Finset.sum_mul, P.mass_sum, one_mul]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_left _ (P.mass_nonneg i)
      exact genuine_attack_signed p (C i).supersingular (C i).a₁_zero (C i).a₃_zero
        hs hp hB hcut

theorem targetDegree_le (C : Source K p) (hp : 2 < p) (B : ℕ)
    (hdeg : ValidDegrees K B)
    (x : ActualTargetOutcome C.a₁_zero C.a₃_zero B hdeg
      (geometricTarget (W := C.curve) p hp C.supersingular))
    (d : ℕ) (hd : actualTargetDegree C.a₁_zero C.a₃_zero B hdeg
      (geometricTarget (W := C.curve) p hp C.supersingular) x = some d) : d ≤ B := by
  rcases x with ⟨t, x⟩
  cases x with
  | none => simp [actualTargetDegree] at hd
  | some x =>
    simp only [actualTargetDegree, Option.map_some, Option.some.injEq] at hd
    rw [← hd, actualStrip_card]
    exact (actualKernelEquiv C.a₁_zero C.a₃_zero B hdeg x.val).val.cyclicDegree_le_degree.trans
      (actualKernelEquiv C.a₁_zero C.a₃_zero B hdeg x.val).property

/-- On either genuine sample space, the verified bit-list work counter has
the same public quadratic bound. -/
theorem decision_work_le (C : Source K p) (hp : 2 < p) (B s : ℕ)
    (hdeg : ValidDegrees K B) :
    (∀ x : ActualKernel C.curve.Point B,
      (ArithmeticAttack.decision B s
        (genuineDegreeObservation C.a₁_zero C.a₃_zero B hdeg x)).work ≤
        8192 * (2 * B.size + s.size + 1) ^ 2 + 1) ∧
    (∀ x : ActualTargetOutcome C.a₁_zero C.a₃_zero B hdeg
        (geometricTarget (W := C.curve) p hp C.supersingular),
      (ArithmeticAttack.decision B s
        (actualTargetDegree C.a₁_zero C.a₃_zero B hdeg
          (geometricTarget (W := C.curve) p hp C.supersingular) x)).work ≤
        8192 * (2 * B.size + s.size + 1) ^ 2 + 1) := by
  constructor
  · intro x
    exact ArithmeticAttack.decision_work_le_public B s _
      (genuineDegreeObservation_le C.a₁_zero C.a₃_zero B hdeg x)
  · intro x
    exact ArithmeticAttack.decision_work_le_public B s _ (targetDegree_le C hp B hdeg x)

end
end IsogenyAttack.GenuineExperiment

namespace IsogenyAttack.GenuineExperiment
noncomputable section
open scoped Classical

section Families
variable (K : ℕ → Type*) [∀ n, Field (K n)] [∀ n, IsAlgClosed (K n)]
    [∀ n, NeZero (2 : K n)] (ι : ℕ → Type*) [∀ n, Fintype (ι n)]
    (p B : ℕ → ℕ) [∀ n, Fact (p n).Prime] [∀ n, CharP (K n) (p n)]
    [∀ n, Algebra (ZMod (p n)) (K n)]
    [∀ n, Algebra.IsAlgebraic (ZMod (p n)) (K n)]
    (hp : ∀ n, 49 ≤ p n) (hB : ∀ n, 8 * (n + 784) ^ 2 ≤ B n)
    (hcut : ∀ n, (B n : ℝ) ^ 2 < 4 * (p n : ℝ))
    (P : ∀ n, FiniteLaw (ι n)) (C : ∀ n, ι n → Source (K n) (p n))

/-- An actual family of signed gaps, with `s = n + 784`. -/
def familySignedGap (n : ℕ) : ℝ :=
  signedGap (P n) (C n) (by have := hp n; omega) (B n) (n + 784)
    (validDegrees_of_cutoff (p n) (B n) (hp n) (hcut n))
    (cutoff_positive (by omega) (hB n))

/-- Nonnegligibility follows from the proved inverse-cubic bound for the
specified geometric experiments, with no abstract codomain parameter. -/
theorem family_gap_not_negligible :
    ¬ IsNegligible (familySignedGap K ι p B hp hB hcut P C) := by
  apply not_negligible_of_attack_bound
  refine ⟨0, fun n _ => ?_⟩
  simpa only [familySignedGap, Nat.cast_add, Nat.cast_ofNat] using
    signedGap_lower (P n) (C n) (by omega : 784 ≤ n + 784) (hp n) (hB n) (hcut n)

theorem family_advantage_not_negligible :
    ¬ IsNegligible (fun n => |familySignedGap K ι p B hp hB hcut P C n|) := by
  intro h
  apply family_gap_not_negligible K ι p B hp hB hcut P C
  simpa only [IsNegligible, abs_abs] using h

omit [∀ n, Fintype (ι n)] in
/-- At every security parameter at least the characteristic's binary length,
the decision has explicitly quadratic charged bit-list work on both games.
This condition is pointwise, so it does not require an impossible bound at n=0. -/
theorem family_decision_work_le (n : ℕ) (hsize : (p n).size ≤ n) (i : ι n) :
    let D := C n i
    let hdeg := validDegrees_of_cutoff (K := K n) (p n) (B n) (hp n) (hcut n)
    (∀ x : ActualKernel D.curve.Point (B n),
      (ArithmeticAttack.decision (B n) (n + 784)
        (genuineDegreeObservation D.a₁_zero D.a₃_zero (B n) hdeg x)).work ≤
        8192 * (3 * n + 787) ^ 2 + 1) ∧
    (∀ x : ActualTargetOutcome D.a₁_zero D.a₃_zero (B n) hdeg
        (geometricTarget (W := D.curve) (p n) (by have := hp n; omega) D.supersingular),
      (ArithmeticAttack.decision (B n) (n + 784)
        (actualTargetDegree D.a₁_zero D.a₃_zero (B n) hdeg
          (geometricTarget (W := D.curve) (p n) (by have := hp n; omega) D.supersingular) x)).work ≤
        8192 * (3 * n + 787) ^ 2 + 1) := by
  dsimp only
  constructor
  · intro x
    exact ArithmeticAttack.decision_work_le_security (by have := hp n; omega)
      (hcut n) hsize _ (genuineDegreeObservation_le _ _ _ _ x)
  · intro x
    exact ArithmeticAttack.decision_work_le_security (by have := hp n; omega)
      (hcut n) hsize _ (targetDegree_le _ _ _ _ x)

end Families
end
end IsogenyAttack.GenuineExperiment

namespace IsogenyAttack.FiniteLaw
open scoped BigOperators
noncomputable section

/-- Independent product of two finite laws. -/
def independentProduct {α β : Type*} [Fintype α] [Fintype β]
    (P : FiniteLaw α) (Q : FiniteLaw β) : FiniteLaw (α × β) where
  mass x := P.mass x.1 * Q.mass x.2
  mass_nonneg x := mul_nonneg (P.mass_nonneg x.1) (Q.mass_nonneg x.2)
  mass_sum := by
    rw [Fintype.sum_prod_type]
    simp only [← Finset.mul_sum, Q.mass_sum, mul_one, P.mass_sum]

theorem independentProduct_first_event {α β : Type*} [Fintype α] [Fintype β]
    (P : FiniteLaw α) (Q : FiniteLaw β) (E : α → Prop) :
    (P.independentProduct Q).eventMass (fun x => E x.1) = P.eventMass E := by
  classical
  rw [eventMass_eq_sum, Fintype.sum_prod_type, eventMass_eq_sum]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : E x <;> simp [independentProduct, hx, ← Finset.mul_sum, Q.mass_sum]

/-- Exactly q independent hints, represented recursively as a finite tuple. -/
def HintTuple (α : Type*) : ℕ → Type _
  | 0 => PUnit
  | q + 1 => α × HintTuple α q

instance hintTupleFintype (α : Type*) [Fintype α] (q : ℕ) : Fintype (HintTuple α q) := by
  induction q with
  | zero => exact inferInstanceAs (Fintype PUnit)
  | succ q ih => exact inferInstanceAs (Fintype (α × HintTuple α q))

/-- Fresh independent sampling of q hints under the same conditional law. -/
def repeatHints {α : Type*} [Fintype α] (P : FiniteLaw α) :
    (q : ℕ) → FiniteLaw (HintTuple α q)
  | 0 => ⟨fun _ => 1, fun _ => by positivity, by
      change ∑ _ : PUnit, (1 : ℝ) = 1
      simp⟩
  | q + 1 => P.independentProduct (repeatHints P q)

def firstHint {α : Type*} : (q : ℕ) → 0 < q → HintTuple α q → α
  | 0, h, _ => False.elim (Nat.not_lt_zero _ h)
  | _ + 1, _, x => x.1

/-- Ignoring all but the first of any positive number of independent hints
preserves every event probability exactly. -/
theorem repeatHints_first_event {α : Type*} [Fintype α]
    (P : FiniteLaw α) (q : ℕ) (hq : 0 < q) (E : α → Prop) :
    (P.repeatHints q).eventMass (fun x => E (firstHint q hq x)) = P.eventMass E := by
  cases q with
  | zero => omega
  | succ q => exact independentProduct_first_event P (repeatHints P q) E

/-- The first-hint decision has the same signed distinguishing gap for every
q≥1. The underlying experiments may have different outcome spaces. -/
theorem repeatHints_signed_gap {α β : Type*} [Fintype α] [Fintype β]
    (P : FiniteLaw α) (Q : FiniteLaw β) (q : ℕ) (hq : 0 < q)
    (EP : α → Prop) (EQ : β → Prop) :
    (P.repeatHints q).eventMass (fun x => EP (firstHint q hq x)) -
      (Q.repeatHints q).eventMass (fun x => EQ (firstHint q hq x)) =
      P.eventMass EP - Q.eventMass EQ := by
  rw [repeatHints_first_event, repeatHints_first_event]

/-- Sample the common context once, then q fresh hints conditioned on that
context. Reading the first hint gives exactly the original joint event. -/
theorem dependentBind_repeatHints_first_event {ι : Type*} [Fintype ι]
    (P : FiniteLaw ι) (α : ι → Type*) [∀ i, Fintype (α i)]
    (Q : ∀ i, FiniteLaw (α i)) (q : ℕ) (hq : 0 < q) (E : Sigma α → Prop) :
    (P.dependentBind (fun i => HintTuple (α i) q) (fun i => (Q i).repeatHints q)).eventMass
        (fun x => E ⟨x.1, firstHint q hq x.2⟩) =
      (P.dependentBind α Q).eventMass E := by
  rw [dependentBind_eventMass, dependentBind_eventMass]
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg (fun r : ℝ => P.mass i * r)
    (repeatHints_first_event (Q i) q hq (fun x => E ⟨i, x⟩))

theorem dependentBind_repeatHints_signed_gap {ι : Type*} [Fintype ι]
    (P : FiniteLaw ι) (α β : ι → Type*)
    [∀ i, Fintype (α i)] [∀ i, Fintype (β i)]
    (U : ∀ i, FiniteLaw (α i)) (S : ∀ i, FiniteLaw (β i))
    (q : ℕ) (hq : 0 < q) (EU : Sigma α → Prop) (ES : Sigma β → Prop) :
    (P.dependentBind (fun i => HintTuple (α i) q) (fun i => (U i).repeatHints q)).eventMass
        (fun x => EU ⟨x.1, firstHint q hq x.2⟩) -
      (P.dependentBind (fun i => HintTuple (β i) q) (fun i => (S i).repeatHints q)).eventMass
        (fun x => ES ⟨x.1, firstHint q hq x.2⟩) =
      (P.dependentBind α U).eventMass EU - (P.dependentBind β S).eventMass ES := by
  rw [dependentBind_repeatHints_first_event, dependentBind_repeatHints_first_event]

end
end IsogenyAttack.FiniteLaw
