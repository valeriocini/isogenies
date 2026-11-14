import IsogenyAttack.Experiments
import IsogenyAttack.BitComplexity
import IsogenyAttack.HasseSampler
import IsogenyAttack.HasseCriterion
import IsogenyAttack.Asymptotics

/-!
The complete finite and asymptotic attack for the explicit arithmetic experiments.
The target law is constructed from Hasse roots, connecting HNFs are conditionally
uniform, empty fibers fail without resampling their targets, and random public
contexts are averaged before taking any absolute value. The decision is the
verified Boolean/list program, supplied with canonical binary degree inputs.

This is not asserted to be the paper's full elliptic-isogeny theorem. The
remaining geometric interface is the map from primitive HNF kernels to quotient
j-invariants, together with the identification of the Hasse law and of the public
degree encoding with the paper's experiments. No quotient geometry is assumed
under the name of an arithmetic definition. The work bound is the program's
explicit Boolean/list work counter, not a machine-model runtime theorem.
-/
namespace IsogenyAttack.ArithmeticAttack
open Legendre BitComplexity
open scoped BigOperators

/-- The verified bit-list decision on the canonical binary form of a public degree.
The conversion to bits specifies the input encoding; its cost is not charged here. -/
def decision (B s : ℕ) (degree : Option ℕ) : BitComplexity.Computation Bool :=
  testBitsOption B.bits s.bits (degree.map Nat.bits)

@[simp] theorem decision_correct (B s : ℕ) (degree : Option ℕ) (hs : 0 < s) :
    (decision B s degree).result = publicTest B s degree := by
  unfold decision
  rw [testBitsOption_correct B.bits s.bits _ (by simpa using hs)]
  simp only [value_bits, Option.map_map, Function.comp_def]
  congr 1
  cases degree <;> simp

/-- Quadratic work in the bit lengths supplied to the program. -/
theorem decision_work_le (B s : ℕ) (degree : Option ℕ) :
    (decision B s degree).work ≤
      8192 * (B.size + s.size + (degree.map Nat.size).getD 0 + 1) ^ 2 + 1 := by
  have h := testBitsOption_work_le B.bits s.bits (degree.map Nat.bits)
  simpa only [decision, Option.map_map, Function.comp_def, Nat.size_eq_bits_len] using h

/-- A fully specified strict-cutoff observation. The printed degree sampler has
an atom at degree B; this concrete completion rejects that endpoint. -/
def degreeObservation {B : ℕ} (k : BoundedKernel B) : Option ℕ :=
  if k.val.degree < B then some k.val.cyclicDegree else none

lemma degreeObservation_interior {B : ℕ} (k : BoundedKernel B)
    (h : k.val.degree < B) : degreeObservation k = some k.val.cyclicDegree := by
  simp [degreeObservation, h]

/-- The degree-first experiment, with the same common public-context law as its
opponent. Keeping the context in the outcome makes the averaging explicit. -/
noncomputable def degreeExperiment {ι : Type*} [Fintype ι]
    (P : FiniteLaw ι) (B : ℕ) (hB : 0 < B) :
    FiniteLaw (Sigma fun _ : ι => BoundedKernel B) :=
  P.dependentBind (fun _ => BoundedKernel B) (fun _ => printedLaw B hB)

/-- The exact target-first experiment with a context-dependent codomain map. -/
noncomputable def targetExperiment {ι τ : Type*} [Fintype ι] [Fintype τ]
    (P : FiniteLaw ι) (μ : FiniteLaw τ) (B : ℕ) (codomain : ι → HNF → τ) :
    FiniteLaw (Sigma fun i : ι => TargetOutcome B (codomain i)) :=
  P.dependentBind (fun i => TargetOutcome B (codomain i))
    (fun i => targetFirstLaw μ B (codomain i))

/-- Context averaging and empty connecting fibers preserve the sampled target law. -/
theorem targetExperiment_marginal {ι τ : Type*} [Fintype ι] [Fintype τ]
    (P : FiniteLaw ι) (μ : FiniteLaw τ) (B : ℕ) (codomain : ι → HNF → τ) (t : τ) :
    (targetExperiment P μ B codomain).eventMass (fun x => x.2.1 = t) = μ.mass t := by
  rw [targetExperiment, FiniteLaw.dependentBind_eventMass]
  simp_rw [targetFirstLaw_marginal]
  rw [← Finset.sum_mul, P.mass_sum, one_mul]

/-- The actual target marginal has exactly the reciprocal-automorphism weight,
using actual admissible coordinate automorphisms of an elliptic curve. This
identity includes the exceptional j-invariants without a generic-case premise. -/
theorem hasse_target_marginal {K ι : Type*} [Field K] [DecidableEq K]
    [IsAlgClosed K] [Fintype ι] (P : FiniteLaw ι)
    (p : ℕ) [CharP K p] [Fact p.Prime] (hp : 3 < p) (B : ℕ)
    (codomain : ι → HNF → HasseJClass (K := K) ((p-1)/2))
    (j : HasseJClass (K := K) ((p-1)/2))
    (W : WeierstrassCurve K) [W.IsElliptic] (hW : W.j = j.val) :
    (targetExperiment P (hasseInvariantLaw (K := K) p (by omega)) B codomain).eventMass
      (fun x => x.2.1 = j) =
      24 / (((p : ℝ)-1) * Nat.card (CurveAutomorphisms.CurveAut W)) := by
  rw [targetExperiment_marginal]
  exact hasseInvariantLaw_eq_reciprocal_aut p hp j W hW

/-- Signed acceptance difference of the two fully specified finite experiments. -/
noncomputable def signedGap {ι τ : Type*} [Fintype ι] [Fintype τ]
    (P : FiniteLaw ι) (μ : FiniteLaw τ) (B s : ℕ) (hB : 0 < B)
    (codomain : ι → HNF → τ) : ℝ :=
  (degreeExperiment P B hB).eventMass
      (fun x => (decision B s (degreeObservation x.2)).result = true) -
    (targetExperiment P μ B codomain).eventMass
      (fun x => (decision B s ((targetComponent x.2).map HNF.degree)).result = true)

/-- Exact finite signed bound. The only probabilistic input here is μ's point-mass
bound; the Hasse-law specialization below proves it rather than assuming it. -/
theorem signedGap_lower {ι τ : Type*} [Fintype ι] [Fintype τ]
    (P : FiniteLaw ι) (μ : FiniteLaw τ) (codomain : ι → HNF → τ)
    {B s : ℕ} (p : ℝ) (hs : 784 ≤ s) (hp : 49 ≤ p)
    (hB : 8 * s ^ 2 ≤ B) (hcut : (B : ℝ) ^ 2 < 4 * p)
    (hμ : ∀ t, μ.mass t ≤ 12 / (p - 1)) :
    1 / (1024 * (s : ℝ) ^ 3) ≤
      signedGap P μ B s (cutoff_positive hs hB) codomain := by
  unfold signedGap degreeExperiment targetExperiment
  apply P.dependentBind_signed_gap
  intro i
  simp only [decision_correct B s _ (by omega : 0 < s)]
  apply attack_correct_signed (targetFirstLaw μ B (codomain i)) Sigma.fst (codomain i)
      targetComponent degreeObservation p hs hp hB hcut
  · exact targetComponent_codomain
  · intro t
    rw [targetFirstLaw_marginal]
    exact hμ t
  · exact degreeObservation_interior

/-- The concrete Hasse target law removes the last abstract probability bound.
Every context may have a different codomain map and different empty fibers. -/
theorem hasse_signedGap_lower {K ι : Type*} [Field K] [DecidableEq K]
    [IsAlgClosed K] [Fintype ι] (P : FiniteLaw ι)
    (p : ℕ) [CharP K p] [Fact p.Prime]
    {B s : ℕ} (hs : 784 ≤ s) (hp : 49 ≤ p) (hB : 8 * s ^ 2 ≤ B)
    (hcut : (B : ℝ) ^ 2 < 4 * (p : ℝ))
    (codomain : ι → HNF → HasseJClass (K := K) ((p-1)/2)) :
    1 / (1024 * (s : ℝ) ^ 3) ≤
      signedGap P (hasseInvariantLaw (K := K) p (by omega)) B s
        (cutoff_positive hs hB) codomain := by
  exact signedGap_lower P _ codomain (p : ℝ) hs (by exact_mod_cast hp) hB hcut
    (hasseInvariantLaw_mass_le p (by omega))

/-- Every degree the concrete experiments expose is at most the public cutoff. -/
theorem degreeObservation_le {B : ℕ} (k : BoundedKernel B) (c : ℕ)
    (hc : degreeObservation k = some c) : c ≤ B := by
  unfold degreeObservation at hc
  split_ifs at hc with hk
  · cases hc
    exact k.val.cyclicDegree_le_degree.trans k.property

lemma targetComponent_degree_le {τ : Type*} {B : ℕ} {codomain : HNF → τ}
    (x : TargetOutcome B codomain) (c : ℕ)
    (hc : (targetComponent x).map HNF.degree = some c) : c ≤ B := by
  rw [targetComponent_degree] at hc
  rcases x with ⟨t, x⟩
  cases x with
  | none => simp at hc
  | some k =>
    simp only [Option.map_some, Option.some.injEq] at hc
    rw [← hc]
    exact k.val.val.cyclicDegree_le_degree.trans (connectingKernel_degree_lt k).le

/-- Work on either experiment is bounded using only the public parameter lengths. -/
theorem decision_work_le_public (B s : ℕ) (degree : Option ℕ)
    (hdegree : ∀ c, degree = some c → c ≤ B) :
    (decision B s degree).work ≤ 8192 * (2 * B.size + s.size + 1) ^ 2 + 1 := by
  apply (decision_work_le B s degree).trans
  have hc : (degree.map Nat.size).getD 0 ≤ B.size := by
    cases degree with
    | none => simp
    | some c => exact Nat.size_le_size (hdegree c rfl)
  have hh : B.size + s.size + (degree.map Nat.size).getD 0 + 1 ≤
      2 * B.size + s.size + 1 := by omega
  exact Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hh 2)) 1

/-- The Hasse cutoff bounds the cutoff's bit length by the characteristic's
bit length plus one. -/
lemma cutoff_size_le {B p : ℕ} (hp : 1 ≤ p)
    (hcut : (B : ℝ) ^ 2 < 4 * (p : ℝ)) : B.size ≤ p.size + 1 := by
  have hBp : B ≤ 2 * p := by
    have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp
    have hBR : (0 : ℝ) ≤ B := Nat.cast_nonneg _
    have h : (B : ℝ) ≤ 2 * p := by nlinarith
    exact_mod_cast h
  apply Nat.size_le.mpr
  calc
    B ≤ 2 * p := hBp
    _ < 2 * 2 ^ p.size := Nat.mul_lt_mul_of_pos_left (Nat.lt_size_self p) (by decide)
    _ = 2 ^ (p.size+1) := by rw [pow_succ]; omega

/-- With n at least the characteristic's binary length and s=n+784, the charged
work is bounded by an explicit quadratic polynomial in the security parameter. -/
theorem decision_work_le_security {B p n : ℕ} (hp : 1 ≤ p)
    (hcut : (B : ℝ) ^ 2 < 4 * (p : ℝ)) (hsize : p.size ≤ n)
    (degree : Option ℕ) (hdegree : ∀ c, degree = some c → c ≤ B) :
    (decision B (n+784) degree).work ≤ 8192 * (3*n+787) ^ 2 + 1 := by
  apply (decision_work_le_public B (n+784) degree hdegree).trans
  have hBsize := cutoff_size_le hp hcut
  have hssize : (n+784).size ≤ n+784 := Nat.size_le.mpr (Nat.lt_two_pow_self)
  have h : 2 * B.size + (n+784).size + 1 ≤ 3*n+787 := by omega
  exact Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h 2)) 1

/-- One finite certificate combines the signed gap of the actual decision
program with its charged work bound on every possible outcome in both games. -/
theorem finite_attack_certificate {K ι : Type*} [Field K] [DecidableEq K]
    [IsAlgClosed K] [Fintype ι] (P : FiniteLaw ι)
    (p : ℕ) [CharP K p] [Fact p.Prime]
    {B s : ℕ} (hs : 784 ≤ s) (hp : 49 ≤ p) (hB : 8 * s ^ 2 ≤ B)
    (hcut : (B : ℝ) ^ 2 < 4 * (p : ℝ))
    (codomain : ι → HNF → HasseJClass (K := K) ((p-1)/2)) :
    (1 / (1024 * (s : ℝ) ^ 3) ≤
      signedGap P (hasseInvariantLaw (K := K) p (by omega)) B s
        (cutoff_positive hs hB) codomain) ∧
    (∀ k : BoundedKernel B,
      (decision B s (degreeObservation k)).work ≤ 8192 * (2 * B.size + s.size + 1) ^ 2 + 1) ∧
    (∀ i (x : TargetOutcome B (codomain i)),
      (decision B s ((targetComponent x).map HNF.degree)).work ≤
        8192 * (2 * B.size + s.size + 1) ^ 2 + 1) := by
  refine ⟨hasse_signedGap_lower P p hs hp hB hcut codomain, ?_, ?_⟩
  · intro k
    exact decision_work_le_public B s _ (degreeObservation_le k)
  · intro i x
    exact decision_work_le_public B s _ (targetComponent_degree_le x)

/-- The finite bound in absolute-value advantage, after averaging contexts. -/
theorem hasse_advantage_lower {K ι : Type*} [Field K] [DecidableEq K]
    [IsAlgClosed K] [Fintype ι] (P : FiniteLaw ι)
    (p : ℕ) [CharP K p] [Fact p.Prime]
    {B s : ℕ} (hs : 784 ≤ s) (hp : 49 ≤ p) (hB : 8 * s ^ 2 ≤ B)
    (hcut : (B : ℝ) ^ 2 < 4 * (p : ℝ))
    (codomain : ι → HNF → HasseJClass (K := K) ((p-1)/2)) :
    1 / (1024 * (s : ℝ) ^ 3) ≤
      |signedGap P (hasseInvariantLaw (K := K) p (by omega)) B s
        (cutoff_positive hs hB) codomain| :=
  (hasse_signedGap_lower P p hs hp hB hcut codomain).trans (le_abs_self _)

/-- Uniformly random public contexts are an explicit instance of the same game;
no independence of the conditional target-fiber sampler is required. -/
theorem uniform_hasse_signedGap_lower {K ι : Type*} [Field K] [DecidableEq K]
    [IsAlgClosed K] [Fintype ι] [Nonempty ι]
    (p : ℕ) [CharP K p] [Fact p.Prime]
    {B s : ℕ} (hs : 784 ≤ s) (hp : 49 ≤ p) (hB : 8 * s ^ 2 ≤ B)
    (hcut : (B : ℝ) ^ 2 < 4 * (p : ℝ))
    (codomain : ι → HNF → HasseJClass (K := K) ((p-1)/2)) :
    1 / (1024 * (s : ℝ) ^ 3) ≤
      signedGap (FiniteLaw.uniform ι) (hasseInvariantLaw (K := K) p (by omega)) B s
        (cutoff_positive hs hB) codomain :=
  hasse_signedGap_lower (FiniteLaw.uniform ι) p hs hp hB hcut codomain

section families
variable (K : ℕ → Type*) [∀ n, Field (K n)] [∀ n, DecidableEq (K n)]
    [∀ n, IsAlgClosed (K n)]
    (ι : ℕ → Type*) [∀ n, Fintype (ι n)]
    (p B : ℕ → ℕ) [∀ n, CharP (K n) (p n)] [∀ n, Fact (p n).Prime]
    (hp : ∀ n, 49 ≤ p n) (hB : ∀ n, 8 * (n + 784) ^ 2 ≤ B n)
    (P : ∀ n, FiniteLaw (ι n))
    (codomain : ∀ n, ι n → HNF → HasseJClass (K := K n) ((p n-1)/2))

/-- The sequence of actual signed acceptance differences, with s = n + 784. -/
noncomputable def familySignedGap (n : ℕ) : ℝ :=
  signedGap (P n) (hasseInvariantLaw (K := K n) (p n) (by have := hp n; omega))
    (B n) (n+784) (cutoff_positive (by omega) (hB n)) (codomain n)

/-- Parameter-family theorem for the defined bit program and finite experiments.
Only the numerical Hasse cutoff may begin after finitely many initial indices. -/
theorem family_gap_not_negligible
    (hcut : ∃ N : ℕ, ∀ n ≥ N, (B n : ℝ) ^ 2 < 4 * (p n : ℝ)) :
    ¬ IsNegligible (familySignedGap K ι p B hp hB P codomain) := by
  apply not_negligible_of_attack_bound
  obtain ⟨N, hN⟩ := hcut
  refine ⟨N, fun n hn => ?_⟩
  have h := hasse_signedGap_lower (P n) (p n) (by omega : 784 ≤ n+784)
    (hp n) (hB n) (hN n hn) (codomain n)
  simpa only [familySignedGap, Nat.cast_add, Nat.cast_ofNat] using h

/-- The ordinary absolute distinguishing advantage is non-negligible as well. -/
theorem family_advantage_not_negligible
    (hcut : ∃ N : ℕ, ∀ n ≥ N, (B n : ℝ) ^ 2 < 4 * (p n : ℝ)) :
    ¬ IsNegligible (fun n => |familySignedGap K ι p B hp hB P codomain n|) := by
  intro h
  apply family_gap_not_negligible K ι p B hp hB P codomain hcut
  simpa only [IsNegligible, abs_abs] using h

/-- A single parameter-family certificate: the actual averaged advantage is
non-negligible and, on all outcomes from either experiment, the decision's
charged Boolean/list work is eventually quadratic in n. The binary-size
condition is explicit because a complexity claim in n requires an input-size
relation; it is not needed for the probability theorem. -/
theorem family_attack_certificate
    (hparameters : ∃ N : ℕ, ∀ n ≥ N,
      (B n : ℝ) ^ 2 < 4 * (p n : ℝ) ∧ (p n).size ≤ n) :
    (¬ IsNegligible (fun n => |familySignedGap K ι p B hp hB P codomain n|)) ∧
    (∃ N : ℕ, ∀ n ≥ N,
      (∀ k : BoundedKernel (B n),
        (decision (B n) (n+784) (degreeObservation k)).work ≤ 8192 * (3*n+787) ^ 2 + 1) ∧
      (∀ i (x : TargetOutcome (B n) (codomain n i)),
        (decision (B n) (n+784) ((targetComponent x).map HNF.degree)).work ≤
          8192 * (3*n+787) ^ 2 + 1)) := by
  obtain ⟨N, hN⟩ := hparameters
  refine ⟨family_advantage_not_negligible K ι p B hp hB P codomain
    ⟨N, fun n hn => (hN n hn).1⟩, N, ?_⟩
  intro n hn
  have hpn : 1 ≤ p n := (by decide : 1 ≤ 49).trans (hp n)
  constructor
  · intro k
    exact decision_work_le_security hpn (hN n hn).1 (hN n hn).2 _ (degreeObservation_le k)
  · intro i x
    exact decision_work_le_security hpn (hN n hn).1 (hN n hn).2 _ (targetComponent_degree_le x)

end families

/-- In particular, the entire uniform-context family has non-negligible advantage. -/
theorem uniform_family_advantage_not_negligible
    (K : ℕ → Type*) [∀ n, Field (K n)] [∀ n, DecidableEq (K n)]
    [∀ n, IsAlgClosed (K n)]
    (ι : ℕ → Type*) [∀ n, Fintype (ι n)] [∀ n, Nonempty (ι n)]
    (p B : ℕ → ℕ) [∀ n, CharP (K n) (p n)] [∀ n, Fact (p n).Prime]
    (hp : ∀ n, 49 ≤ p n) (hB : ∀ n, 8 * (n + 784) ^ 2 ≤ B n)
    (codomain : ∀ n, ι n → HNF → HasseJClass (K := K n) ((p n-1)/2))
    (hcut : ∃ N : ℕ, ∀ n ≥ N, (B n : ℝ) ^ 2 < 4 * (p n : ℝ)) :
    ¬ IsNegligible (fun n =>
      |familySignedGap K ι p B hp hB (fun n => FiniteLaw.uniform (ι n)) codomain n|) :=
  family_advantage_not_negligible K ι p B hp hB _ codomain hcut

/-- The same non-negligibility statement with the growth bound required only
eventually. Positivity alone defines every initial cutoff; the finitely many
initial experiments need satisfy no quantitative growth condition. -/
theorem eventual_family_advantage_not_negligible
    (K : ℕ → Type*) [∀ n, Field (K n)] [∀ n, DecidableEq (K n)]
    [∀ n, IsAlgClosed (K n)]
    (ι : ℕ → Type*) [∀ n, Fintype (ι n)]
    (p B : ℕ → ℕ) [∀ n, CharP (K n) (p n)] [∀ n, Fact (p n).Prime]
    (hp : ∀ n, 49 ≤ p n) (hBpos : ∀ n, 0 < B n)
    (P : ∀ n, FiniteLaw (ι n))
    (codomain : ∀ n, ι n → HNF → HasseJClass (K := K n) ((p n-1)/2))
    (hparameters : ∃ N : ℕ, ∀ n ≥ N,
      8 * (n+784)^2 ≤ B n ∧ (B n : ℝ)^2 < 4 * (p n : ℝ)) :
    ¬ IsNegligible (fun n =>
      |signedGap (P n)
        (hasseInvariantLaw (K := K n) (p n) (by have := hp n; omega))
        (B n) (n+784) (hBpos n) (codomain n)|) := by
  apply not_negligible_of_attack_bound
  obtain ⟨N, hN⟩ := hparameters
  refine ⟨N, fun n hn => ?_⟩
  have h := (hasse_signedGap_lower (P n) (p n) (by omega : 784 ≤ n+784)
    (hp n) (hN n hn).1 (hN n hn).2 (codomain n)).trans (le_abs_self _)
  simpa only [Nat.cast_add, Nat.cast_ofNat] using h

end IsogenyAttack.ArithmeticAttack
