import IsogenyAttack.Attack
import IsogenyAttack.FiniteTorsionKernels

/-!
The endpoint problem is a positive-probability event, not merely a possible
zero-mass input. The exact printed degree law assigns positive mass to a cyclic
kernel of degree B. Splitting that cyclic degree as 2^v times an odd part makes
the complementary degree B/2^v minus the odd part equal zero.

These theorems concern the displayed arithmetic degree formulas and finite
kernel laws. They do not assert that an unspecified implementation handles the
zero-degree request, nor identify an elliptic quotient with a mere group quotient.
-/
namespace IsogenyAttack.Endpoint

/-- The explicit cyclic endpoint HNF (B,1,0). -/
def cyclicEndpoint (B : ℕ) (hB : 0 < B) : BoundedKernel B :=
  ⟨HNF.lift 1 B 0 (by decide) hB hB, by simp⟩

@[simp] theorem cyclicEndpoint_degree (B : ℕ) (hB : 0 < B) :
    (cyclicEndpoint B hB).val.degree = B := by
  simp [cyclicEndpoint]

@[simp] theorem cyclicEndpoint_content (B : ℕ) (hB : 0 < B) :
    (cyclicEndpoint B hB).val.content = 1 := by
  simp [cyclicEndpoint]

@[simp] theorem cyclicEndpoint_cyclicDegree (B : ℕ) (hB : 0 < B) :
    (cyclicEndpoint B hB).val.cyclicDegree = B := by
  simp [cyclicEndpoint]

/-- A specified endpoint atom has strictly positive probability. -/
theorem cyclicEndpoint_mass_pos (B : ℕ) (hB : 0 < B) :
    0 < (printedLaw B hB).mass (cyclicEndpoint B hB) := by
  rw [printedLaw_mass, cyclicEndpoint_degree]
  apply div_pos
  · exact_mod_cast printedWeight_pos hB
  · exact mul_pos (normalizer_pos hB) (by exact_mod_cast kernelCount_pos hB)

/-- The printed law reaches original degree B and cyclic degree B with positive
probability. Thus excluding this case changes the stated experiment. -/
theorem cyclic_endpoint_probability_pos (B : ℕ) (hB : 0 < B) :
    0 < (printedLaw B hB).eventMass
      (fun k => k.val.degree = B ∧ k.val.cyclicDegree = B) := by
  have hatom : (printedLaw B hB).eventMass
      (fun k => k = cyclicEndpoint B hB) =
      (printedLaw B hB).mass (cyclicEndpoint B hB) := by
    simp [FiniteLaw.eventMass_eq_sum]
  have hle := (printedLaw B hB).eventMass_mono
    (E := fun k => k = cyclicEndpoint B hB)
    (F := fun k => k.val.degree = B ∧ k.val.cyclicDegree = B)
    (fun k hk => by subst k; simp)
  rw [hatom] at hle
  exact (cyclicEndpoint_mass_pos B hB).trans_le hle

/-- The unsplit complementary degree is zero on a positive-probability event. -/
theorem zero_complement_probability_pos (B : ℕ) (hB : 0 < B) :
    0 < (printedLaw B hB).eventMass (fun k => B - k.val.cyclicDegree = 0) := by
  apply (cyclic_endpoint_probability_pos B hB).trans_le
  apply (printedLaw B hB).eventMass_mono
  intro k hk
  simp [hk.2]

/-- The literal complementary-degree formula vanishes for any factorization
B=2^v*d. In particular this applies to the canonical split with d odd. -/
theorem split_complement_eq_zero {B v d : ℕ} (hsplit : B = 2 ^ v * d) :
    B / 2 ^ v - d = 0 := by
  rw [hsplit, Nat.mul_div_cancel_left d (pow_pos (by decide) v), Nat.sub_self]

/-- For every prescribed two-power/odd-part split of B, the printed law reaches
that cyclic degree and a zero literal complementary degree with positive mass.
Oddness is retained in the statement to match the source's split convention. -/
theorem split_zero_complement_probability_pos {B v d : ℕ} (hB : 0 < B)
    (_hdodd : Odd d) (hsplit : B = 2 ^ v * d) :
    0 < (printedLaw B hB).eventMass
      (fun k => k.val.cyclicDegree = 2 ^ v * d ∧ B / 2 ^ v - d = 0) := by
  apply (cyclic_endpoint_probability_pos B hB).trans_le
  apply (printedLaw B hB).eventMass_mono
  intro k hk
  exact ⟨hk.2.trans hsplit, split_complement_eq_zero hsplit⟩

/-- Positive probability of the literal split-formula failure without supplying
a split as a hypothesis: every positive B has a two-power times odd factorization. -/
theorem odd_split_zero_complement_probability_pos (B : ℕ) (hB : 0 < B) :
    0 < (printedLaw B hB).eventMass (fun k => ∃ v d : ℕ,
      Odd d ∧ k.val.cyclicDegree = 2 ^ v * d ∧ B / 2 ^ v - d = 0) := by
  obtain ⟨v,d,hd,hsplit⟩ := Nat.exists_eq_two_pow_mul_odd (Nat.ne_of_gt hB)
  apply (split_zero_complement_probability_pos hB hd hsplit).trans_le
  apply (printedLaw B hB).eventMass_mono
  intro k hk
  exact ⟨v,d,hd,hk⟩

/-- In the source's power-of-two cutoff convention B=2^n, the endpoint has odd
part one, and its complementary degree B/2^n−1 is zero with positive probability. -/
theorem power_two_cutoff_zero_complement_probability_pos (n : ℕ) :
    0 < (printedLaw (2^n) (pow_pos (by decide) n)).eventMass
      (fun k => k.val.cyclicDegree = 2^n ∧ (2^n) / 2^n - 1 = 0) := by
  simpa only [mul_one] using split_zero_complement_probability_pos
    (B := 2^n) (v := n) (d := 1) (pow_pos (by decide) n) (by decide) (by simp)

/-- A degree-zero HNF kernel does not exist. -/
theorem no_degree_zero_HNF : ¬ ∃ k : HNF, k.degree = 0 := by
  rintro ⟨k,hk⟩
  exact (Nat.ne_of_gt k.degree_pos) hk

/-- An actual finite subgroup has positive cardinality because it contains zero.
The finiteness premise avoids the Nat.card convention for infinite types. -/
theorem finite_subgroup_card_ne_zero {G : Type*} [AddGroup G]
    (S : AddSubgroup G) [Finite S] : Nat.card S ≠ 0 :=
  Nat.card_pos.ne'

end IsogenyAttack.Endpoint
