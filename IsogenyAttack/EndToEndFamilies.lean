import IsogenyAttack.EndToEnd

/-!
Nonnegligibility for the actual publicly encoded experiments, at the source's
exact response cutoff. Both context-dependent source curves are finite-field
Montgomery models. Arbitrary valid randomized representation and continuation
channels are retained in the probability space.
-/
namespace IsogenyAttack.EndToEndFamilies

open PublicObservation PublicFullAttack
noncomputable section
open scoped Classical

variable (K : ℕ → Type*) [∀ n, Field (K n)] [∀ n, IsAlgClosed (K n)]
    [∀ n, NeZero (2 : K n)] (ι : ℕ → Type*) [∀ n, Fintype (ι n)]
    (p : ℕ → ℕ) [∀ n, Fact (p n).Prime] [∀ n, CharP (K n) (p n)]
    [∀ n, Algebra (ZMod (p n)) (K n)]
    [∀ n, Algebra.IsAlgebraic (ZMod (p n)) (K n)]
    (hp : ∀ n, 49 ≤ p n)

include hp in
/-- Every sampled degree is valid at the canonical response cutoff. -/
theorem cutoffValidity (n : ℕ) : ValidDegrees (K n) (ResponseCutoff.bound (p n)) :=
  validDegrees_of_cutoff (K := K n) (p n) (ResponseCutoff.bound (p n)) (hp n)
    (ResponseCutoff.bound_sq_lt_four_mul_real (p n) (by have := hp n; omega))

variable (P : ∀ n, FiniteLaw (ι n))
    (A X : ∀ n, ι n → FiniteMontgomerySampler.Parameters (K := K n) (p n))
    (E : ℕ → PolynomialDegreeDecoder)
    (CU : ∀ n, EncodingChannel (E n)
      (EndToEnd.degreeObservation (p n) (by have := hp n; omega) (A n)
        (ResponseCutoff.bound (p n)) (cutoffValidity K p hp n)))
    (CS : ∀ n, EncodingChannel (E n)
      (EndToEnd.targetObservation (p n) (by have := hp n; omega) (X n)
        (ResponseCutoff.bound (p n)) (cutoffValidity K p hp n)))

/-- The actual signed gap after context sampling, raw morphism sampling,
response construction, continuation randomness, and public representation. -/
def familySignedGap (n : ℕ) : ℝ :=
  EndToEnd.signedGap (p n) (P n) (by have := hp n; omega) (A n) (X n)
    (ResponseCutoff.bound (p n)) (n+784) (cutoffValidity K p hp n)
    (ResponseCutoff.bound_pos (p n)) (E n) (CU n) (CS n)

/-- The finite certificate supplies the lower bound eventually. No equality
to a modified endpoint experiment and no probability-bound hypothesis is used. -/
theorem family_gap_lower_eventually
    (hgrowth : ∃ N : ℕ, ∀ n ≥ N, 2^n ≤ p n) :
    ∃ N : ℕ, ∀ n ≥ N,
      1/(1024*((n : ℝ)+784)^3) ≤ familySignedGap K ι p hp P A X E CU CS n := by
  obtain ⟨N, hN⟩ := hgrowth
  refine ⟨max N 64, fun n hn => ?_⟩
  have h64 : 64 ≤ n := (le_max_right N 64).trans hn
  have hg := (ResponseCutoff.polynomial_le_exponential n h64).trans
    (hN n ((le_max_left N 64).trans hn))
  have hB := ResponseCutoff.threshold_growth (p n) n hg
  have h := (EndToEnd.full_attack_certificate (p n) (P n) (A n) (X n)
    (s := n+784) (by omega) (hp n) hB (E n) (CU n) (CS n)).1
  simpa only [familySignedGap, Nat.cast_add, Nat.cast_ofNat] using h

/-- The encoded experiment's signed gap is nonnegligible. -/
theorem family_gap_not_negligible
    (hgrowth : ∃ N : ℕ, ∀ n ≥ N, 2^n ≤ p n) :
    ¬ IsNegligible (familySignedGap K ι p hp P A X E CU CS) :=
  not_negligible_of_attack_bound
    (family_gap_lower_eventually K ι p hp P A X E CU CS hgrowth)

/-- The usual absolute distinguishing advantage of the public attack on the
actual encoded experiments is nonnegligible. -/
theorem family_advantage_not_negligible
    (hgrowth : ∃ N : ℕ, ∀ n ≥ N, 2^n ≤ p n) :
    ¬ IsNegligible (fun n => |familySignedGap K ι p hp P A X E CU CS n|) := by
  intro h
  apply family_gap_not_negligible K ι p hp P A X E CU CS hgrowth
  simpa only [IsNegligible, abs_abs] using h

theorem family_advantage_not_negligible_of_exponential
    (hgrowth : ∀ n, 2^n ≤ p n) :
    ¬ IsNegligible (fun n => |familySignedGap K ι p hp P A X E CU CS n|) :=
  family_advantage_not_negligible K ι p hp P A X E CU CS
    ⟨0, fun n _ => hgrowth n⟩

/-- Uniform decoder bounds and polynomial public input length give an
explicit polynomial in the security parameter for the actual public program.
The length hypothesis includes the encoded response, cutoff, and threshold. -/
theorem work_le_polynomial_security (c e L k n : ℕ) (D : Option (List Bool))
    (hc : (E n).coefficient ≤ c) (he : (E n).exponent ≤ e)
    (hlen : (ResponseCutoff.bound (p n)).size + (n+784).size +
      (D.map List.length).getD 0 + 1 ≤ L * (n+1)^k) :
    (run (E n) (ResponseCutoff.bound (p n)) (n+784) D).work ≤
      ((c + 8192*(c+1)^2 + 2) * L^(2*(e+1))) * (n+1)^(k*(2*(e+1))) := by
  have hc' : (E n).coefficient + 8192*((E n).coefficient+1)^2 + 2 ≤
      c + 8192*(c+1)^2 + 2 := by
    have hsq := Nat.pow_le_pow_left (Nat.add_le_add_right hc 1) 2
    omega
  have hbase : 1 ≤ L * (n+1)^k := by omega
  have hexp : 2*((E n).exponent+1) ≤ 2*(e+1) := by omega
  calc
    _ ≤ ((E n).coefficient + 8192*((E n).coefficient+1)^2 + 2) *
        ((ResponseCutoff.bound (p n)).size + (n+784).size +
          (D.map List.length).getD 0 + 1)^(2*((E n).exponent+1)) :=
      run_work_polynomial (E n) _ _ D
    _ ≤ (c + 8192*(c+1)^2 + 2) * (L * (n+1)^k)^(2*((E n).exponent+1)) :=
      Nat.mul_le_mul hc' (Nat.pow_le_pow_left hlen _)
    _ ≤ (c + 8192*(c+1)^2 + 2) * (L * (n+1)^k)^(2*(e+1)) :=
      Nat.mul_le_mul_left _ (pow_le_pow_right₀ hbase hexp)
    _ = _ := by rw [mul_pow, ← pow_mul]; ring

end
end IsogenyAttack.EndToEndFamilies
