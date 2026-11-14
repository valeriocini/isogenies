import IsogenyAttack.LegendreDistribution
import IsogenyAttack.HassePolynomial

/-! Explicit probability laws on Legendre parameters and their geometric
j-invariants. The supersingular interpretation is deliberately not asserted. -/

namespace IsogenyAttack.Legendre
open scoped BigOperators
open Polynomial Finset

variable {K : Type*} [Field K] [DecidableEq K] [IsAlgClosed K]

abbrev HasseRoot (n : ℕ) := {t : K // t ∈ (hassePolynomial (K := K) n).roots.toFinset}

lemma hasseRoot_card (n : ℕ) (hsep : (hassePolynomial (K := K) n).Separable) :
    Fintype.card (HasseRoot (K := K) n) = n := by
  simp [HasseRoot, hasse_root_count n hsep]

lemma hasseRoot_nonempty (n : ℕ) (hn : 0 < n)
    (hsep : (hassePolynomial (K := K) n).Separable) : Nonempty (HasseRoot (K := K) n) := by
  apply Fintype.card_pos_iff.mp
  rw [hasseRoot_card n hsep]
  exact hn

omit [IsAlgClosed K] in
lemma hasseRoot_eval {n : ℕ} (t : HasseRoot (K := K) n) :
    (hassePolynomial (K := K) n).eval t.val = 0 := by
  have hp : hassePolynomial (K := K) n ≠ 0 := (hassePolynomial_monic n).ne_zero
  simpa only [Multiset.mem_toFinset, mem_roots hp, IsRoot] using t.property

omit [IsAlgClosed K] in
lemma hasseRoot_ne_zero {n : ℕ} (t : HasseRoot (K := K) n) : t.val ≠ 0 := by
  intro ht
  have h := hasseRoot_eval t
  rw [ht, hassePolynomial_eval_zero] at h
  exact one_ne_zero h

omit [IsAlgClosed K] in
lemma hasseRoot_ne_one {n : ℕ} (h1 : (hassePolynomial (K := K) n).eval 1 ≠ 0)
    (t : HasseRoot (K := K) n) : t.val ≠ 1 := by
  intro ht
  exact h1 (ht ▸ hasseRoot_eval t)

/-- The honest uniform law on the distinct roots of the explicit Hasse polynomial. -/
noncomputable def hasseRootLaw (n : ℕ) (hn : 0 < n)
    (hsep : (hassePolynomial (K := K) n).Separable) : FiniteLaw (HasseRoot (K := K) n) := by
  letI := hasseRoot_nonempty n hn hsep
  exact FiniteLaw.uniform (HasseRoot (K := K) n)

/-- The finite target set consists of the actual j-invariants of these roots. -/
abbrev HasseJClass (n : ℕ) :=
  {j : K // j ∈ (hassePolynomial (K := K) n).roots.toFinset.image jInvariant}

def hasseJMap {n : ℕ} (t : HasseRoot (K := K) n) : HasseJClass (K := K) n :=
  ⟨jInvariant t.val, mem_image.mpr ⟨t.val, t.property, rfl⟩⟩

/-- The j-class law is a defined pushforward, not an assumed point-mass formula. -/
noncomputable def hasseJLaw (n : ℕ) (hn : 0 < n)
    (hsep : (hassePolynomial (K := K) n).Separable) : FiniteLaw (HasseJClass (K := K) n) :=
  (hasseRootLaw n hn hsep).pushForward hasseJMap

/-- The cardinal degree-six fiber bound gives the exact required 6/n scale. -/
theorem hasseJLaw_mass_le (n : ℕ) (hn : 0 < n)
    (hsep : (hassePolynomial (K := K) n).Separable)
    (h1 : (hassePolynomial (K := K) n).eval 1 ≠ 0) (h256 : (256 : K) ≠ 0)
    (j : HasseJClass (K := K) n) :
    (hasseJLaw n hn hsep).mass j ≤ 6 / (n : ℝ) := by
  letI := hasseRoot_nonempty n hn hsep
  have h := uniform_j_mass_le (fun t : HasseRoot (K := K) n => t.val)
    Subtype.val_injective h256 (fun t => ⟨hasseRoot_ne_zero t, hasseRoot_ne_one h1 t⟩) j.val
  rw [hasseRoot_card n hsep] at h
  change (hasseRootLaw n hn hsep).eventMass (fun t => hasseJMap t = j) ≤ _
  have heq : (hasseRootLaw n hn hsep).eventMass (fun t => hasseJMap t = j) =
      (FiniteLaw.uniform (HasseRoot (K := K) n)).eventMass
        (fun t => jInvariant t.val = j.val) := by
    apply FiniteLaw.eventMass_congr
    intro t
    exact Subtype.ext_iff
  rw [heq]
  exact h

/-- A concrete law on j-invariants, obtained from the explicit Hasse polynomial
in characteristic p. Its identification with the supersingular stationary walk
is a separate geometric theorem; no such identification is built into this name. -/
noncomputable def hasseInvariantLaw (p : ℕ) [CharP K p] [Fact p.Prime] (hp : 2 < p) :
    FiniteLaw (HasseJClass (K := K) ((p-1)/2)) :=
  hasseJLaw ((p-1)/2) (by omega)
    (hassePolynomial_separable (K := K) p (by omega))

/-- The desired point-mass scale is proved unconditionally for the concrete
Hasse-root j-law, from polynomial separability and the actual j-map's degree. -/
theorem hasseInvariantLaw_mass_le (p : ℕ) [CharP K p] [Fact p.Prime]
    (hp : 2 < p) (j : HasseJClass (K := K) ((p-1)/2)) :
    (hasseInvariantLaw (K := K) p hp).mass j ≤ 12 / ((p : ℝ)-1) := by
  have hn : 0 < (p-1)/2 := by omega
  have hnp : 2*((p-1)/2) < p := by omega
  have h2 : (2 : K) ≠ 0 := small_natCast_ne_zero p (by decide) hp
  have h256 : (256 : K) ≠ 0 := by
    have h := pow_ne_zero 8 h2
    norm_num at h
    exact h
  have hbound := hasseJLaw_mass_le ((p-1)/2) hn
    (hassePolynomial_separable (K := K) p hnp)
    (hassePolynomial_eval_one_ne_zero (K := K) p hnp) h256 j
  change (hasseJLaw ((p-1)/2) _ _).mass j ≤ _
  have hpodd := (Fact.out : Nat.Prime p).odd_of_ne_two (by omega)
  obtain ⟨a, ha⟩ := hpodd
  have hpn : p = 2*((p-1)/2)+1 := by omega
  have hreal : (p : ℝ)-1 = 2*((p-1)/2 : ℕ) := by
    have h := congrArg (fun n : ℕ => (n : ℝ)) hpn
    push_cast at h
    linarith
  have hden : (((p-1)/2 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  have heq : 6 / (((p-1)/2 : ℕ) : ℝ) = 12 / ((p : ℝ)-1) := by
    rw [hreal]
    field_simp
    ring
  exact heq ▸ hbound

omit [IsAlgClosed K] in
/-- Every target of the explicit j-law is realized by an actual nonsingular
Mathlib Weierstrass curve whose Legendre parameter is a Hasse root. -/
theorem hasseJClass_elliptic_witness (p : ℕ) [CharP K p] [Fact p.Prime]
    (hp : 2 < p) (j : HasseJClass (K := K) ((p-1)/2)) :
    ∃ (t : K) (h : (curve t).IsElliptic),
      @WeierstrassCurve.j K _ (curve t) h = j.val ∧
      (hassePolynomial (K := K) ((p-1)/2)).eval t = 0 := by
  obtain ⟨t, ht, hj⟩ := Finset.mem_image.mp j.property
  let r : HasseRoot (K := K) ((p-1)/2) := ⟨t, ht⟩
  have h2 : (2 : K) ≠ 0 := small_natCast_ne_zero p (by decide) hp
  have ht0 : t ≠ 0 := hasseRoot_ne_zero r
  have ht1 : t ≠ 1 := hasseRoot_ne_one
    (hassePolynomial_eval_one_ne_zero (K := K) p (by omega)) r
  have hell := curve_isElliptic h2 ht0 ht1
  refine ⟨t, hell, ?_, hasseRoot_eval r⟩
  letI := hell
  exact (curve_jInvariant t).trans hj

end IsogenyAttack.Legendre
