import IsogenyAttack.StationaryRootLaw
import IsogenyAttack.JFiberOrbit
import IsogenyAttack.CurveAutomorphisms

/-! Exact identification of the Hasse-root law with reciprocal-automorphism
weights on geometric elliptic-curve classes. -/
namespace IsogenyAttack.Legendre
open Polynomial Finset
variable {K : Type*} [Field K] [DecidableEq K] [IsAlgClosed K]

omit [IsAlgClosed K] in
/-- The full sextic fiber over a Hasse j-class consists of Hasse roots. -/
lemma hasse_j_fiber_root (p : ℕ) [CharP K p] [Fact p.Prime]
    {n : ℕ} (hp : p = 2*n+1) (h256 : (256 : K) ≠ 0)
    (j : HasseJClass (K := K) n) {t : K}
    (ht : (fiberPolynomial j.val).IsRoot t) :
    (hassePolynomial (K := K) n).IsRoot t := by
  obtain ⟨a, ha, haj⟩ := Finset.mem_image.mp j.property
  have ha' : (hassePolynomial (K := K) n).IsRoot a := by
    simpa only [Multiset.mem_toFinset, mem_roots (hassePolynomial_monic n).ne_zero] using ha
  apply fiber_root_is_hasse_root p hp h256 ha'
  simpa only [haj] using ht

/-- The exact fiber of the map on finite Hasse-root types is the full
geometric j-fiber, including its exceptional fibers. -/
noncomputable def hasseJFiberEquiv (p : ℕ) [CharP K p] [Fact p.Prime]
    {n : ℕ} (hp : p = 2*n+1) (h256 : (256 : K) ≠ 0)
    (j : HasseJClass (K := K) n) :
    {r : HasseRoot (K := K) n // hasseJMap r = j} ≃
      {t : K // t ∈ (fiberPolynomial j.val).roots.toFinset} where
  toFun r := ⟨r.val.val, by
    rw [Multiset.mem_toFinset, mem_roots (fiberPolynomial_ne_zero j.val h256)]
    apply fiberPolynomial_root (hasseRoot_ne_zero r.val)
      (hasseRoot_ne_one (hassePolynomial_eval_one_ne_zero p (by omega)) r.val)
    exact congrArg Subtype.val r.property⟩
  invFun t := ⟨⟨t.val, by
    rw [Multiset.mem_toFinset, mem_roots (hassePolynomial_monic n).ne_zero]
    apply hasse_j_fiber_root p hp h256 j
    simpa only [Multiset.mem_toFinset,
      mem_roots (fiberPolynomial_ne_zero j.val h256)] using t.property⟩, by
    apply Subtype.ext
    exact ((fiberPolynomial_isRoot_iff h256).mp (by
      simpa only [Multiset.mem_toFinset,
        mem_roots (fiberPolynomial_ne_zero j.val h256)] using t.property)).2.2⟩
  left_inv r := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv t := by apply Subtype.ext; rfl

/-- Each class has probability exactly its number of distinct Legendre
parameters divided by the total number of Hasse roots. -/
theorem hasseJLaw_mass_eq_fiber (p : ℕ) [CharP K p] [Fact p.Prime]
    {n : ℕ} (hp : p = 2*n+1) (hn : 0 < n) (h256 : (256 : K) ≠ 0)
    (hsep : (hassePolynomial (K := K) n).Separable)
    (j : HasseJClass (K := K) n) :
    (hasseJLaw n hn hsep).mass j =
      ((fiberPolynomial j.val).roots.toFinset.card : ℝ) / n := by
  letI := hasseRoot_nonempty n hn hsep
  change (FiniteLaw.uniform (HasseRoot (K := K) n)).eventMass
    (fun r => hasseJMap r = j) = _
  rw [FiniteLaw.uniform_event, hasseRoot_card n hsep,
    Fintype.card_congr (hasseJFiberEquiv p hp h256 j)]
  simp

/-- Exact generic and exceptional probabilities: 12, 4, and 6 divided by p−1. -/
theorem hasseInvariantLaw_mass_exact (p : ℕ) [CharP K p] [Fact p.Prime]
    (hp : 3 < p) (j : HasseJClass (K := K) ((p-1)/2)) :
    (hasseInvariantLaw (K := K) p (by omega)).mass j =
      (if j.val = 0 then 4 else if j.val = 1728 then 6 else 12) / ((p : ℝ)-1) := by
  have hn : 0 < (p-1)/2 := by omega
  have hpodd := (Fact.out : Nat.Prime p).odd_of_ne_two (by omega)
  obtain ⟨a, ha⟩ := hpodd
  have hpn : p = 2*((p-1)/2)+1 := by omega
  have h2 : (2 : K) ≠ 0 := small_natCast_ne_zero p (k := 2) (by decide) (by omega)
  have h3 : (3 : K) ≠ 0 := small_natCast_ne_zero p (by decide) hp
  have h256 : (256 : K) ≠ 0 := by
    have h := pow_ne_zero 8 h2
    norm_num at h
    exact h
  change (hasseJLaw ((p-1)/2) _ _).mass j = _
  rw [hasseJLaw_mass_eq_fiber p hpn hn h256]
  have hreal : (p : ℝ)-1 = 2*((p-1)/2 : ℕ) := by
    have h := congrArg (fun n : ℕ => (n : ℝ)) hpn
    push_cast at h
    linarith
  by_cases hj0 : j.val = 0
  · rw [hj0, zero_j_fiber_card h256 h3]
    simp only [ite_true, Nat.cast_ofNat]
    rw [hreal]
    ring
  · by_cases hj1728 : j.val = 1728
    · rw [if_neg hj0, if_pos hj1728, hj1728, exceptional_j_fiber_card h2 h3]
      simp only [Nat.cast_ofNat]
      rw [hreal]
      ring
    · rw [generic_j_fiber_card h256 hj0 hj1728, if_neg hj0, if_neg hj1728]
      simp only [Nat.cast_ofNat]
      rw [hreal]
      ring

/-- The explicit Hasse-root pushforward is exactly the stationary weight
24/((p−1)|Aut(E)|) for every actual elliptic model in the geometric class.
The automorphisms here are actual admissible Weierstrass coordinate changes. -/
theorem hasseInvariantLaw_eq_reciprocal_aut (p : ℕ) [CharP K p] [Fact p.Prime]
    (hp : 3 < p) (j : HasseJClass (K := K) ((p-1)/2))
    (W : WeierstrassCurve K) [W.IsElliptic] (hW : W.j = j.val) :
    (hasseInvariantLaw (K := K) p (by omega)).mass j =
      24 / (((p : ℝ)-1) * Nat.card (CurveAutomorphisms.CurveAut W)) := by
  rw [hasseInvariantLaw_mass_exact p hp j,
    CurveAutomorphisms.card_curveAut_by_j W
      (small_natCast_ne_zero p (k := 2) (by decide) (by omega))
      (small_natCast_ne_zero p (k := 3) (by decide) hp), hW]
  split_ifs <;> push_cast <;> simp only [mul_inv_rev, div_eq_mul_inv] <;> ring

end IsogenyAttack.Legendre
