import IsogenyAttack.TargetSampler
import IsogenyAttack.StationaryRootLaw
import IsogenyAttack.LegendreCurve

/-!
An unconditional specialization to the explicitly constructed Hasse-root j-law.
This eliminates the old point-mass hypothesis for that law. It is not an
identification with the paper's supersingular stationary law: that geometric
identification, and the geometric kernel-to-codomain map, are still required.
-/
namespace IsogenyAttack
open Legendre

variable {K : Type*} [Field K] [DecidableEq K] [IsAlgClosed K]

omit [IsAlgClosed K] in
/-- Each parameter in the characteristic-p Hasse-root law defines a genuine
nonsingular Mathlib Legendre elliptic curve. -/
theorem hasse_root_curve_isElliptic (p : ℕ) [CharP K p] [Fact p.Prime]
    (hp : 2 < p) (t : HasseRoot (K := K) ((p-1)/2)) :
    (curve t.val).IsElliptic := by
  exact curve_isElliptic (small_natCast_ne_zero p (by decide) hp)
    (hasseRoot_ne_zero t)
    (hasseRoot_ne_one (hassePolynomial_eval_one_ne_zero p (by omega)) t)

/-- The concrete Hasse-root law satisfies the attack's exact finite bound.
The remaining codomain parameter is deliberately not called an elliptic
quotient: no such construction is smuggled into this theorem's hypotheses. -/
theorem hasse_sampler_attack (p : ℕ) [CharP K p] [Fact p.Prime]
    {B s : ℕ} (hs : 784 ≤ s) (hp : 49 ≤ p) (hB : 8 * s ^ 2 ≤ B)
    (hcut : (B : ℝ) ^ 2 < 4 * (p : ℝ))
    (codomain : HNF → HasseJClass (K := K) ((p-1)/2)) :
    1 / (1024 * (s : ℝ) ^ 3) ≤
      |(printedLaw B (cutoff_positive hs hB)).eventMass
          (fun k => publicTest B s (some k.val.cyclicDegree) = true) -
        (targetFirstLaw (hasseInvariantLaw (K := K) p (by omega)) B codomain).eventMass
          (fun x => publicTest B s ((targetComponent x).map HNF.degree) = true)| := by
  apply explicit_samplers_attack (hasseInvariantLaw (K := K) p (by omega)) codomain (p : ℝ)
      hs (by exact_mod_cast hp) hB hcut
  exact hasseInvariantLaw_mass_le p (by omega)

end IsogenyAttack
