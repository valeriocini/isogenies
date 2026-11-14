import IsogenyAttack.IsogenySampler
import IsogenyAttack.EllipticKernels
import IsogenyAttack.PublicObservation
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.Torsion.Structure

/-! Total positive-degree cyclic continuation samplers for Algorithms 5 and 6. -/
namespace IsogenyAttack.HintContinuation

open WeierstrassCurve WeierstrassCurve.Affine TauCeti IsogenySampler
noncomputable section
open scoped Classical

variable {K : Type*} [Field K] [IsAlgClosed K]
    (W : Affine K) [W.IsElliptic]

/-- An actual cyclic subgroup of every positive order invertible in the field. -/
theorem exists_cyclic_subgroup (d : ℕ) (hd : (d : K) ≠ 0) :
    ∃ S : AddSubgroup W.Point, Nat.card S = d ∧ IsAddCyclic S := by
  have hd0 : 0 < d := Nat.pos_of_ne_zero (by intro h; simp [h] at hd)
  let : NeZero d := ⟨hd0.ne'⟩
  obtain ⟨b⟩ := W.torsion_addEquiv_prod d hd
  let h := HNF.lift 1 d 0 (by decide) hd0 hd0
  have hdegree : h.degree = d := by simp [h]
  let S := ((ambientHNFEquiv hd0 b).symm ⟨h, hdegree⟩).val
  have hS : Nat.card S = d := ((ambientHNFEquiv hd0 b).symm ⟨h, hdegree⟩).property
  refine ⟨S, hS, ?_⟩
  have hc := (ambientHNF_inverse_code_spec hd0 b ⟨h, hdegree⟩).2.1
  have hone : nsmulAddMonoidHom (α := W.Point) 1 = AddMonoidHom.id W.Point := by
    ext x
    simp
  have hcontent : h.content = 1 := by simp [h]
  change IsAddCyclic (S.map (nsmulAddMonoidHom h.content)) at hc
  rwa [hcontent, hone, AddSubgroup.map_id] at hc

/-- All actual cyclic degree-d morphisms, retaining their Montgomery target. -/
abbrev CyclicMaps (d : ℕ) :=
  {φ : DegreeMaps W d // IsAddCyclic (pointKernel W φ.2.val)}

@[reducible] def degreeKernelFintype (d : ℕ) (hd : (d : K) ≠ 0) :
    Fintype (DegreeKernel W d) := by
  have hd0 : 0 < d := Nat.pos_of_ne_zero (by intro h; simp [h] at hd)
  letI : NeZero d := ⟨hd0.ne'⟩
  let b := Classical.choice (W.torsion_addEquiv_prod d hd)
  exact Fintype.ofEquiv {h : HNF // h.degree = d} (ambientHNFEquiv hd0 b).symm

@[reducible] def cyclicMapsFintype (d : ℕ) (hd : (d : K) ≠ 0)
    (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) : Fintype (CyclicMaps W d) := by
  letI : NeZero d := ⟨by intro h; simp [h] at hd⟩
  letI := degreeKernelFintype W d hd
  letI : Finite (DegreeMaps W d) := degreeMaps_finite W d h2 h3
  exact Fintype.ofFinite _

theorem cyclicMaps_nonempty (d : ℕ) (hd : (d : K) ≠ 0)
    (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) : Nonempty (CyclicMaps W d) := by
  obtain ⟨S, hS, hcyc⟩ := exists_cyclic_subgroup W d hd
  have hd0 : d ≠ 0 := by intro h; simp [h] at hd
  let : Finite S := Nat.finite_of_card_ne_zero (hS ▸ hd0)
  obtain ⟨A, φ⟩ := montgomeryMapsWithKernel_nonempty W S h2 h3
  refine ⟨⟨⟨A, φ.val, (fixedKernelMaps_degree W _ S φ).trans hS, φ.property.2⟩, ?_⟩⟩
  change IsAddCyclic (pointKernel W φ.val)
  rw [pointKernel_eq_of_ker_eq W φ.val S φ.property.1]
  exact hcyc

/-- A normalized finite uniform law on all genuine cyclic degree-d maps.
No unproved existence or sampler-totality premise occurs. -/
def cyclicLaw (d : ℕ) (hd : (d : K) ≠ 0)
    (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) :
    @FiniteLaw (CyclicMaps W d) (cyclicMapsFintype W d hd h2 h3) := by
  letI := cyclicMapsFintype W d hd h2 h3
  letI := cyclicMaps_nonempty W d hd h2 h3
  exact FiniteLaw.uniform _

theorem cyclicLaw_mass (d : ℕ) (hd : (d : K) ≠ 0)
    (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) (φ : CyclicMaps W d) :
    letI := cyclicMapsFintype W d hd h2 h3
    (cyclicLaw W d hd h2 h3).mass φ = 1 / (Nat.card (CyclicMaps W d) : ℝ) := by
  let := cyclicMapsFintype W d hd h2 h3
  simp only [cyclicLaw, FiniteLaw.uniform, Fintype.card_eq_nat_card]

/-- The interior degree condition makes the complementary degree positive,
less than the characteristic, and coprime to the original cyclic degree. It
also bounds the freshly resampled two-primary degree. -/
theorem algorithm5_complement_bounds {p e n d : ℕ} (hd : Odd d)
    (hfirst : 2 ^ n * d < 2 ^ e) (hcut : 2 ^ e < p) :
    0 < 2 ^ (e - n) - d ∧ 2 ^ (e - n) - d < p ∧
      (2 ^ n * d).Coprime (2 ^ (e - n) - d) ∧ 2 ^ n < p := by
  have hpowle : 2 ^ n ≤ 2 ^ n * d := Nat.le_mul_of_pos_right _ hd.pos
  have hn : n < e := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp
    (hpowle.trans_lt hfirst)
  have he : 2 ^ n * 2 ^ (e - n) = 2 ^ e := by
    rw [← pow_add, Nat.add_sub_of_le hn.le]
  have hdlt : d < 2 ^ (e - n) := Nat.lt_of_mul_lt_mul_left (by rwa [he])
  have hsmall : 2 ^ (e - n) ≤ 2 ^ e := Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)
  exact ⟨Nat.sub_pos_of_lt hdlt,
    (Nat.sub_le _ _).trans_lt (hsmall.trans_lt hcut),
    IsogenyPush.algorithm5_degrees_coprime n (e - n) d hd hdlt,
    hpowle.trans_lt (hfirst.trans hcut)⟩

variable (p : ℕ) [CharP K p]

/-- Algorithm 5 line 5, and the identical complementary step of Experiment 3,
have a nonempty finite cyclic-map sample space at every interior first degree. -/
theorem complement_nonempty (hp : 3 < p) (e n d : ℕ)
    (hd : Odd d) (hfirst : 2 ^ n * d < 2 ^ e) (hcut : 2 ^ e < p) :
    Nonempty (CyclicMaps W (2 ^ (e - n) - d)) := by
  obtain ⟨hcpos, hcp, -, -⟩ := algorithm5_complement_bounds hd hfirst hcut
  exact cyclicMaps_nonempty W _ (Legendre.small_natCast_ne_zero p hcpos hcp)
    (Legendre.small_natCast_ne_zero p (k := 2) (by decide) (by omega))
    (Legendre.small_natCast_ne_zero p (k := 3) (by decide) hp)

/-- The actual normalized complementary sampler, with its existence proved
from the positive interior degree inequality. -/
def complementLaw (hp : 3 < p) (e n d : ℕ)
    (hd : Odd d) (hfirst : 2 ^ n * d < 2 ^ e) (hcut : 2 ^ e < p) :=
  cyclicLaw W (2 ^ (e - n) - d)
    (Legendre.small_natCast_ne_zero p
      (algorithm5_complement_bounds hd hfirst hcut).1
      (algorithm5_complement_bounds hd hfirst hcut).2.1)
    (Legendre.small_natCast_ne_zero p (k := 2) (by decide) (by omega))
    (Legendre.small_natCast_ne_zero p (k := 3) (by decide) hp)

/-- Algorithm 6's fresh two-primary map also has a nonempty sample space on
every elliptic intermediate curve. -/
theorem fresh_two_primary_nonempty (hp : 3 < p) (e n d : ℕ)
    (hd : Odd d) (hfirst : 2 ^ n * d < 2 ^ e) (hcut : 2 ^ e < p) :
    Nonempty (CyclicMaps W (2 ^ n)) :=
  cyclicMaps_nonempty W _ (Legendre.small_natCast_ne_zero p (pow_pos (by decide) n)
    (algorithm5_complement_bounds hd hfirst hcut).2.2.2)
    (Legendre.small_natCast_ne_zero p (k := 2) (by decide) (by omega))
    (Legendre.small_natCast_ne_zero p (k := 3) (by decide) hp)

def freshTwoPrimaryLaw (hp : 3 < p) (e n d : ℕ)
    (hd : Odd d) (hfirst : 2 ^ n * d < 2 ^ e) (hcut : 2 ^ e < p) :=
  cyclicLaw W (2 ^ n) (Legendre.small_natCast_ne_zero p (pow_pos (by decide) n)
    (algorithm5_complement_bounds hd hfirst hcut).2.2.2)
    (Legendre.small_natCast_ne_zero p (k := 2) (by decide) (by omega))
    (Legendre.small_natCast_ne_zero p (k := 3) (by decide) hp)

/-- Every map in the fresh cyclic sampler supplies the actual finite cyclic
point kernel required by the geometric Algorithm 6 theorem. -/
theorem sampled_kernel (d : ℕ) (φ : CyclicMaps W d) :
    Nat.card (pointKernel W φ.val.2.val) = d ∧ IsAddCyclic (pointKernel W φ.val.2.val) := by
  exact ⟨(pointKernel_card W φ.val.2.val).trans (φ.val.2.property.2.trans φ.val.2.property.1),
    φ.property⟩

/-- The odd part of the composite in Algorithm 5 is the product of the odd
part of its first component and its complementary degree. -/
theorem algorithm5_composite_odd {e n d : ℕ} (hd : Odd d)
    (hfirst : 2 ^ n * d < 2 ^ e) : Odd (d * (2 ^ (e - n) - d)) := by
  have hpowle : 2 ^ n ≤ 2 ^ n * d := Nat.le_mul_of_pos_right _ hd.pos
  have hn : n < e := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp
    (hpowle.trans_lt hfirst)
  have he : 2 ^ n * 2 ^ (e - n) = 2 ^ e := by
    rw [← pow_add, Nat.add_sub_of_le hn.le]
  have hdlt : d < 2 ^ (e - n) := Nat.lt_of_mul_lt_mul_left (by rwa [he])
  exact hd.mul (Nat.Even.sub_odd hdlt.le
    ((by decide : Even 2).pow_of_ne_zero (by omega)) hd)

/-- Fresh two-primary kernels exist in every elliptic intermediate curve in
odd characteristic, independently of any upper degree cutoff. -/
theorem fresh_two_primary_kernel (h2 : (2 : K) ≠ 0) (n : ℕ) :
    ∃ R : AddSubgroup W.Point, Finite R ∧ IsAddCyclic R ∧ Nat.card R = 2 ^ n := by
  obtain ⟨R, hR, hc⟩ := exists_cyclic_subgroup W (2 ^ n) (by
    push_cast
    exact pow_ne_zero n h2)
  exact ⟨R, Nat.finite_of_card_ne_zero (hR ▸ (pow_pos (by decide) n).ne'), hc, hR⟩

end
end IsogenyAttack.HintContinuation

namespace IsogenyAttack.HintContinuation
open WeierstrassCurve WeierstrassCurve.Affine
noncomputable section
open scoped Classical

/-- Appending the actual uniform cyclic continuation changes no test of the
first component's degree, regardless of its dependence on the first outcome. -/
theorem continuation_degree_event {K α : Type*} [Field K] [IsAlgClosed K] [Fintype α]
    (P : FiniteLaw α) (V : α → Affine K) [∀ a, (V a).IsElliptic]
    (d : α → ℕ) (hd : ∀ a, (d a : K) ≠ 0)
    (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0)
    (degree : α → Option ℕ) (test : Option ℕ → Bool) :
    letI := fun a => cyclicMapsFintype (V a) (d a) (hd a) h2 h3
    (P.dependentBind (fun a => CyclicMaps (V a) (d a))
      (fun a => cyclicLaw (V a) (d a) (hd a) h2 h3)).eventMass
      (fun x => test (degree x.1) = true) =
      P.eventMass (fun a => test (degree a) = true) := by
  let := fun a => cyclicMapsFintype (V a) (d a) (hd a) h2 h3
  exact FiniteLaw.dependentBind_degree_observation P _ _ degree _ test (fun _ _ => rfl)

/-- A valid randomized encoding after drawing the continuation also preserves
the public degree decision exactly; decoder work is included by `program`. -/
theorem continuation_public_program {K α : Type*} [Field K] [IsAlgClosed K] [Fintype α]
    (P : FiniteLaw α) (V : α → Affine K) [∀ a, (V a).IsElliptic]
    (d : α → ℕ) (hd : ∀ a, (d a : K) ≠ 0)
    (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0)
    (degree : α → Option ℕ) (E : PublicObservation.PolynomialDegreeDecoder)
    (encode : (a : α) → CyclicMaps (V a) (d a) → List Bool)
    (B s : List Bool) (hs : 0 < BitComplexity.value s)
    (hencode : ∀ a b, E.degree (encode a b) = degree a) :
    letI := fun a => cyclicMapsFintype (V a) (d a) (hd a) h2 h3
    (P.dependentBind (fun a => CyclicMaps (V a) (d a))
      (fun a => cyclicLaw (V a) (d a) (hd a) h2 h3)).eventMass
      (fun x => (PublicObservation.program E B s (encode x.1 x.2)).result = true) =
      P.eventMass (fun a => publicTest (BitComplexity.value B) (BitComplexity.value s)
        (degree a) = true) := by
  let := fun a => cyclicMapsFintype (V a) (d a) (hd a) h2 h3
  exact FiniteLaw.dependentBind_public_program P _ _ degree E encode B s hs hencode

end
end IsogenyAttack.HintContinuation
