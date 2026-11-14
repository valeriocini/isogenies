import IsogenyAttack.Probability
import IsogenyAttack.Kernels

/-! Exact degree-first distribution on arithmetic kernel classes. -/

namespace IsogenyAttack

open scoped BigOperators

abbrev BoundedKernel (B : ℕ) := {x : HNF // x.degree ≤ B}
abbrev DegreeIndex (B : ℕ) := {d : ℕ // d ∈ Finset.Icc 1 B}

noncomputable def degreeNormalizer (w : ℕ → ℝ) (B : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 B, w d

/-- A degree fiber inside a sufficiently large bound contains every kernel. -/
def boundedDegreeEquiv (B d : ℕ) (hd : d ≤ B) :
    {x : BoundedKernel B // x.val.degree = d} ≃ {x : HNF // x.degree = d} where
  toFun x := ⟨x.val.val, x.property⟩
  invFun x := ⟨⟨x.val, by rw [x.property]; exact hd⟩, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- An arbitrary function of the degree sums once for every kernel class. -/
theorem sum_by_degree (B : ℕ) (f : ℕ → ℝ) :
    (∑ x : BoundedKernel B, f x.val.degree) =
      ∑ d ∈ Finset.Icc 1 B, (kernelCount d : ℝ) * f d := by
  classical
  have hf : ∀ x ∈ (Finset.univ : Finset (BoundedKernel B)),
      x.val.degree ∈ Finset.Icc 1 B := by
    intro x _
    exact Finset.mem_Icc.mpr ⟨x.val.degree_pos,x.property⟩
  rw [← Finset.sum_fiberwise_of_maps_to' hf f]
  apply Finset.sum_congr rfl
  intro d hd
  simp only [Finset.sum_const, nsmul_eq_mul]
  congr 1
  have hc : (Finset.univ.filter (fun x : BoundedKernel B => x.val.degree = d)).card =
      kernelCount d := by
    rw [← Fintype.card_subtype]
    exact (Fintype.card_congr (boundedDegreeEquiv B d (Finset.mem_Icc.mp hd).2)).trans
      (degree_card d)
  exact_mod_cast hc

/-- The unnormalized atom weights have the degree-weight normalizer exactly. -/
theorem kernel_weight_sum (B : ℕ) (w : ℕ → ℝ)
    (hcount : ∀ d ∈ Finset.Icc 1 B, 0 < kernelCount d) :
    (∑ x : BoundedKernel B, w x.val.degree / (kernelCount x.val.degree : ℝ)) =
      degreeNormalizer w B := by
  rw [sum_by_degree B (fun d => w d / (kernelCount d : ℝ))]
  unfold degreeNormalizer
  apply Finset.sum_congr rfl
  intro d hd
  have hc : (kernelCount d : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt (hcount d hd)
  field_simp

/-- Actual degree-first law: choose degree with weight `w`, then a uniform
kernel of that degree. This constructs the law and proves normalization. -/
noncomputable def degreeFirstLaw (B : ℕ) (w : ℕ → ℝ)
    (hw : ∀ d ∈ Finset.Icc 1 B, 0 ≤ w d)
    (hz : 0 < degreeNormalizer w B)
    (hcount : ∀ d ∈ Finset.Icc 1 B, 0 < kernelCount d) : FiniteLaw (BoundedKernel B) where
  mass x := w x.val.degree / (degreeNormalizer w B * (kernelCount x.val.degree : ℝ))
  mass_nonneg x := by
    have hd : x.val.degree ∈ Finset.Icc 1 B :=
      Finset.mem_Icc.mpr ⟨Nat.mul_pos x.val.a_pos x.val.e_pos,x.property⟩
    exact div_nonneg (hw _ hd) (mul_nonneg (le_of_lt hz) (Nat.cast_nonneg _))
  mass_sum := by
    calc
      (∑ x : BoundedKernel B,
          w x.val.degree / (degreeNormalizer w B * (kernelCount x.val.degree : ℝ))) =
          (∑ x : BoundedKernel B, w x.val.degree / (kernelCount x.val.degree : ℝ)) /
            degreeNormalizer w B := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro x _
        ring
      _ = 1 := by rw [kernel_weight_sum B w hcount, div_self (ne_of_gt hz)]

@[simp] theorem degreeFirstLaw_mass (B : ℕ) (w : ℕ → ℝ)
    (hw : ∀ d ∈ Finset.Icc 1 B, 0 ≤ w d)
    (hz : 0 < degreeNormalizer w B)
    (hcount : ∀ d ∈ Finset.Icc 1 B, 0 < kernelCount d)
    (x : BoundedKernel B) :
    (degreeFirstLaw B w hw hz hcount).mass x =
      w x.val.degree / (degreeNormalizer w B * (kernelCount x.val.degree : ℝ)) := rfl

end IsogenyAttack
