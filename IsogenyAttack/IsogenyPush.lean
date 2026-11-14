import IsogenyAttack.Pushforward
import IsogenyAttack.VeluQuotient
import IsogenyAttack.BitComplexity
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Dual.Basic
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom.Ring

/-!
The geometric and public-observation parts of Algorithms 5--6.  The maps below
are Tau Ceti function-field isogenies.  Their dual identities, the finite
subgroup bijection, and the degrees of the resulting Vélu quotients are proved,
not fields of an abstract attack interface.
-/
namespace IsogenyAttack.IsogenyPush

open WeierstrassCurve WeierstrassCurve.Affine TauCeti

variable {K : Type*} [Field K] [DecidableEq K]
variable {W V : Affine K} [W.IsElliptic] [V.IsElliptic]

/-- The action of an actual geometric isogeny on the additive point group. -/
noncomputable abbrev pointHom (σ : Isogeny W V) : W.Point →+ V.Point :=
  (Isogeny.Hom.ofIsogeny σ).pointMapHom

theorem dual_pointHom (σ : Isogeny W V) (P : W.Point) :
    pointHom σ.dual (pointHom σ P) = σ.degree • P :=
  σ.pointMap_dual_pointMap P

theorem pointHom_dual (σ : Isogeny W V) (P : V.Point) :
    pointHom σ (pointHom σ.dual P) = σ.degree • P :=
  σ.pointMap_pointMap_dual P

theorem pointHom_eq_toPointHom [IsSepClosed K] (σ : Isogeny W V)
    [Algebra.IsSeparable σ.fieldPullback.fieldRange W.FunctionField] :
    pointHom σ = σ.toPointHom := by
  ext P
  exact Isogeny.Hom.pointMap_ofIsogeny_eq_toPointHom σ P

theorem pointHom_comp {U : Affine K} [U.IsElliptic]
    (τ : Isogeny V U) (σ : Isogeny W V) (P : W.Point) :
    pointHom (τ.comp σ) P = pointHom τ (pointHom σ P) := by
  exact (congrArg (fun f : Isogeny.Hom W U => f.pointMap P)
    (Isogeny.Hom.ofIsogeny_comp_ofIsogeny τ σ)).symm.trans
      (Isogeny.Hom.comp_pointMap _ _ _)

/-- Coprime kernel pushing, instantiated with the proved geometric dual. -/
noncomputable def kernelEquiv (σ : Isogeny W V) (d : ℕ)
    (hd : d.Coprime σ.degree) :
    Pushforward.KernelsOfOrder d W.Point ≃ Pushforward.KernelsOfOrder d V.Point :=
  Pushforward.kernelPushBijection d σ.degree (pointHom σ) (pointHom σ.dual)
    (dual_pointHom σ) (pointHom_dual σ) hd

/-- Algorithm 6's odd part is transported bijectively by any power-of-two
challenge.  No kernel or duality assertion is an input hypothesis. -/
noncomputable def oddKernelEquiv (σ : Isogeny W V) (d k : ℕ)
    (hσ : σ.degree = 2 ^ k) (hd : Odd d) :
    Pushforward.KernelsOfOrder d W.Point ≃ Pushforward.KernelsOfOrder d V.Point :=
  kernelEquiv σ d (hσ ▸ Nat.Coprime.pow_right k hd.coprime_two_right)

noncomputable def cyclicKernelEquiv (σ : Isogeny W V) (d : ℕ)
    (hd : d.Coprime σ.degree) :
    {S : Pushforward.KernelsOfOrder d W.Point // IsAddCyclic S.val} ≃
      {S : Pushforward.KernelsOfOrder d V.Point // IsAddCyclic S.val} :=
  Pushforward.cyclicKernelPushBijection d σ.degree (pointHom σ) (pointHom σ.dual)
    (dual_pointHom σ) (pointHom_dual σ) hd

theorem push_card (σ : Isogeny W V) (S : AddSubgroup W.Point)
    (hcop : (Nat.card S).Coprime σ.degree) :
    Nat.card (S.map (pointHom σ)) = Nat.card S :=
  Pushforward.card_push_of_dual (pointHom σ) (pointHom σ.dual) σ.degree
    (dual_pointHom σ) S hcop

theorem push_cyclic_iff (σ : Isogeny W V) (S : AddSubgroup W.Point)
    (hcop : (Nat.card S).Coprime σ.degree) :
    IsAddCyclic (S.map (pointHom σ)) ↔ IsAddCyclic S :=
  (Pushforward.cyclic_push_iff_of_dual (pointHom σ) (pointHom σ.dual) σ.degree
    (dual_pointHom σ) S hcop).symm

theorem push_dual_cancel (σ : Isogeny W V) (S : AddSubgroup W.Point)
    (hcop : (Nat.card S).Coprime σ.degree) :
    (S.map (pointHom σ)).map (pointHom σ.dual) = S :=
  Pushforward.push_dual_cancel (pointHom σ) (pointHom σ.dual) σ.degree
    (dual_pointHom σ) S hcop

/-- The pushed map is an actual elliptic quotient, not a group quotient. -/
instance pushedKernel_finite (σ : Isogeny W V) (S : AddSubgroup W.Point)
    [Finite S] : Finite (S.map (pointHom σ)) :=
  Finite.of_surjective _ ((pointHom σ).addSubgroupMap_surjective S)

noncomputable abbrev pushedIsogeny (σ : Isogeny W V) (S : AddSubgroup W.Point)
    [Finite S] := quotientIsogeny V (S.map (pointHom σ))

theorem pushedIsogeny_degree (σ : Isogeny W V) (S : AddSubgroup W.Point)
    [Finite S] (hcop : (Nat.card S).Coprime σ.degree) :
    (pushedIsogeny σ S).degree = Nat.card S := by
  rw [pushedIsogeny, quotientIsogeny_degree, push_card σ S hcop]

theorem pushedIsogeny_degree_eq (σ : Isogeny W V) (S : AddSubgroup W.Point)
    [Finite S] (hcop : (Nat.card S).Coprime σ.degree) :
    (pushedIsogeny σ S).degree = (quotientIsogeny W S).degree := by
  rw [pushedIsogeny_degree σ S hcop, quotientIsogeny_degree]

/-- The pushed quotient fits in the actual commuting isogeny square. -/
theorem pushed_square [IsAlgClosed K] (σ : Isogeny W V)
    [Algebra.IsSeparable σ.fieldPullback.fieldRange W.FunctionField]
    (S : AddSubgroup W.Point) [Finite S] :
    ∃! τ : Isogeny (quotientCurve W S).toAffine
        (quotientCurve V (S.map (pointHom σ))).toAffine,
      τ.comp (quotientIsogeny W S) = (pushedIsogeny σ S).comp σ := by
  have := Isogeny.isSeparable_comp (pushedIsogeny σ S) σ
  apply (Isogeny.existsUnique_comp_eq_iff_ker_le
    (quotientIsogeny W S).card_ker_eq_degree ((pushedIsogeny σ S).comp σ)).mpr
  rw [quotientIsogeny_kernel]
  rintro _ ⟨P, hP, rfl⟩
  apply (Isogeny.mem_ker_iff_toPointHom_eq_zero _ _).mpr
  rw [← pointHom_eq_toPointHom, pointHom_comp,
    pointHom_eq_toPointHom (pushedIsogeny σ S)]
  change pointHom σ P ∈ (pushedIsogeny σ S).toPointHom.ker
  rw [pushedIsogeny, quotientIsogeny_point_kernel]
  exact ⟨P, hP, rfl⟩

/-- Under inclusion of finite kernels, the geometric quotient factors through
the smaller geometric quotient. -/
theorem quotient_factor (S T : AddSubgroup W.Point) [Finite S] [Finite T]
    (hST : S ≤ T) :
    ∃! χ : Isogeny (quotientCurve W S).toAffine (quotientCurve W T).toAffine,
      χ.comp (quotientIsogeny W S) = quotientIsogeny W T := by
  apply (Isogeny.existsUnique_comp_eq_iff_ker_le
    (φ := quotientIsogeny W S) ?_ (quotientIsogeny W T)).mpr
  · rw [quotientIsogeny_kernel, quotientIsogeny_kernel]
    exact AddSubgroup.map_mono hST
  · rw [quotientIsogeny_kernel, quotientIsogeny_degree]
    exact (Nat.card_congr ((Point.equivBaseChangeSelf W).addSubgroupMap S).toEquiv).symm

/-- Every requested divisor of a cyclic geometric quotient is the degree of
an actual first component with the same final target. This implements the
existence assertion in Algorithm 6, line 6. -/
theorem split_cyclic_quotient (S : AddSubgroup W.Point) [Finite S] [IsAddCyclic S]
    (c : ℕ) (hc : c ∣ Nat.card S) :
    ∃ (T : AddSubgroup W.Point) (_ : Finite T),
      T ≤ S ∧ Nat.card T = c ∧
      ∃ χ : Isogeny (quotientCurve W T).toAffine (quotientCurve W S).toAffine,
        χ.comp (quotientIsogeny W T) = quotientIsogeny W S ∧
        (quotientIsogeny W T).degree = c ∧ χ.degree * c = Nat.card S := by
  obtain ⟨A, hA, _⟩ := Pushforward.existsUnique_cyclic_subgroup (G := S) c hc
  let T : AddSubgroup W.Point := A.map S.subtype
  have : Finite T := Finite.of_surjective _ (S.subtype.addSubgroupMap_surjective A)
  have hTS : T ≤ S := by
    rintro x ⟨y, _, rfl⟩
    exact y.property
  have hT : Nat.card T = c := by
    exact (Nat.card_congr (A.equivMapOfInjective S.subtype Subtype.val_injective).toEquiv).symm.trans hA
  obtain ⟨χ, hχ, _⟩ := quotient_factor T S hTS
  refine ⟨T, inferInstance, hTS, hT, χ, hχ, ?_, ?_⟩
  · rw [quotientIsogeny_degree, hT]
  · have hh := congrArg Isogeny.degree hχ
    simpa only [Isogeny.degree_comp, quotientIsogeny_degree, hT] using hh

/-- The canonical subgroup of order `d` of a finite cyclic subgroup. -/
def degreeSubgroup (S : AddSubgroup W.Point) (d : ℕ) : AddSubgroup W.Point :=
  (Pushforward.scalarHom d : S →+ S).ker.map S.subtype

instance degreeSubgroup_finite (S : AddSubgroup W.Point) [Finite S] (d : ℕ) :
    Finite (degreeSubgroup S d) :=
  Finite.of_surjective _ (S.subtype.addSubgroupMap_surjective _)

instance degreeSubgroup_cyclic (S : AddSubgroup W.Point) [IsAddCyclic S] (d : ℕ) :
    IsAddCyclic (degreeSubgroup S d) := Pushforward.cyclic_push _ _

omit [W.IsElliptic] in
theorem degreeSubgroup_le (S : AddSubgroup W.Point) (d : ℕ) : degreeSubgroup S d ≤ S := by
  rintro _ ⟨x, _, rfl⟩
  exact x.property

omit [W.IsElliptic] in
theorem degreeSubgroup_card (S : AddSubgroup W.Point) [Finite S] [IsAddCyclic S]
    (d : ℕ) (hd : d ∣ Nat.card S) : Nat.card (degreeSubgroup S d) = d := by
  exact ((Nat.card_congr
    (((Pushforward.scalarHom d : S →+ S).ker).equivMapOfInjective
      S.subtype Subtype.val_injective).toEquiv).symm).trans
        (Pushforward.cyclic_torsion_card (G := S) d hd)

/-- Cyclic kernels of coprime orders remain cyclic under composition of
surjective homomorphisms. -/
theorem cyclic_comp_kernel {A B C : Type*} [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup C] (f : A →+ B) (g : B →+ C) (hf : Function.Surjective f)
    [IsAddCyclic f.ker] [IsAddCyclic g.ker]
    (hcop : (Nat.card f.ker).Coprime (Nat.card g.ker)) :
    IsAddCyclic (g.comp f).ker := by
  let r : (g.comp f).ker →+ g.ker :=
    { toFun := fun x => ⟨f x.val, x.property⟩
      map_zero' := Subtype.ext (map_zero f)
      map_add' := fun x y => Subtype.ext (map_add f x.val y.val) }
  let e : f.ker ≃+ r.ker :=
    { toFun := fun x => ⟨⟨x.val, by change g (f x.val) = 0; rw [x.property, map_zero]⟩,
        by apply Subtype.ext; exact x.property⟩
      invFun := fun x => ⟨x.val.val, congrArg Subtype.val x.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl }
  have : IsAddCyclic r.ker := isAddCyclic_of_surjective e e.surjective
  apply AddGroup.isAddCyclic_of_coprime_card_ker r
    (by rwa [← Nat.card_congr e.toEquiv])
  intro y
  obtain ⟨x, hx⟩ := hf y.val
  refine ⟨⟨x, ?_⟩, Subtype.ext hx⟩
  change g (f x) = 0
  rw [hx]
  exact y.property

theorem toPointHom_comp [IsAlgClosed K] {U : Affine K} [U.IsElliptic]
    (τ : Isogeny V U) (σ : Isogeny W V)
    [Algebra.IsSeparable τ.fieldPullback.fieldRange V.FunctionField]
    [Algebra.IsSeparable σ.fieldPullback.fieldRange W.FunctionField] :
    (τ.comp σ).toPointHom = τ.toPointHom.comp σ.toPointHom := by
  have := Isogeny.isSeparable_comp τ σ
  ext P
  rw [← pointHom_eq_toPointHom (τ.comp σ), pointHom_comp,
    pointHom_eq_toPointHom τ, pointHom_eq_toPointHom σ]
  rfl

/-- The cyclicity premise for the total hint is derived from its two actual
cyclic isogenies and their coprime degrees. -/
theorem cyclic_isogeny_comp [IsAlgClosed K] {U : Affine K} [U.IsElliptic]
    (τ : Isogeny V U) (σ : Isogeny W V)
    [Algebra.IsSeparable τ.fieldPullback.fieldRange V.FunctionField]
    [Algebra.IsSeparable σ.fieldPullback.fieldRange W.FunctionField]
    [IsAddCyclic τ.toPointHom.ker] [IsAddCyclic σ.toPointHom.ker]
    (hcop : σ.degree.Coprime τ.degree) : IsAddCyclic (τ.comp σ).toPointHom.ker := by
  rw [toPointHom_comp τ σ]
  exact cyclic_comp_kernel σ.toPointHom τ.toPointHom σ.toPointHom_surjective
    (by simpa only [Isogeny.card_ker_toPointHom_eq_degree] using hcop)

/-- Split an arbitrary actual cyclic separable isogeny at a divisor of its
degree, retaining its actual target curve. -/
theorem split_cyclic_isogeny [IsAlgClosed K] (φ : Isogeny W V)
    [Algebra.IsSeparable φ.fieldPullback.fieldRange W.FunctionField]
    [IsAddCyclic φ.toPointHom.ker] (c : ℕ) (hc : c ∣ φ.degree) :
    ∃ χ : Isogeny (quotientCurve W (degreeSubgroup φ.toPointHom.ker c)).toAffine V,
      χ.comp (quotientIsogeny W (degreeSubgroup φ.toPointHom.ker c)) = φ ∧
      (quotientIsogeny W (degreeSubgroup φ.toPointHom.ker c)).degree = c ∧
      χ.degree * c = φ.degree := by
  let T := degreeSubgroup φ.toPointHom.ker c
  have hT : Nat.card T = c := degreeSubgroup_card _ _
    (by simpa only [Isogeny.card_ker_toPointHom_eq_degree] using hc)
  obtain ⟨χ, hχ, _⟩ := (Isogeny.existsUnique_comp_eq_iff_ker_le
    (quotientIsogeny W T).card_ker_eq_degree φ).mpr (by
      rw [quotientIsogeny_kernel, Isogeny.ker_eq_map_ker_toPointHom]
      exact AddSubgroup.map_mono (degreeSubgroup_le _ _))
  refine ⟨χ, hχ, ?_, ?_⟩
  · rw [quotientIsogeny_degree, hT]
  · have hh := congrArg Isogeny.degree hχ
    simpa only [Isogeny.degree_comp, quotientIsogeny_degree, hT] using hh

/-- Algorithm 6, lines 3--5: push the selected odd kernel and append the
freshly sampled cyclic two-primary kernel. -/
noncomputable abbrev rebuiltIsogeny (σ : Isogeny W V) (O : AddSubgroup W.Point)
    [Finite O]
    (R : AddSubgroup (quotientCurve V (O.map (pointHom σ))).toAffine.Point) [Finite R] :=
  (quotientIsogeny _ R).comp (pushedIsogeny σ O)

instance rebuiltIsogeny_separable (σ : Isogeny W V) (O : AddSubgroup W.Point)
    [Finite O]
    (R : AddSubgroup (quotientCurve V (O.map (pointHom σ))).toAffine.Point) [Finite R] :
    Algebra.IsSeparable (rebuiltIsogeny σ O R).fieldPullback.fieldRange V.FunctionField :=
  Isogeny.isSeparable_comp _ _

theorem rebuiltIsogeny_degree (σ : Isogeny W V) (O : AddSubgroup W.Point)
    [Finite O]
    (R : AddSubgroup (quotientCurve V (O.map (pointHom σ))).toAffine.Point) [Finite R]
    (hcop : (Nat.card O).Coprime σ.degree) :
    (rebuiltIsogeny σ O R).degree = Nat.card R * Nat.card O := by
  rw [rebuiltIsogeny, Isogeny.degree_comp, quotientIsogeny_degree,
    pushedIsogeny_degree σ O hcop]

theorem rebuiltIsogeny_cyclic [IsAlgClosed K] (σ : Isogeny W V)
    (O : AddSubgroup W.Point) [Finite O] [IsAddCyclic O]
    (R : AddSubgroup (quotientCurve V (O.map (pointHom σ))).toAffine.Point)
    [Finite R] [IsAddCyclic R]
    (hσ : (Nat.card O).Coprime σ.degree)
    (hR : (Nat.card O).Coprime (Nat.card R)) :
    IsAddCyclic (rebuiltIsogeny σ O R).toPointHom.ker := by
  have : IsAddCyclic (pushedIsogeny σ O).toPointHom.ker := by
    rw [pushedIsogeny, quotientIsogeny_point_kernel]
    exact Pushforward.cyclic_push _ _
  have : IsAddCyclic (quotientIsogeny _ R).toPointHom.ker := by
    rw [quotientIsogeny_point_kernel]
    infer_instance
  exact cyclic_isogeny_comp (quotientIsogeny _ R) (pushedIsogeny σ O)
    (by simpa only [pushedIsogeny_degree σ O hσ, quotientIsogeny_degree] using hR)

/-- The actual first isogeny returned at Algorithm 6, line 6. It is the
canonical geometric quotient of the rebuilt source by its subgroup of order c. -/
noncomputable abbrev algorithm6First [IsAlgClosed K] (σ : Isogeny W V)
    (O : AddSubgroup W.Point) [Finite O]
    (R : AddSubgroup (quotientCurve V (O.map (pointHom σ))).toAffine.Point) [Finite R]
    (c : ℕ) :=
  quotientIsogeny V (degreeSubgroup (rebuiltIsogeny σ O R).toPointHom.ker c)

theorem algorithm6First_degree [IsAlgClosed K] (σ : Isogeny W V)
    (O : AddSubgroup W.Point) [Finite O] [IsAddCyclic O]
    (R : AddSubgroup (quotientCurve V (O.map (pointHom σ))).toAffine.Point)
    [Finite R] [IsAddCyclic R] (c : ℕ)
    (hσ : (Nat.card O).Coprime σ.degree)
    (hR : (Nat.card O).Coprime (Nat.card R))
    (hc : c ∣ Nat.card R * Nat.card O) : (algorithm6First σ O R c).degree = c := by
  have : IsAddCyclic (rebuiltIsogeny σ O R).toPointHom.ker :=
    rebuiltIsogeny_cyclic σ O R hσ hR
  apply (quotientIsogeny_degree V _).trans
  apply degreeSubgroup_card
  rw [Isogeny.card_ker_toPointHom_eq_degree, rebuiltIsogeny_degree σ O R hσ]
  exact hc

/-- The canonical first component has an actual second component into the
rebuilt target. Both public component degrees are therefore attained. -/
theorem algorithm6First_factor [IsAlgClosed K] (σ : Isogeny W V)
    (O : AddSubgroup W.Point) [Finite O] [IsAddCyclic O]
    (R : AddSubgroup (quotientCurve V (O.map (pointHom σ))).toAffine.Point)
    [Finite R] [IsAddCyclic R] (c : ℕ)
    (hσ : (Nat.card O).Coprime σ.degree)
    (hR : (Nat.card O).Coprime (Nat.card R))
    (hc : c ∣ Nat.card R * Nat.card O) :
    ∃ χ : Isogeny
      (quotientCurve V (degreeSubgroup (rebuiltIsogeny σ O R).toPointHom.ker c)).toAffine
      (quotientCurve _ R).toAffine,
      χ.comp (algorithm6First σ O R c) = rebuiltIsogeny σ O R ∧
      χ.degree * c = Nat.card R * Nat.card O := by
  have : IsAddCyclic (rebuiltIsogeny σ O R).toPointHom.ker :=
    rebuiltIsogeny_cyclic σ O R hσ hR
  have hdiv : c ∣ (rebuiltIsogeny σ O R).degree := by
    rw [rebuiltIsogeny_degree σ O R hσ]
    exact hc
  obtain ⟨χ, hχ, _, hdegree⟩ := split_cyclic_isogeny (rebuiltIsogeny σ O R) c hdiv
  exact ⟨χ, hχ, hdegree.trans (rebuiltIsogeny_degree σ O R hσ)⟩

/-- An actual two-isogeny output, with its composite and observed first degree. -/
def HasSplit {W V : Affine K} (φ : Isogeny W V) (c : ℕ) : Prop :=
  ∃ M : Affine K, M.IsElliptic ∧
    ∃ (first : Isogeny W M) (second : Isogeny M V),
      second.comp first = φ ∧ first.degree = c

theorem hasSplit_of_cyclic [IsAlgClosed K] (φ : Isogeny W V)
    [Algebra.IsSeparable φ.fieldPullback.fieldRange W.FunctionField]
    [IsAddCyclic φ.toPointHom.ker] (c : ℕ) (hc : c ∣ φ.degree) : HasSplit φ c := by
  obtain ⟨χ, hχ, hfirst, _⟩ := split_cyclic_isogeny φ c hc
  exact ⟨_, inferInstance, _, χ, hχ, hfirst⟩

set_option maxHeartbeats 1200000 in
/-- Concrete correctness of Algorithm 6. The odd component is selected as
the unique subgroup of its degree, transported by the actual challenge, and
composed with any fresh cyclic `2^n` kernel. The final two maps are constructed
by geometric factorization, and the first has the prescribed original degree.
No hypothesis about a returned split or its degree is assumed. -/
theorem algorithm6_output [IsAlgClosed K] {U : Affine K} [U.IsElliptic]
    (φ : Isogeny W U)
    [Algebra.IsSeparable φ.fieldPullback.fieldRange W.FunctionField]
    [IsAddCyclic φ.toPointHom.ker]
    (σ : Isogeny W V) (k n d c : ℕ)
    (hσ : σ.degree = 2 ^ k) (hd : Odd d) (hφ : φ.degree = 2 ^ n * d)
    (hc : c ∣ φ.degree)
    (R : AddSubgroup (quotientCurve V
      ((degreeSubgroup φ.toPointHom.ker d).map (pointHom σ))).toAffine.Point)
    [Finite R] [IsAddCyclic R] (hR : Nat.card R = 2 ^ n) :
    HasSplit (rebuiltIsogeny σ (degreeSubgroup φ.toPointHom.ker d) R) c ∧
      (rebuiltIsogeny σ (degreeSubgroup φ.toPointHom.ker d) R).degree = φ.degree := by
  let O := degreeSubgroup φ.toPointHom.ker d
  have hO : Nat.card O = d := degreeSubgroup_card _ d (by
    rw [Isogeny.card_ker_toPointHom_eq_degree, hφ]
    exact Nat.dvd_mul_left d (2 ^ n))
  have hOσ : (Nat.card O).Coprime σ.degree := by
    rw [hO, hσ]
    exact hd.coprime_two_right.pow_right k
  have hOR : (Nat.card O).Coprime (Nat.card R) := by
    rw [hO, hR]
    exact hd.coprime_two_right.pow_right n
  let ψ := rebuiltIsogeny σ O R
  have : Algebra.IsSeparable ψ.fieldPullback.fieldRange V.FunctionField :=
    rebuiltIsogeny_separable σ O R
  have : IsAddCyclic ψ.toPointHom.ker := rebuiltIsogeny_cyclic σ O R hOσ hOR
  have hψ : ψ.degree = φ.degree :=
    (rebuiltIsogeny_degree σ O R hOσ).trans (by rw [hO, hR, hφ])
  have hdiv : c ∣ ψ.degree := by rw [hψ]; exact hc
  exact ⟨hasSplit_of_cyclic ψ c hdiv, hψ⟩

/-- The explicit first output map has the input degree c; the odd kernel and
fresh two-primary kernel are those appearing in `algorithm6_output`. -/
theorem algorithm6First_degree_of_input [IsAlgClosed K] {U : Affine K} [U.IsElliptic]
    (φ : Isogeny W U)
    [Algebra.IsSeparable φ.fieldPullback.fieldRange W.FunctionField]
    [IsAddCyclic φ.toPointHom.ker]
    (σ : Isogeny W V) (k n d c : ℕ)
    (hσ : σ.degree = 2 ^ k) (hd : Odd d) (hφ : φ.degree = 2 ^ n * d)
    (hc : c ∣ φ.degree)
    (R : AddSubgroup (quotientCurve V
      ((degreeSubgroup φ.toPointHom.ker d).map (pointHom σ))).toAffine.Point)
    [Finite R] [IsAddCyclic R] (hR : Nat.card R = 2 ^ n) :
    (algorithm6First σ (degreeSubgroup φ.toPointHom.ker d) R c).degree = c := by
  have hO : Nat.card (degreeSubgroup φ.toPointHom.ker d) = d := degreeSubgroup_card _ d (by
    rw [Isogeny.card_ker_toPointHom_eq_degree, hφ]
    exact Nat.dvd_mul_left d (2 ^ n))
  apply algorithm6First_degree
  · rw [hO, hσ]
    exact hd.coprime_two_right.pow_right k
  · rw [hO, hR]
    exact hd.coprime_two_right.pow_right n
  · rw [hO, hR, ← hφ]
    exact hc

section HintInput
attribute [local instance] Isogeny.isSeparable_comp

set_option maxHeartbeats 1600000 in
/-- Algorithm 6 on a genuine Algorithm 5 input pair. For every pair of actual
cyclic separable isogenies of coprime degrees, and every permitted fresh cyclic
two-primary draw, geometric factorization constructs an output pair whose
first public degree equals the input first public degree. -/
theorem algorithm6_hint [IsAlgClosed K]
    {M U : Affine K} [M.IsElliptic] [U.IsElliptic]
    (first : Isogeny W M) (second : Isogeny M U)
    [Algebra.IsSeparable first.fieldPullback.fieldRange W.FunctionField]
    [Algebra.IsSeparable second.fieldPullback.fieldRange M.FunctionField]
    [IsAddCyclic first.toPointHom.ker] [IsAddCyclic second.toPointHom.ker]
    (hcop : first.degree.Coprime second.degree)
    (σ : Isogeny W V) (k n d : ℕ) (hσ : σ.degree = 2 ^ k) (hd : Odd d)
    (hφ : (second.comp first).degree = 2 ^ n * d)
    (R : AddSubgroup (quotientCurve V
      ((degreeSubgroup (second.comp first).toPointHom.ker d).map (pointHom σ))).toAffine.Point)
    [Finite R] [IsAddCyclic R] (hR : Nat.card R = 2 ^ n) :
    HasSplit (rebuiltIsogeny σ (degreeSubgroup (second.comp first).toPointHom.ker d) R)
      first.degree := by
  have : IsAddCyclic (second.comp first).toPointHom.ker :=
    cyclic_isogeny_comp second first hcop
  have hc : first.degree ∣ (second.comp first).degree := by
    rw [Isogeny.degree_comp]
    exact Nat.dvd_mul_left _ _
  exact (algorithm6_output (second.comp first) σ k n d first.degree hσ hd hφ hc R hR).1

end HintInput

/-- The two positive degrees printed in Algorithm 5 are automatically
coprime. The strict inequality excludes exactly the zero/invalid complementary
degree, which is handled separately by the endpoint convention. -/
theorem algorithm5_degrees_coprime (v r d : ℕ) (hd : Odd d) (hbound : d < 2 ^ r) :
    (2 ^ v * d).Coprime (2 ^ r - d) := by
  have hr : r ≠ 0 := by
    intro h
    have hdpos : 0 < d := hd.pos
    simp only [h, pow_zero] at hbound
    omega
  have heven : Even (2 ^ r) := (by decide : Even 2).pow_of_ne_zero hr
  have hodd : Odd (2 ^ r - d) := Nat.Even.sub_odd hbound.le heven hd
  apply Nat.Coprime.mul_left (hodd.coprime_two_right.symm.pow_left v)
  exact (Nat.coprime_sub_self_right hbound.le).mpr (hd.coprime_two_right.pow_right r)

/-- For every interior Algorithm 5 degree, the literal complementary degree
is positive and coprime to the first component. -/
theorem algorithm5_complement_positive_coprime (e n d : ℕ) (hd : Odd d)
    (hbound : 2 ^ n * d < 2 ^ e) :
    0 < 2 ^ (e - n) - d ∧ (2 ^ n * d).Coprime (2 ^ (e - n) - d) := by
  have hmul : 2 ^ n ≤ 2 ^ n * d := Nat.le_mul_of_pos_right _ hd.pos
  have hn : n ≤ e := by
    by_contra h
    have he : e ≤ n := by omega
    have hpow : 2 ^ e ≤ 2 ^ n := pow_le_pow_right' (by decide : 1 ≤ (2 : ℕ)) he
    omega
  have hp : 2 ^ e = 2 ^ n * 2 ^ (e - n) := by
    rw [← pow_add, Nat.add_sub_of_le hn]
  have hd' : d < 2 ^ (e - n) := by
    apply (Nat.mul_lt_mul_left (by positivity : 0 < 2 ^ n)).mp
    simpa only [← hp] using hbound
  exact ⟨Nat.sub_pos_of_lt hd', algorithm5_degrees_coprime n (e - n) d hd hd'⟩

/-- The part of Definition 2.11's public validator used by the adversary:
it rejects, or returns the binary degree. Domain/codomain and point-evaluation
outputs are irrelevant to this observation and may be carried separately. -/
structure DegreeDecoder where
  valid : List Bool → Option (List Bool)

/-- A valid public representation of a genuine isogeny, as far as its degree
output is concerned. This is a representation specification, not a probability
or distinguishing assumption. -/
def DegreeDecoder.Represents (E : DegreeDecoder) (D : List Bool)
    {W V : Affine K} (φ : Isogeny W V) : Prop :=
  (E.valid D).map BitComplexity.value = some φ.degree

omit [DecidableEq K] [W.IsElliptic] [V.IsElliptic] in
/-- The bit program observes the genuine geometric degree in every valid
representation, including randomized encodings satisfying the same validator. -/
theorem public_test_of_representation (E : DegreeDecoder) (D B s : List Bool)
    (φ : Isogeny W V) (hD : E.Represents D φ) (hs : 0 < BitComplexity.value s) :
    (BitComplexity.testBitsOption B s (E.valid D)).result =
      publicTest (BitComplexity.value B) (BitComplexity.value s) (some φ.degree) := by
  rw [BitComplexity.testBitsOption_correct B s _ hs, hD]

/-- Combining a geometric coprime push with the public decoder leaves the
degree-only attack exactly unchanged. -/
theorem pushed_public_test (σ : Isogeny W V) (S : AddSubgroup W.Point)
    [Finite S] (hcop : (Nat.card S).Coprime σ.degree)
    (E : DegreeDecoder) (D B s : List Bool) (hD : E.Represents D (pushedIsogeny σ S))
    (hs : 0 < BitComplexity.value s) :
    (BitComplexity.testBitsOption B s (E.valid D)).result =
      publicTest (BitComplexity.value B) (BitComplexity.value s) (some (Nat.card S)) := by
  rw [public_test_of_representation E D B s _ hD hs, pushedIsogeny_degree σ S hcop]

/-- Public bit-level observation of the concrete first output of Algorithm 6. -/
theorem algorithm6First_public_test [IsAlgClosed K] (σ : Isogeny W V)
    (O : AddSubgroup W.Point) [Finite O] [IsAddCyclic O]
    (R : AddSubgroup (quotientCurve V (O.map (pointHom σ))).toAffine.Point)
    [Finite R] [IsAddCyclic R] (c : ℕ)
    (hσ : (Nat.card O).Coprime σ.degree)
    (hR : (Nat.card O).Coprime (Nat.card R))
    (hc : c ∣ Nat.card R * Nat.card O)
    (E : DegreeDecoder) (D B s : List Bool)
    (hD : E.Represents D (algorithm6First σ O R c)) (hs : 0 < BitComplexity.value s) :
    (BitComplexity.testBitsOption B s (E.valid D)).result =
      publicTest (BitComplexity.value B) (BitComplexity.value s) (some c) := by
  rw [public_test_of_representation E D B s _ hD hs,
    algorithm6First_degree σ O R c hσ hR hc]

end IsogenyAttack.IsogenyPush
