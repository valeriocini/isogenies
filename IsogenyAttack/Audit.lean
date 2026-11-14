import IsogenyAttack

/-! Reproducible kernel dependency audit of the delivered certificate. -/
#print axioms IsogenyAttack.HNF.strip_content
#print axioms IsogenyAttack.HNF.degree_eq_content_sq_mul_strip
#print axioms IsogenyAttack.HNF.scalar_unique
#print axioms IsogenyAttack.HNF.bounded_card_le
#print axioms IsogenyAttack.degree_card
#print axioms IsogenyAttack.liftIndex_card_twice
#print axioms IsogenyAttack.sigmaOne_le_printedWeight
#print axioms IsogenyAttack.printedWeightAF_eq_convolution
#print axioms IsogenyAttack.normalizedConvolutionWeight_sum_le_four
#print axioms IsogenyAttack.normalizer_le_four_mul_square
#print axioms IsogenyAttack.kernel_weight_sum
#print axioms IsogenyAttack.printedLaw
#print axioms IsogenyAttack.publicTest_spec
#print axioms IsogenyAttack.attack_correct
#print axioms IsogenyAttack.not_negligible_of_attack_bound
#print axioms IsogenyAttack.elliptic_torsion_rank_two
#print axioms IsogenyAttack.elliptic_kernel_count
#print axioms IsogenyAttack.elliptic_scalar_stripping
#print axioms IsogenyAttack.elliptic_kernel_code_spec
#print axioms IsogenyAttack.Legendre.hasseInvariantLaw_eq_reciprocal_aut
#print axioms IsogenyAttack.Legendre.hasLegendreHasseZero_iff_j_mem
#print axioms IsogenyAttack.GeometricMultiplicity.card_realization
#print axioms IsogenyAttack.GeometricMultiplicity.uniform_realization_family
#print axioms IsogenyAttack.ArithmeticAttack.finite_attack_certificate
#print axioms IsogenyAttack.ArithmeticAttack.family_attack_certificate
#print axioms IsogenyAttack.ArithmeticAttack.eventual_family_advantage_not_negligible
#print axioms IsogenyAttack.actualPrintedLaw_mass
#print axioms IsogenyAttack.actual_hasse_samplers_attack
#print axioms IsogenyAttack.Endpoint.odd_split_zero_complement_probability_pos
#print axioms IsogenyAttack.Legendre.isSupersingular_iff_j_mem_hasse
#print axioms IsogenyAttack.MontgomeryStationary.parameterLaw_j_mass
#print axioms IsogenyAttack.MontgomeryStationary.card_parameterLocus
#print axioms IsogenyAttack.card_frobeniusFixedField
#print axioms IsogenyAttack.supersingular_j_pow_square_eq
#print axioms IsogenyAttack.supersingular_j_mem_quadraticField
#print axioms IsogenyAttack.quotientIsogeny_degree
#print axioms IsogenyAttack.quotientIsogeny_point_kernel
#print axioms IsogenyAttack.quotientCurve_supersingular
#print axioms IsogenyAttack.quotientJClass
#print axioms IsogenyAttack.ScalarQuotient.exists_scalar_component_same_j
#print axioms IsogenyAttack.EndToEnd.full_attack_certificate
#print axioms IsogenyAttack.EndToEndFamilies.family_advantage_not_negligible
#print axioms IsogenyAttack.RationalAttack.signed_gap_lower
#print axioms IsogenyAttack.RationalAttack.public_finite_attack
#print axioms IsogenyAttack.SourceEndpoint.signed_gap_lower
#print axioms IsogenyAttack.Montgomery.isogeny_descends
#print axioms IsogenyAttack.PushedEncoding.sourceDegreeChannel
#print axioms IsogenyAttack.TranscriptEncoding.acceptance_eq

-- Exact statement, including the visible geometric/model interface.
#check IsogenyAttack.attack_correct
#check IsogenyAttack.ArithmeticAttack.finite_attack_certificate
#check IsogenyAttack.ArithmeticAttack.family_attack_certificate
#check IsogenyAttack.elliptic_scalar_stripping
#check IsogenyAttack.actual_hasse_samplers_attack
#check IsogenyAttack.EndToEnd.full_attack_certificate
#check IsogenyAttack.EndToEndFamilies.family_advantage_not_negligible
#check IsogenyAttack.RationalAttack.public_finite_attack

-- Boundary examples of the actual executable test; proved by kernel-checked
-- arithmetic normalization, not an external evaluator.
example : IsogenyAttack.publicTest (2^126) 1024 (some (2^104)) = true := by
  norm_num [IsogenyAttack.publicTest, IsogenyAttack.threshold]
example : IsogenyAttack.publicTest (2^126) 1024 (some (2^104+1)) = false := by
  norm_num [IsogenyAttack.publicTest, IsogenyAttack.threshold]
example : IsogenyAttack.publicTest (2^126) 1024 none = false := rfl
