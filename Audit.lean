import StanleyWilf

/-! Execute with `lake env lean Audit.lean` after a successful build.
The checked-in presence of these commands is not a claim they were executed. -/

#print axioms StanleyWilf.contains_trans
#print axioms StanleyWilf.size_le_of_contains
#print axioms StanleyWilf.sumIndecomposable_or_skewIndecomposable
#print axioms StanleyWilf.directSum_injective
#print axioms StanleyWilf.skewSum_injective
#print axioms StanleyWilf.WeightedSequence.append_injective
#print axioms StanleyWilf.SequenceSpecification.ogf_mul_one_sub
#print axioms StanleyWilf.GradedProduct.counts_supermultiplicative
#print axioms StanleyWilf.pow_div_le
#print axioms StanleyWilf.exists_growthRate
#print axioms StanleyWilf.growthTarget_of_product

#print axioms StanleyWilf.positions_split
#print axioms StanleyWilf.contains_directSum_cases
#print axioms StanleyWilf.contains_skewSum_cases
#print axioms StanleyWilf.avoids_directSum
#print axioms StanleyWilf.avoids_skewSum
#print axioms StanleyWilf.avoidanceProduct
#print axioms StanleyWilf.avoiderCount_supermultiplicative
#print axioms StanleyWilf.contains_of_length_le_one
#print axioms StanleyWilf.growthTarget_of_length_le_one
#print axioms StanleyWilf.stanleyWilf_of_marcusTardos

-- Third-pass symbolic route: all of these queries still require a real Lean run.
#print axioms StanleyWilf.IsSumCut.to_boundary
#print axioms StanleyWilf.SumBoundary.value_lt_iff
#print axioms StanleyWilf.IsFirstSumBoundary.unique
#print axioms StanleyWilf.reconstruct_prefix_suffix
#print axioms StanleyWilf.prefixPerm_indecomposable_of_first
#print axioms StanleyWilf.directFirstJoin_injective
#print axioms StanleyWilf.directFirstJoin_surjective
#print axioms StanleyWilf.directFirstEquiv
#print axioms StanleyWilf.FirstComponentSpecification.counts_eq_seq
#print axioms StanleyWilf.FirstComponentSpecification.counts_supermultiplicative
#print axioms StanleyWilf.contains_complement_iff
#print axioms StanleyWilf.complement_directSum
#print axioms StanleyWilf.skewFirstEquiv
#print axioms StanleyWilf.avoidanceSequenceSpecification
#print axioms StanleyWilf.avoidance_ogf_mul_one_sub
#print axioms StanleyWilf.avoiderCount_supermultiplicative_symbolic
#print axioms StanleyWilf.stanleyWilf_symbolic
#print axioms StanleyWilf.stanleyWilf_symbolic_of_marcusTardos
#print axioms StanleyWilf.stanleyWilf

-- Marcus--Tardos extremal and Klazar enumeration chain.
#print axioms StanleyWilf.ForbiddenMatrix.ex_permPattern_le
#print axioms StanleyWilf.MarcusTardos.contains_iff_permutationMatrix_contains
#print axioms StanleyWilf.MarcusTardos.weight_le_marcusTardos
#print axioms StanleyWilf.MarcusTardos.contractionCodeOfAvoider_injective
#print axioms StanleyWilf.MarcusTardos.avoidingMatrixCount_two_mul_le
#print axioms StanleyWilf.MarcusTardos.avoidingMatrixCount_mono
#print axioms StanleyWilf.MarcusTardos.count_le_uniform_exponential_of_doubling
#print axioms StanleyWilf.MarcusTardos.marcusTardosBound
