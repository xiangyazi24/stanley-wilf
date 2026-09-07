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
