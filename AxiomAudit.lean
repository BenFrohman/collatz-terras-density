-- Axiom audit: prints the axioms of every theorem/lemma in the project.
-- CI fails unless each depends only on propext, Classical.choice, Quot.sound (or none).
import TerrasDensity
import TerrasDensity.Basic
import TerrasDensity.Covering
import TerrasDensity.Density
import TerrasDensity.Inclusion
import TerrasDensity.Tail

#print axioms TerrasDensity.not_neverDrops_iff
#print axioms TerrasDensity.covering_from_assumption
#print axioms TerrasDensity.density_from_assumption
#print axioms TerrasDensity.density_of_covering
#print axioms TerrasDensity.drop_of_affine
#print axioms TerrasDensity.inclusion_of_affine
#print axioms TerrasDensity.terras_inclusion
#print axioms TerrasDensity.tail_le
#print axioms TerrasDensity.two_pow_le_three_pow
