import RKCert.Research.SDIRKSevenMultiplierZeroF19
import RKCert.Research.SDIRKSevenQuarticPoleScalar

open RKResearch.Certified.SDIRKSevenMultiplierZeroF19
open RKResearch.Certified.SDIRKSevenQuarticPoleScalar

#check Second.active_adjoint
#check Second.multiplier_site
#check Second.order_seven
#check Second.not_order_eight
#check Fourth.active_adjoint
#check Fourth.multiplier_site
#check Fourth.order_seven
#check Fourth.not_order_eight
#check centered_last_reflection_gate

#print axioms Second.active_adjoint
#print axioms Second.multiplier_site
#print axioms Second.order_seven
#print axioms Second.not_order_eight
#print axioms Fourth.active_adjoint
#print axioms Fourth.multiplier_site
#print axioms Fourth.order_seven
#print axioms Fourth.not_order_eight
#print axioms centered_last_reflection_gate
