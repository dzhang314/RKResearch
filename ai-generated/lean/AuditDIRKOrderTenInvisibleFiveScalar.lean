import RKCert.ReviewedNative.DIRKOrderTenInvisibleFiveScalar

open RKResearch.Certified.Graded.InvisibleFiveScalar

#check roots227
#check roots59
#check forward227
#check forward59
#check reverse59
#print axioms roots227
#print axioms roots59
#print axioms forward227
#print axioms forward59
#print axioms reverse59

example : reverseAll 59 = true := reverse59

example : anchorAll 227 = true ∧ noLeakZero 227 = true ∧
    ((withEnd 227).all fun a => (withEnd 227).all fun b =>
      if a=b then true else firstInterior 227 a b != 0) = true := forward227
