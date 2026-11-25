module

import RKCert.ReviewedNative.P10AugmentedRender.Positive

namespace RKResearch.Certified.P10AugmentedRender

open RKResearch.Certified NativeIntegerSpanClearing NativeIntegerAugmentedChecker
  NativeIntegerAugmentedShardJoin NativeIntegerBlock4 P10AugmentedScaffold
  RationalStrictSDIRKTwentySevenStageTenUpper

example : Receipts renderOps header lower := literalReceipts

example : RKResearch.HasOrder 10 RationalStrictSDIRKTwentySevenStageTenUpper.A
    RationalStrictSDIRKTwentySevenStageTenUpper.b := checked_order_ten

end RKResearch.Certified.P10AugmentedRender

#print axioms RKResearch.Certified.P10AugmentedRender.literalReceipts
#print axioms RKResearch.Certified.P10AugmentedRender.checked_order_ten
