module

public import RKCert.ReviewedNative.P10AugmentedScaffold.Assembly
public import RKCert.ReviewedNative.RationalStrictSDIRKTwentySevenStageTenData

@[expose] public section

namespace RKResearch.Certified.P10AugmentedScaffold

open NativeIntegerSpanClearing NativeIntegerAugmentedChecker NativeIntegerAugmentedTopPay
open RationalStrictSDIRKTwentySevenStageTenUpper

def actualOps : Ops := ⟨actInt, outInt, stageScale, weightScale⟩

/-- Explicitly conditional until genuine literal-window receipts are supplied. -/
theorem positive_of_shards (H : Header) (L : LowerPayload)
    (R : Receipts actualOps H L) : RKResearch.HasOrder 10 A b := by
  have hA : ratMatrix AInt = (stageScale : ℚ) • A := cast_AInt
  have hb : ratVec bInt = (weightScale : ℚ) • b := cast_bInt
  have hc : checkDirectTop actInt outInt stageScale weightScale 10 (candidate H L) = true :=
    assembled_check actualOps H L R
  exact hasOrder_of_direct_top_check AInt bInt actInt outInt actInt_eq outInt_eq
    stageScale weightScale 10 (candidate H L) hA hb hc

end RKResearch.Certified.P10AugmentedScaffold
