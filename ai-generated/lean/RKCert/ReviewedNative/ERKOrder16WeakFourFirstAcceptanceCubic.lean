module

public import RKCert.ReviewedNative.ERKOrder16WeakFourFirstAcceptanceCubicClaims000
public import RKCert.ReviewedNative.ERKOrder16WeakFourFirstAcceptanceCubicClaims001
public import RKCert.ReviewedNative.ERKOrder16WeakFourFirstAcceptanceCubicFrames000

@[expose] public section

namespace RKCert.ReviewedNative.WeakFourFirstOnly.Replay.Cubic
open RKCert.ReviewedNative.WeakFourFirstOnly.DataCubic
open RKCert.ReviewedNative.PolynomialCertificate (checkChain)
set_option maxRecDepth 12000
set_option maxHeartbeats 4000000

private theorem geometryAc : [frame0].all stripTest=true := by
  simp only [List.all_cons,List.all_nil,stripOK000,Bool.and_self]

private theorem framesAc : [frame0].all (frameRankTest original useStop)=true := by
  simp only [List.all_cons,List.all_nil,frameOK000,Bool.and_self]

private theorem claimsAc : original.claims.all claimTest=true :=
  (appendAccepted (appendAccepted (appendAccepted (appendAccepted (appendAccepted claimOK000 claimOK001) claimOK002) claimOK003) claimOK004) claimOK005)

private theorem chainAc : checkChain original.den 0
    (original.terminal.map RationalStripFrame.span)=true :=
  spanOK000

theorem accepted : checkOrdinaryReceipts original referenceJList referenceJList=true :=
  ordinaryReceipts_of_checkpoints (by decide)
    chainAc geometryAc claimsAc framesAc


end RKCert.ReviewedNative.WeakFourFirstOnly.Replay.Cubic
