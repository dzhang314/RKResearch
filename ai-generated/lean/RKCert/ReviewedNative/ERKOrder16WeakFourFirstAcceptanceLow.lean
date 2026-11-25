module

public import RKCert.ReviewedNative.ERKOrder16WeakFourFirstAcceptanceLowClaims000
public import RKCert.ReviewedNative.ERKOrder16WeakFourFirstAcceptanceLowClaims001
public import RKCert.ReviewedNative.ERKOrder16WeakFourFirstAcceptanceLowClaims002
public import RKCert.ReviewedNative.ERKOrder16WeakFourFirstAcceptanceLowClaims003
public import RKCert.ReviewedNative.ERKOrder16WeakFourFirstAcceptanceLowClaims004
public import RKCert.ReviewedNative.ERKOrder16WeakFourFirstAcceptanceLowFrames000
public import RKCert.ReviewedNative.ERKOrder16WeakFourFirstAcceptanceLowFrames001
public import RKCert.ReviewedNative.ERKOrder16WeakFourFirstAcceptanceLowFrames002
public import RKCert.ReviewedNative.ERKOrder16WeakFourFirstAcceptanceLowFrames003
public import RKCert.ReviewedNative.ERKOrder16WeakFourFirstAcceptanceLowFrames004
public import RKCert.ReviewedNative.ERKOrder16WeakFourFirstAcceptanceLowFrames005
public import RKCert.ReviewedNative.ERKOrder16WeakFourFirstAcceptanceLowFrames006
public import RKCert.ReviewedNative.ERKOrder16WeakFourFirstAcceptanceLowFrames007
public import RKCert.ReviewedNative.ERKOrder16WeakFourFirstAcceptanceLowFrames008
public import RKCert.ReviewedNative.ERKOrder16WeakFourFirstAcceptanceLowFrames009
public import RKCert.ReviewedNative.ERKOrder16WeakFourFirstAcceptanceLowFrames010
public import RKCert.ReviewedNative.ERKOrder16WeakFourFirstAcceptanceLowFrames011
public import RKCert.ReviewedNative.ERKOrder16WeakFourFirstAcceptanceLowFrames012

@[expose] public section

namespace RKCert.ReviewedNative.WeakFourFirstOnly.Replay.Low
open RKCert.ReviewedNative.WeakFourFirstOnly.DataLow
open RKCert.ReviewedNative.PolynomialCertificate (checkChain)
set_option maxRecDepth 12000
set_option maxHeartbeats 4000000

private theorem geometryAc : [frame3,frame4,frame6,frame7,frame10,frame12,frame14,frame16,frame18,frame20,frame21,frame29,frame32,frame33,frame35,frame36,frame39,frame40,frame41,frame43,frame44,frame45,frame46,frame47,frame48].all stripTest=true := by
  simp only [List.all_cons,List.all_nil,stripOK000,stripOK001,stripOK002,stripOK003,stripOK004,stripOK005,stripOK006,stripOK007,stripOK008,stripOK009,stripOK010,stripOK011,stripOK012,stripOK013,stripOK014,stripOK015,stripOK016,stripOK017,stripOK018,stripOK019,stripOK020,stripOK021,stripOK022,stripOK023,stripOK024,Bool.and_self]

private theorem framesAc : [frame3,frame4,frame6,frame7,frame10,frame12,frame14,frame16,frame18,frame20,frame21,frame29,frame32,frame33,frame35,frame36,frame39,frame40,frame41,frame43,frame44,frame45,frame46,frame47,frame48].all (frameRankTest original useStop)=true := by
  simp only [List.all_cons,List.all_nil,frameOK000,frameOK001,frameOK002,frameOK003,frameOK004,frameOK005,frameOK006,frameOK007,frameOK008,frameOK009,frameOK010,frameOK011,frameOK012,frameOK013,frameOK014,frameOK015,frameOK016,frameOK017,frameOK018,frameOK019,frameOK020,frameOK021,frameOK022,frameOK023,frameOK024,Bool.and_self]

private theorem claimsAc : original.claims.all claimTest=true :=
  (appendAccepted (appendAccepted (appendAccepted (appendAccepted (appendAccepted (appendAccepted (appendAccepted (appendAccepted (appendAccepted (appendAccepted (appendAccepted (appendAccepted (appendAccepted claimOK000 claimOK001) claimOK002) claimOK003) claimOK004) claimOK005) claimOK006) claimOK007) claimOK008) claimOK009) claimOK010) claimOK011) claimOK012) claimOK013)

private theorem chainAc : checkChain original.den 0
    (original.terminal.map RationalStripFrame.span)=true :=
  (chainAppendAccepted spanOK000 (chainAppendAccepted spanOK001 (chainAppendAccepted spanOK002 (chainAppendAccepted spanOK003 (chainAppendAccepted spanOK004 (chainAppendAccepted spanOK005 (chainAppendAccepted spanOK006 (chainAppendAccepted spanOK007 (chainAppendAccepted spanOK008 (chainAppendAccepted spanOK009 (chainAppendAccepted spanOK010 (chainAppendAccepted spanOK011 (chainAppendAccepted spanOK012 (chainAppendAccepted spanOK013 (chainAppendAccepted spanOK014 (chainAppendAccepted spanOK015 (chainAppendAccepted spanOK016 (chainAppendAccepted spanOK017 (chainAppendAccepted spanOK018 (chainAppendAccepted spanOK019 (chainAppendAccepted spanOK020 (chainAppendAccepted spanOK021 (chainAppendAccepted spanOK022 (chainAppendAccepted spanOK023 spanOK024))))))))))))))))))))))))

theorem accepted : checkExteriorReceipts original referenceJList referenceP₀List false=true :=
  exteriorReceipts_of_checkpoints (by decide) (by decide)
    chainAc geometryAc claimsAc framesAc


end RKCert.ReviewedNative.WeakFourFirstOnly.Replay.Low
