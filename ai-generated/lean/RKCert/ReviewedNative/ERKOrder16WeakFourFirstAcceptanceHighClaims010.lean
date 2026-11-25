module

public import RKCert.ReviewedNative.ERKOrder16WeakFourFirstRanksHigh

@[expose] public section

namespace RKCert.ReviewedNative.WeakFourFirstOnly.Replay.High
open RKCert.ReviewedNative.WeakFourFirstOnly.DataHigh
open RKCert.ReviewedNative.PolynomialCertificate (checkChain)
set_option maxRecDepth 12000
set_option maxHeartbeats 4000000

private theorem claimOK030_s000 : ((claims030.drop 0).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK030_s002 : ((claims030.drop 2).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK030_s004 : ((claims030.drop 4).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK030_s006 : ((claims030.drop 6).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK030_s008 : ((claims030.drop 8).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK030_s010 : ((claims030.drop 10).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK030_s012 : ((claims030.drop 12).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK030_s014 : ((claims030.drop 14).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK030_s016 : ((claims030.drop 16).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK030_s018 : ((claims030.drop 18).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK030_s020 : ((claims030.drop 20).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK030_s022 : ((claims030.drop 22).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK030_end : (claims030.drop 24).all claimTest=true := by
  decide +kernel

theorem claimOK030 : claims030.all claimTest=true := by
  have h22 := stitchAt 22 2 claimOK030_s022 claimOK030_end
  have h20 := stitchAt 20 2 claimOK030_s020 h22
  have h18 := stitchAt 18 2 claimOK030_s018 h20
  have h16 := stitchAt 16 2 claimOK030_s016 h18
  have h14 := stitchAt 14 2 claimOK030_s014 h16
  have h12 := stitchAt 12 2 claimOK030_s012 h14
  have h10 := stitchAt 10 2 claimOK030_s010 h12
  have h8 := stitchAt 8 2 claimOK030_s008 h10
  have h6 := stitchAt 6 2 claimOK030_s006 h8
  have h4 := stitchAt 4 2 claimOK030_s004 h6
  have h2 := stitchAt 2 2 claimOK030_s002 h4
  have h0 := stitchAt 0 2 claimOK030_s000 h2
  simpa only [List.drop_zero] using h0

private theorem claimOK031_s000 : ((claims031.drop 0).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK031_s002 : ((claims031.drop 2).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK031_s004 : ((claims031.drop 4).take 1).all claimTest=true := by
  decide +kernel

private theorem claimOK031_end : (claims031.drop 5).all claimTest=true := by
  decide +kernel

theorem claimOK031 : claims031.all claimTest=true := by
  have h4 := stitchAt 4 1 claimOK031_s004 claimOK031_end
  have h2 := stitchAt 2 2 claimOK031_s002 h4
  have h0 := stitchAt 0 2 claimOK031_s000 h2
  simpa only [List.drop_zero] using h0


end RKCert.ReviewedNative.WeakFourFirstOnly.Replay.High
