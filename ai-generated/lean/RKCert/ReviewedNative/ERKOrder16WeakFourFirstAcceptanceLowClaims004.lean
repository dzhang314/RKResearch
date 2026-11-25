module

public import RKCert.ReviewedNative.ERKOrder16WeakFourFirstRanksLow

@[expose] public section

namespace RKCert.ReviewedNative.WeakFourFirstOnly.Replay.Low
open RKCert.ReviewedNative.WeakFourFirstOnly.DataLow
open RKCert.ReviewedNative.PolynomialCertificate (checkChain)
set_option maxRecDepth 12000
set_option maxHeartbeats 4000000

private theorem claimOK012_s000 : ((claims012.drop 0).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK012_s002 : ((claims012.drop 2).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK012_s004 : ((claims012.drop 4).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK012_s006 : ((claims012.drop 6).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK012_s008 : ((claims012.drop 8).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK012_s010 : ((claims012.drop 10).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK012_s012 : ((claims012.drop 12).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK012_s014 : ((claims012.drop 14).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK012_s016 : ((claims012.drop 16).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK012_s018 : ((claims012.drop 18).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK012_s020 : ((claims012.drop 20).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK012_s022 : ((claims012.drop 22).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK012_end : (claims012.drop 24).all claimTest=true := by
  decide +kernel

theorem claimOK012 : claims012.all claimTest=true := by
  have h22 := stitchAt 22 2 claimOK012_s022 claimOK012_end
  have h20 := stitchAt 20 2 claimOK012_s020 h22
  have h18 := stitchAt 18 2 claimOK012_s018 h20
  have h16 := stitchAt 16 2 claimOK012_s016 h18
  have h14 := stitchAt 14 2 claimOK012_s014 h16
  have h12 := stitchAt 12 2 claimOK012_s012 h14
  have h10 := stitchAt 10 2 claimOK012_s010 h12
  have h8 := stitchAt 8 2 claimOK012_s008 h10
  have h6 := stitchAt 6 2 claimOK012_s006 h8
  have h4 := stitchAt 4 2 claimOK012_s004 h6
  have h2 := stitchAt 2 2 claimOK012_s002 h4
  have h0 := stitchAt 0 2 claimOK012_s000 h2
  simpa only [List.drop_zero] using h0

private theorem claimOK013_s000 : ((claims013.drop 0).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK013_s002 : ((claims013.drop 2).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK013_s004 : ((claims013.drop 4).take 1).all claimTest=true := by
  decide +kernel

private theorem claimOK013_end : (claims013.drop 5).all claimTest=true := by
  decide +kernel

theorem claimOK013 : claims013.all claimTest=true := by
  have h4 := stitchAt 4 1 claimOK013_s004 claimOK013_end
  have h2 := stitchAt 2 2 claimOK013_s002 h4
  have h0 := stitchAt 0 2 claimOK013_s000 h2
  simpa only [List.drop_zero] using h0


end RKCert.ReviewedNative.WeakFourFirstOnly.Replay.Low
