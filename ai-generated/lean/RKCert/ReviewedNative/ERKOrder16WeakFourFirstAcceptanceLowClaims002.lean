module

public import RKCert.ReviewedNative.ERKOrder16WeakFourFirstRanksLow

@[expose] public section

namespace RKCert.ReviewedNative.WeakFourFirstOnly.Replay.Low
open RKCert.ReviewedNative.WeakFourFirstOnly.DataLow
open RKCert.ReviewedNative.PolynomialCertificate (checkChain)
set_option maxRecDepth 12000
set_option maxHeartbeats 4000000

private theorem claimOK006_s000 : ((claims006.drop 0).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK006_s002 : ((claims006.drop 2).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK006_s004 : ((claims006.drop 4).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK006_s006 : ((claims006.drop 6).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK006_s008 : ((claims006.drop 8).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK006_s010 : ((claims006.drop 10).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK006_s012 : ((claims006.drop 12).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK006_s014 : ((claims006.drop 14).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK006_s016 : ((claims006.drop 16).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK006_s018 : ((claims006.drop 18).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK006_s020 : ((claims006.drop 20).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK006_s022 : ((claims006.drop 22).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK006_end : (claims006.drop 24).all claimTest=true := by
  decide +kernel

theorem claimOK006 : claims006.all claimTest=true := by
  have h22 := stitchAt 22 2 claimOK006_s022 claimOK006_end
  have h20 := stitchAt 20 2 claimOK006_s020 h22
  have h18 := stitchAt 18 2 claimOK006_s018 h20
  have h16 := stitchAt 16 2 claimOK006_s016 h18
  have h14 := stitchAt 14 2 claimOK006_s014 h16
  have h12 := stitchAt 12 2 claimOK006_s012 h14
  have h10 := stitchAt 10 2 claimOK006_s010 h12
  have h8 := stitchAt 8 2 claimOK006_s008 h10
  have h6 := stitchAt 6 2 claimOK006_s006 h8
  have h4 := stitchAt 4 2 claimOK006_s004 h6
  have h2 := stitchAt 2 2 claimOK006_s002 h4
  have h0 := stitchAt 0 2 claimOK006_s000 h2
  simpa only [List.drop_zero] using h0

private theorem claimOK007_s000 : ((claims007.drop 0).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK007_s002 : ((claims007.drop 2).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK007_s004 : ((claims007.drop 4).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK007_s006 : ((claims007.drop 6).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK007_s008 : ((claims007.drop 8).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK007_s010 : ((claims007.drop 10).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK007_s012 : ((claims007.drop 12).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK007_s014 : ((claims007.drop 14).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK007_s016 : ((claims007.drop 16).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK007_s018 : ((claims007.drop 18).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK007_s020 : ((claims007.drop 20).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK007_s022 : ((claims007.drop 22).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK007_end : (claims007.drop 24).all claimTest=true := by
  decide +kernel

theorem claimOK007 : claims007.all claimTest=true := by
  have h22 := stitchAt 22 2 claimOK007_s022 claimOK007_end
  have h20 := stitchAt 20 2 claimOK007_s020 h22
  have h18 := stitchAt 18 2 claimOK007_s018 h20
  have h16 := stitchAt 16 2 claimOK007_s016 h18
  have h14 := stitchAt 14 2 claimOK007_s014 h16
  have h12 := stitchAt 12 2 claimOK007_s012 h14
  have h10 := stitchAt 10 2 claimOK007_s010 h12
  have h8 := stitchAt 8 2 claimOK007_s008 h10
  have h6 := stitchAt 6 2 claimOK007_s006 h8
  have h4 := stitchAt 4 2 claimOK007_s004 h6
  have h2 := stitchAt 2 2 claimOK007_s002 h4
  have h0 := stitchAt 0 2 claimOK007_s000 h2
  simpa only [List.drop_zero] using h0

private theorem claimOK008_s000 : ((claims008.drop 0).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK008_s002 : ((claims008.drop 2).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK008_s004 : ((claims008.drop 4).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK008_s006 : ((claims008.drop 6).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK008_s008 : ((claims008.drop 8).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK008_s010 : ((claims008.drop 10).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK008_s012 : ((claims008.drop 12).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK008_s014 : ((claims008.drop 14).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK008_s016 : ((claims008.drop 16).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK008_s018 : ((claims008.drop 18).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK008_s020 : ((claims008.drop 20).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK008_s022 : ((claims008.drop 22).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK008_end : (claims008.drop 24).all claimTest=true := by
  decide +kernel

theorem claimOK008 : claims008.all claimTest=true := by
  have h22 := stitchAt 22 2 claimOK008_s022 claimOK008_end
  have h20 := stitchAt 20 2 claimOK008_s020 h22
  have h18 := stitchAt 18 2 claimOK008_s018 h20
  have h16 := stitchAt 16 2 claimOK008_s016 h18
  have h14 := stitchAt 14 2 claimOK008_s014 h16
  have h12 := stitchAt 12 2 claimOK008_s012 h14
  have h10 := stitchAt 10 2 claimOK008_s010 h12
  have h8 := stitchAt 8 2 claimOK008_s008 h10
  have h6 := stitchAt 6 2 claimOK008_s006 h8
  have h4 := stitchAt 4 2 claimOK008_s004 h6
  have h2 := stitchAt 2 2 claimOK008_s002 h4
  have h0 := stitchAt 0 2 claimOK008_s000 h2
  simpa only [List.drop_zero] using h0


end RKCert.ReviewedNative.WeakFourFirstOnly.Replay.Low
