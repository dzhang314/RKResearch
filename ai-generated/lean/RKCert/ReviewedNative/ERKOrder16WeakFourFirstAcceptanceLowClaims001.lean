module

public import RKCert.ReviewedNative.ERKOrder16WeakFourFirstRanksLow

@[expose] public section

namespace RKCert.ReviewedNative.WeakFourFirstOnly.Replay.Low
open RKCert.ReviewedNative.WeakFourFirstOnly.DataLow
open RKCert.ReviewedNative.PolynomialCertificate (checkChain)
set_option maxRecDepth 12000
set_option maxHeartbeats 4000000

private theorem claimOK003_s000 : ((claims003.drop 0).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK003_s002 : ((claims003.drop 2).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK003_s004 : ((claims003.drop 4).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK003_s006 : ((claims003.drop 6).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK003_s008 : ((claims003.drop 8).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK003_s010 : ((claims003.drop 10).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK003_s012 : ((claims003.drop 12).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK003_s014 : ((claims003.drop 14).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK003_s016 : ((claims003.drop 16).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK003_s018 : ((claims003.drop 18).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK003_s020 : ((claims003.drop 20).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK003_s022 : ((claims003.drop 22).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK003_end : (claims003.drop 24).all claimTest=true := by
  decide +kernel

theorem claimOK003 : claims003.all claimTest=true := by
  have h22 := stitchAt 22 2 claimOK003_s022 claimOK003_end
  have h20 := stitchAt 20 2 claimOK003_s020 h22
  have h18 := stitchAt 18 2 claimOK003_s018 h20
  have h16 := stitchAt 16 2 claimOK003_s016 h18
  have h14 := stitchAt 14 2 claimOK003_s014 h16
  have h12 := stitchAt 12 2 claimOK003_s012 h14
  have h10 := stitchAt 10 2 claimOK003_s010 h12
  have h8 := stitchAt 8 2 claimOK003_s008 h10
  have h6 := stitchAt 6 2 claimOK003_s006 h8
  have h4 := stitchAt 4 2 claimOK003_s004 h6
  have h2 := stitchAt 2 2 claimOK003_s002 h4
  have h0 := stitchAt 0 2 claimOK003_s000 h2
  simpa only [List.drop_zero] using h0

private theorem claimOK004_s000 : ((claims004.drop 0).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK004_s002 : ((claims004.drop 2).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK004_s004 : ((claims004.drop 4).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK004_s006 : ((claims004.drop 6).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK004_s008 : ((claims004.drop 8).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK004_s010 : ((claims004.drop 10).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK004_s012 : ((claims004.drop 12).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK004_s014 : ((claims004.drop 14).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK004_s016 : ((claims004.drop 16).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK004_s018 : ((claims004.drop 18).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK004_s020 : ((claims004.drop 20).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK004_s022 : ((claims004.drop 22).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK004_end : (claims004.drop 24).all claimTest=true := by
  decide +kernel

theorem claimOK004 : claims004.all claimTest=true := by
  have h22 := stitchAt 22 2 claimOK004_s022 claimOK004_end
  have h20 := stitchAt 20 2 claimOK004_s020 h22
  have h18 := stitchAt 18 2 claimOK004_s018 h20
  have h16 := stitchAt 16 2 claimOK004_s016 h18
  have h14 := stitchAt 14 2 claimOK004_s014 h16
  have h12 := stitchAt 12 2 claimOK004_s012 h14
  have h10 := stitchAt 10 2 claimOK004_s010 h12
  have h8 := stitchAt 8 2 claimOK004_s008 h10
  have h6 := stitchAt 6 2 claimOK004_s006 h8
  have h4 := stitchAt 4 2 claimOK004_s004 h6
  have h2 := stitchAt 2 2 claimOK004_s002 h4
  have h0 := stitchAt 0 2 claimOK004_s000 h2
  simpa only [List.drop_zero] using h0

private theorem claimOK005_s000 : ((claims005.drop 0).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK005_s002 : ((claims005.drop 2).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK005_s004 : ((claims005.drop 4).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK005_s006 : ((claims005.drop 6).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK005_s008 : ((claims005.drop 8).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK005_s010 : ((claims005.drop 10).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK005_s012 : ((claims005.drop 12).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK005_s014 : ((claims005.drop 14).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK005_s016 : ((claims005.drop 16).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK005_s018 : ((claims005.drop 18).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK005_s020 : ((claims005.drop 20).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK005_s022 : ((claims005.drop 22).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK005_end : (claims005.drop 24).all claimTest=true := by
  decide +kernel

theorem claimOK005 : claims005.all claimTest=true := by
  have h22 := stitchAt 22 2 claimOK005_s022 claimOK005_end
  have h20 := stitchAt 20 2 claimOK005_s020 h22
  have h18 := stitchAt 18 2 claimOK005_s018 h20
  have h16 := stitchAt 16 2 claimOK005_s016 h18
  have h14 := stitchAt 14 2 claimOK005_s014 h16
  have h12 := stitchAt 12 2 claimOK005_s012 h14
  have h10 := stitchAt 10 2 claimOK005_s010 h12
  have h8 := stitchAt 8 2 claimOK005_s008 h10
  have h6 := stitchAt 6 2 claimOK005_s006 h8
  have h4 := stitchAt 4 2 claimOK005_s004 h6
  have h2 := stitchAt 2 2 claimOK005_s002 h4
  have h0 := stitchAt 0 2 claimOK005_s000 h2
  simpa only [List.drop_zero] using h0


end RKCert.ReviewedNative.WeakFourFirstOnly.Replay.Low
