module

public import RKCert.ReviewedNative.ERKOrder16WeakFourFirstRanksHigh

@[expose] public section

namespace RKCert.ReviewedNative.WeakFourFirstOnly.Replay.High
open RKCert.ReviewedNative.WeakFourFirstOnly.DataHigh
open RKCert.ReviewedNative.PolynomialCertificate (checkChain)
set_option maxRecDepth 12000
set_option maxHeartbeats 4000000

private theorem claimOK027_s000 : ((claims027.drop 0).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK027_s002 : ((claims027.drop 2).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK027_s004 : ((claims027.drop 4).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK027_s006 : ((claims027.drop 6).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK027_s008 : ((claims027.drop 8).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK027_s010 : ((claims027.drop 10).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK027_s012 : ((claims027.drop 12).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK027_s014 : ((claims027.drop 14).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK027_s016 : ((claims027.drop 16).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK027_s018 : ((claims027.drop 18).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK027_s020 : ((claims027.drop 20).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK027_s022 : ((claims027.drop 22).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK027_end : (claims027.drop 24).all claimTest=true := by
  decide +kernel

theorem claimOK027 : claims027.all claimTest=true := by
  have h22 := stitchAt 22 2 claimOK027_s022 claimOK027_end
  have h20 := stitchAt 20 2 claimOK027_s020 h22
  have h18 := stitchAt 18 2 claimOK027_s018 h20
  have h16 := stitchAt 16 2 claimOK027_s016 h18
  have h14 := stitchAt 14 2 claimOK027_s014 h16
  have h12 := stitchAt 12 2 claimOK027_s012 h14
  have h10 := stitchAt 10 2 claimOK027_s010 h12
  have h8 := stitchAt 8 2 claimOK027_s008 h10
  have h6 := stitchAt 6 2 claimOK027_s006 h8
  have h4 := stitchAt 4 2 claimOK027_s004 h6
  have h2 := stitchAt 2 2 claimOK027_s002 h4
  have h0 := stitchAt 0 2 claimOK027_s000 h2
  simpa only [List.drop_zero] using h0

private theorem claimOK028_s000 : ((claims028.drop 0).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK028_s002 : ((claims028.drop 2).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK028_s004 : ((claims028.drop 4).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK028_s006 : ((claims028.drop 6).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK028_s008 : ((claims028.drop 8).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK028_s010 : ((claims028.drop 10).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK028_s012 : ((claims028.drop 12).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK028_s014 : ((claims028.drop 14).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK028_s016 : ((claims028.drop 16).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK028_s018 : ((claims028.drop 18).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK028_s020 : ((claims028.drop 20).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK028_s022 : ((claims028.drop 22).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK028_end : (claims028.drop 24).all claimTest=true := by
  decide +kernel

theorem claimOK028 : claims028.all claimTest=true := by
  have h22 := stitchAt 22 2 claimOK028_s022 claimOK028_end
  have h20 := stitchAt 20 2 claimOK028_s020 h22
  have h18 := stitchAt 18 2 claimOK028_s018 h20
  have h16 := stitchAt 16 2 claimOK028_s016 h18
  have h14 := stitchAt 14 2 claimOK028_s014 h16
  have h12 := stitchAt 12 2 claimOK028_s012 h14
  have h10 := stitchAt 10 2 claimOK028_s010 h12
  have h8 := stitchAt 8 2 claimOK028_s008 h10
  have h6 := stitchAt 6 2 claimOK028_s006 h8
  have h4 := stitchAt 4 2 claimOK028_s004 h6
  have h2 := stitchAt 2 2 claimOK028_s002 h4
  have h0 := stitchAt 0 2 claimOK028_s000 h2
  simpa only [List.drop_zero] using h0

private theorem claimOK029_s000 : ((claims029.drop 0).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK029_s002 : ((claims029.drop 2).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK029_s004 : ((claims029.drop 4).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK029_s006 : ((claims029.drop 6).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK029_s008 : ((claims029.drop 8).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK029_s010 : ((claims029.drop 10).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK029_s012 : ((claims029.drop 12).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK029_s014 : ((claims029.drop 14).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK029_s016 : ((claims029.drop 16).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK029_s018 : ((claims029.drop 18).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK029_s020 : ((claims029.drop 20).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK029_s022 : ((claims029.drop 22).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK029_end : (claims029.drop 24).all claimTest=true := by
  decide +kernel

theorem claimOK029 : claims029.all claimTest=true := by
  have h22 := stitchAt 22 2 claimOK029_s022 claimOK029_end
  have h20 := stitchAt 20 2 claimOK029_s020 h22
  have h18 := stitchAt 18 2 claimOK029_s018 h20
  have h16 := stitchAt 16 2 claimOK029_s016 h18
  have h14 := stitchAt 14 2 claimOK029_s014 h16
  have h12 := stitchAt 12 2 claimOK029_s012 h14
  have h10 := stitchAt 10 2 claimOK029_s010 h12
  have h8 := stitchAt 8 2 claimOK029_s008 h10
  have h6 := stitchAt 6 2 claimOK029_s006 h8
  have h4 := stitchAt 4 2 claimOK029_s004 h6
  have h2 := stitchAt 2 2 claimOK029_s002 h4
  have h0 := stitchAt 0 2 claimOK029_s000 h2
  simpa only [List.drop_zero] using h0


end RKCert.ReviewedNative.WeakFourFirstOnly.Replay.High
