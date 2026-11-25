module

public import RKCert.ReviewedNative.ERKOrder16WeakFourFirstRanksHigh

@[expose] public section

namespace RKCert.ReviewedNative.WeakFourFirstOnly.Replay.High
open RKCert.ReviewedNative.WeakFourFirstOnly.DataHigh
open RKCert.ReviewedNative.PolynomialCertificate (checkChain)
set_option maxRecDepth 12000
set_option maxHeartbeats 4000000

private theorem claimOK024_s000 : ((claims024.drop 0).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK024_s002 : ((claims024.drop 2).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK024_s004 : ((claims024.drop 4).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK024_s006 : ((claims024.drop 6).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK024_s008 : ((claims024.drop 8).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK024_s010 : ((claims024.drop 10).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK024_s012 : ((claims024.drop 12).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK024_s014 : ((claims024.drop 14).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK024_s016 : ((claims024.drop 16).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK024_s018 : ((claims024.drop 18).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK024_s020 : ((claims024.drop 20).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK024_s022 : ((claims024.drop 22).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK024_end : (claims024.drop 24).all claimTest=true := by
  decide +kernel

theorem claimOK024 : claims024.all claimTest=true := by
  have h22 := stitchAt 22 2 claimOK024_s022 claimOK024_end
  have h20 := stitchAt 20 2 claimOK024_s020 h22
  have h18 := stitchAt 18 2 claimOK024_s018 h20
  have h16 := stitchAt 16 2 claimOK024_s016 h18
  have h14 := stitchAt 14 2 claimOK024_s014 h16
  have h12 := stitchAt 12 2 claimOK024_s012 h14
  have h10 := stitchAt 10 2 claimOK024_s010 h12
  have h8 := stitchAt 8 2 claimOK024_s008 h10
  have h6 := stitchAt 6 2 claimOK024_s006 h8
  have h4 := stitchAt 4 2 claimOK024_s004 h6
  have h2 := stitchAt 2 2 claimOK024_s002 h4
  have h0 := stitchAt 0 2 claimOK024_s000 h2
  simpa only [List.drop_zero] using h0

private theorem claimOK025_s000 : ((claims025.drop 0).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK025_s002 : ((claims025.drop 2).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK025_s004 : ((claims025.drop 4).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK025_s006 : ((claims025.drop 6).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK025_s008 : ((claims025.drop 8).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK025_s010 : ((claims025.drop 10).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK025_s012 : ((claims025.drop 12).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK025_s014 : ((claims025.drop 14).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK025_s016 : ((claims025.drop 16).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK025_s018 : ((claims025.drop 18).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK025_s020 : ((claims025.drop 20).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK025_s022 : ((claims025.drop 22).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK025_end : (claims025.drop 24).all claimTest=true := by
  decide +kernel

theorem claimOK025 : claims025.all claimTest=true := by
  have h22 := stitchAt 22 2 claimOK025_s022 claimOK025_end
  have h20 := stitchAt 20 2 claimOK025_s020 h22
  have h18 := stitchAt 18 2 claimOK025_s018 h20
  have h16 := stitchAt 16 2 claimOK025_s016 h18
  have h14 := stitchAt 14 2 claimOK025_s014 h16
  have h12 := stitchAt 12 2 claimOK025_s012 h14
  have h10 := stitchAt 10 2 claimOK025_s010 h12
  have h8 := stitchAt 8 2 claimOK025_s008 h10
  have h6 := stitchAt 6 2 claimOK025_s006 h8
  have h4 := stitchAt 4 2 claimOK025_s004 h6
  have h2 := stitchAt 2 2 claimOK025_s002 h4
  have h0 := stitchAt 0 2 claimOK025_s000 h2
  simpa only [List.drop_zero] using h0

private theorem claimOK026_s000 : ((claims026.drop 0).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK026_s002 : ((claims026.drop 2).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK026_s004 : ((claims026.drop 4).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK026_s006 : ((claims026.drop 6).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK026_s008 : ((claims026.drop 8).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK026_s010 : ((claims026.drop 10).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK026_s012 : ((claims026.drop 12).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK026_s014 : ((claims026.drop 14).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK026_s016 : ((claims026.drop 16).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK026_s018 : ((claims026.drop 18).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK026_s020 : ((claims026.drop 20).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK026_s022 : ((claims026.drop 22).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK026_end : (claims026.drop 24).all claimTest=true := by
  decide +kernel

theorem claimOK026 : claims026.all claimTest=true := by
  have h22 := stitchAt 22 2 claimOK026_s022 claimOK026_end
  have h20 := stitchAt 20 2 claimOK026_s020 h22
  have h18 := stitchAt 18 2 claimOK026_s018 h20
  have h16 := stitchAt 16 2 claimOK026_s016 h18
  have h14 := stitchAt 14 2 claimOK026_s014 h16
  have h12 := stitchAt 12 2 claimOK026_s012 h14
  have h10 := stitchAt 10 2 claimOK026_s010 h12
  have h8 := stitchAt 8 2 claimOK026_s008 h10
  have h6 := stitchAt 6 2 claimOK026_s006 h8
  have h4 := stitchAt 4 2 claimOK026_s004 h6
  have h2 := stitchAt 2 2 claimOK026_s002 h4
  have h0 := stitchAt 0 2 claimOK026_s000 h2
  simpa only [List.drop_zero] using h0


end RKCert.ReviewedNative.WeakFourFirstOnly.Replay.High
