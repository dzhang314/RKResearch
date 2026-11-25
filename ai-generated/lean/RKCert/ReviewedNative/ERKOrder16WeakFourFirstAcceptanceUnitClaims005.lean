module

public import RKCert.ReviewedNative.ERKOrder16WeakFourFirstRanksUnit

@[expose] public section

namespace RKCert.ReviewedNative.WeakFourFirstOnly.Replay.Unit
open RKCert.ReviewedNative.WeakFourFirstOnly.DataUnit
open RKCert.ReviewedNative.PolynomialCertificate (checkChain)
set_option maxRecDepth 12000
set_option maxHeartbeats 4000000

private theorem claimOK015_s000 : ((claims015.drop 0).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK015_s002 : ((claims015.drop 2).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK015_s004 : ((claims015.drop 4).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK015_s006 : ((claims015.drop 6).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK015_s008 : ((claims015.drop 8).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK015_s010 : ((claims015.drop 10).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK015_s012 : ((claims015.drop 12).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK015_s014 : ((claims015.drop 14).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK015_s016 : ((claims015.drop 16).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK015_s018 : ((claims015.drop 18).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK015_s020 : ((claims015.drop 20).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK015_s022 : ((claims015.drop 22).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK015_end : (claims015.drop 24).all claimTest=true := by
  decide +kernel

theorem claimOK015 : claims015.all claimTest=true := by
  have h22 := stitchAt 22 2 claimOK015_s022 claimOK015_end
  have h20 := stitchAt 20 2 claimOK015_s020 h22
  have h18 := stitchAt 18 2 claimOK015_s018 h20
  have h16 := stitchAt 16 2 claimOK015_s016 h18
  have h14 := stitchAt 14 2 claimOK015_s014 h16
  have h12 := stitchAt 12 2 claimOK015_s012 h14
  have h10 := stitchAt 10 2 claimOK015_s010 h12
  have h8 := stitchAt 8 2 claimOK015_s008 h10
  have h6 := stitchAt 6 2 claimOK015_s006 h8
  have h4 := stitchAt 4 2 claimOK015_s004 h6
  have h2 := stitchAt 2 2 claimOK015_s002 h4
  have h0 := stitchAt 0 2 claimOK015_s000 h2
  simpa only [List.drop_zero] using h0

private theorem claimOK016_s000 : ((claims016.drop 0).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK016_s002 : ((claims016.drop 2).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK016_s004 : ((claims016.drop 4).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK016_s006 : ((claims016.drop 6).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK016_s008 : ((claims016.drop 8).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK016_s010 : ((claims016.drop 10).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK016_s012 : ((claims016.drop 12).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK016_s014 : ((claims016.drop 14).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK016_s016 : ((claims016.drop 16).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK016_s018 : ((claims016.drop 18).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK016_s020 : ((claims016.drop 20).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK016_s022 : ((claims016.drop 22).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK016_end : (claims016.drop 24).all claimTest=true := by
  decide +kernel

theorem claimOK016 : claims016.all claimTest=true := by
  have h22 := stitchAt 22 2 claimOK016_s022 claimOK016_end
  have h20 := stitchAt 20 2 claimOK016_s020 h22
  have h18 := stitchAt 18 2 claimOK016_s018 h20
  have h16 := stitchAt 16 2 claimOK016_s016 h18
  have h14 := stitchAt 14 2 claimOK016_s014 h16
  have h12 := stitchAt 12 2 claimOK016_s012 h14
  have h10 := stitchAt 10 2 claimOK016_s010 h12
  have h8 := stitchAt 8 2 claimOK016_s008 h10
  have h6 := stitchAt 6 2 claimOK016_s006 h8
  have h4 := stitchAt 4 2 claimOK016_s004 h6
  have h2 := stitchAt 2 2 claimOK016_s002 h4
  have h0 := stitchAt 0 2 claimOK016_s000 h2
  simpa only [List.drop_zero] using h0

private theorem claimOK017_s000 : ((claims017.drop 0).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK017_s002 : ((claims017.drop 2).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK017_s004 : ((claims017.drop 4).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK017_s006 : ((claims017.drop 6).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK017_s008 : ((claims017.drop 8).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK017_s010 : ((claims017.drop 10).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK017_s012 : ((claims017.drop 12).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK017_s014 : ((claims017.drop 14).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK017_s016 : ((claims017.drop 16).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK017_s018 : ((claims017.drop 18).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK017_s020 : ((claims017.drop 20).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK017_s022 : ((claims017.drop 22).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK017_end : (claims017.drop 24).all claimTest=true := by
  decide +kernel

theorem claimOK017 : claims017.all claimTest=true := by
  have h22 := stitchAt 22 2 claimOK017_s022 claimOK017_end
  have h20 := stitchAt 20 2 claimOK017_s020 h22
  have h18 := stitchAt 18 2 claimOK017_s018 h20
  have h16 := stitchAt 16 2 claimOK017_s016 h18
  have h14 := stitchAt 14 2 claimOK017_s014 h16
  have h12 := stitchAt 12 2 claimOK017_s012 h14
  have h10 := stitchAt 10 2 claimOK017_s010 h12
  have h8 := stitchAt 8 2 claimOK017_s008 h10
  have h6 := stitchAt 6 2 claimOK017_s006 h8
  have h4 := stitchAt 4 2 claimOK017_s004 h6
  have h2 := stitchAt 2 2 claimOK017_s002 h4
  have h0 := stitchAt 0 2 claimOK017_s000 h2
  simpa only [List.drop_zero] using h0


end RKCert.ReviewedNative.WeakFourFirstOnly.Replay.Unit
