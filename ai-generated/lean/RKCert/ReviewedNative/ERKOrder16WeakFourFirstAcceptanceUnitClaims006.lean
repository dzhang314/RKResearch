module

public import RKCert.ReviewedNative.ERKOrder16WeakFourFirstRanksUnit

@[expose] public section

namespace RKCert.ReviewedNative.WeakFourFirstOnly.Replay.Unit
open RKCert.ReviewedNative.WeakFourFirstOnly.DataUnit
open RKCert.ReviewedNative.PolynomialCertificate (checkChain)
set_option maxRecDepth 12000
set_option maxHeartbeats 4000000

private theorem claimOK018_s000 : ((claims018.drop 0).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK018_s002 : ((claims018.drop 2).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK018_s004 : ((claims018.drop 4).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK018_s006 : ((claims018.drop 6).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK018_s008 : ((claims018.drop 8).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK018_s010 : ((claims018.drop 10).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK018_s012 : ((claims018.drop 12).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK018_s014 : ((claims018.drop 14).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK018_s016 : ((claims018.drop 16).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK018_s018 : ((claims018.drop 18).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK018_s020 : ((claims018.drop 20).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK018_s022 : ((claims018.drop 22).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK018_end : (claims018.drop 24).all claimTest=true := by
  decide +kernel

theorem claimOK018 : claims018.all claimTest=true := by
  have h22 := stitchAt 22 2 claimOK018_s022 claimOK018_end
  have h20 := stitchAt 20 2 claimOK018_s020 h22
  have h18 := stitchAt 18 2 claimOK018_s018 h20
  have h16 := stitchAt 16 2 claimOK018_s016 h18
  have h14 := stitchAt 14 2 claimOK018_s014 h16
  have h12 := stitchAt 12 2 claimOK018_s012 h14
  have h10 := stitchAt 10 2 claimOK018_s010 h12
  have h8 := stitchAt 8 2 claimOK018_s008 h10
  have h6 := stitchAt 6 2 claimOK018_s006 h8
  have h4 := stitchAt 4 2 claimOK018_s004 h6
  have h2 := stitchAt 2 2 claimOK018_s002 h4
  have h0 := stitchAt 0 2 claimOK018_s000 h2
  simpa only [List.drop_zero] using h0

private theorem claimOK019_s000 : ((claims019.drop 0).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK019_s002 : ((claims019.drop 2).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK019_s004 : ((claims019.drop 4).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK019_s006 : ((claims019.drop 6).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK019_s008 : ((claims019.drop 8).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK019_s010 : ((claims019.drop 10).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK019_s012 : ((claims019.drop 12).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK019_s014 : ((claims019.drop 14).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK019_s016 : ((claims019.drop 16).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK019_s018 : ((claims019.drop 18).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK019_s020 : ((claims019.drop 20).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK019_s022 : ((claims019.drop 22).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK019_end : (claims019.drop 24).all claimTest=true := by
  decide +kernel

theorem claimOK019 : claims019.all claimTest=true := by
  have h22 := stitchAt 22 2 claimOK019_s022 claimOK019_end
  have h20 := stitchAt 20 2 claimOK019_s020 h22
  have h18 := stitchAt 18 2 claimOK019_s018 h20
  have h16 := stitchAt 16 2 claimOK019_s016 h18
  have h14 := stitchAt 14 2 claimOK019_s014 h16
  have h12 := stitchAt 12 2 claimOK019_s012 h14
  have h10 := stitchAt 10 2 claimOK019_s010 h12
  have h8 := stitchAt 8 2 claimOK019_s008 h10
  have h6 := stitchAt 6 2 claimOK019_s006 h8
  have h4 := stitchAt 4 2 claimOK019_s004 h6
  have h2 := stitchAt 2 2 claimOK019_s002 h4
  have h0 := stitchAt 0 2 claimOK019_s000 h2
  simpa only [List.drop_zero] using h0

private theorem claimOK020_s000 : ((claims020.drop 0).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK020_s002 : ((claims020.drop 2).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK020_s004 : ((claims020.drop 4).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK020_s006 : ((claims020.drop 6).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK020_s008 : ((claims020.drop 8).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK020_s010 : ((claims020.drop 10).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK020_s012 : ((claims020.drop 12).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK020_s014 : ((claims020.drop 14).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK020_s016 : ((claims020.drop 16).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK020_s018 : ((claims020.drop 18).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK020_s020 : ((claims020.drop 20).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK020_s022 : ((claims020.drop 22).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK020_end : (claims020.drop 24).all claimTest=true := by
  decide +kernel

theorem claimOK020 : claims020.all claimTest=true := by
  have h22 := stitchAt 22 2 claimOK020_s022 claimOK020_end
  have h20 := stitchAt 20 2 claimOK020_s020 h22
  have h18 := stitchAt 18 2 claimOK020_s018 h20
  have h16 := stitchAt 16 2 claimOK020_s016 h18
  have h14 := stitchAt 14 2 claimOK020_s014 h16
  have h12 := stitchAt 12 2 claimOK020_s012 h14
  have h10 := stitchAt 10 2 claimOK020_s010 h12
  have h8 := stitchAt 8 2 claimOK020_s008 h10
  have h6 := stitchAt 6 2 claimOK020_s006 h8
  have h4 := stitchAt 4 2 claimOK020_s004 h6
  have h2 := stitchAt 2 2 claimOK020_s002 h4
  have h0 := stitchAt 0 2 claimOK020_s000 h2
  simpa only [List.drop_zero] using h0


end RKCert.ReviewedNative.WeakFourFirstOnly.Replay.Unit
