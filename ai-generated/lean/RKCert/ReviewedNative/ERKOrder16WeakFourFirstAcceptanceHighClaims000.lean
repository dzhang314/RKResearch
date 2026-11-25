module

public import RKCert.ReviewedNative.ERKOrder16WeakFourFirstRanksHigh

@[expose] public section

namespace RKCert.ReviewedNative.WeakFourFirstOnly.Replay.High
open RKCert.ReviewedNative.WeakFourFirstOnly.DataHigh
open RKCert.ReviewedNative.PolynomialCertificate (checkChain)
set_option maxRecDepth 12000
set_option maxHeartbeats 4000000

private theorem claimOK000_s000 : ((claims000.drop 0).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK000_s002 : ((claims000.drop 2).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK000_s004 : ((claims000.drop 4).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK000_s006 : ((claims000.drop 6).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK000_s008 : ((claims000.drop 8).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK000_s010 : ((claims000.drop 10).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK000_s012 : ((claims000.drop 12).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK000_s014 : ((claims000.drop 14).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK000_s016 : ((claims000.drop 16).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK000_s018 : ((claims000.drop 18).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK000_s020 : ((claims000.drop 20).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK000_s022 : ((claims000.drop 22).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK000_end : (claims000.drop 24).all claimTest=true := by
  decide +kernel

theorem claimOK000 : claims000.all claimTest=true := by
  have h22 := stitchAt 22 2 claimOK000_s022 claimOK000_end
  have h20 := stitchAt 20 2 claimOK000_s020 h22
  have h18 := stitchAt 18 2 claimOK000_s018 h20
  have h16 := stitchAt 16 2 claimOK000_s016 h18
  have h14 := stitchAt 14 2 claimOK000_s014 h16
  have h12 := stitchAt 12 2 claimOK000_s012 h14
  have h10 := stitchAt 10 2 claimOK000_s010 h12
  have h8 := stitchAt 8 2 claimOK000_s008 h10
  have h6 := stitchAt 6 2 claimOK000_s006 h8
  have h4 := stitchAt 4 2 claimOK000_s004 h6
  have h2 := stitchAt 2 2 claimOK000_s002 h4
  have h0 := stitchAt 0 2 claimOK000_s000 h2
  simpa only [List.drop_zero] using h0

private theorem claimOK001_s000 : ((claims001.drop 0).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK001_s002 : ((claims001.drop 2).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK001_s004 : ((claims001.drop 4).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK001_s006 : ((claims001.drop 6).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK001_s008 : ((claims001.drop 8).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK001_s010 : ((claims001.drop 10).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK001_s012 : ((claims001.drop 12).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK001_s014 : ((claims001.drop 14).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK001_s016 : ((claims001.drop 16).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK001_s018 : ((claims001.drop 18).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK001_s020 : ((claims001.drop 20).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK001_s022 : ((claims001.drop 22).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK001_end : (claims001.drop 24).all claimTest=true := by
  decide +kernel

theorem claimOK001 : claims001.all claimTest=true := by
  have h22 := stitchAt 22 2 claimOK001_s022 claimOK001_end
  have h20 := stitchAt 20 2 claimOK001_s020 h22
  have h18 := stitchAt 18 2 claimOK001_s018 h20
  have h16 := stitchAt 16 2 claimOK001_s016 h18
  have h14 := stitchAt 14 2 claimOK001_s014 h16
  have h12 := stitchAt 12 2 claimOK001_s012 h14
  have h10 := stitchAt 10 2 claimOK001_s010 h12
  have h8 := stitchAt 8 2 claimOK001_s008 h10
  have h6 := stitchAt 6 2 claimOK001_s006 h8
  have h4 := stitchAt 4 2 claimOK001_s004 h6
  have h2 := stitchAt 2 2 claimOK001_s002 h4
  have h0 := stitchAt 0 2 claimOK001_s000 h2
  simpa only [List.drop_zero] using h0

private theorem claimOK002_s000 : ((claims002.drop 0).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK002_s002 : ((claims002.drop 2).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK002_s004 : ((claims002.drop 4).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK002_s006 : ((claims002.drop 6).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK002_s008 : ((claims002.drop 8).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK002_s010 : ((claims002.drop 10).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK002_s012 : ((claims002.drop 12).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK002_s014 : ((claims002.drop 14).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK002_s016 : ((claims002.drop 16).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK002_s018 : ((claims002.drop 18).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK002_s020 : ((claims002.drop 20).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK002_s022 : ((claims002.drop 22).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK002_end : (claims002.drop 24).all claimTest=true := by
  decide +kernel

theorem claimOK002 : claims002.all claimTest=true := by
  have h22 := stitchAt 22 2 claimOK002_s022 claimOK002_end
  have h20 := stitchAt 20 2 claimOK002_s020 h22
  have h18 := stitchAt 18 2 claimOK002_s018 h20
  have h16 := stitchAt 16 2 claimOK002_s016 h18
  have h14 := stitchAt 14 2 claimOK002_s014 h16
  have h12 := stitchAt 12 2 claimOK002_s012 h14
  have h10 := stitchAt 10 2 claimOK002_s010 h12
  have h8 := stitchAt 8 2 claimOK002_s008 h10
  have h6 := stitchAt 6 2 claimOK002_s006 h8
  have h4 := stitchAt 4 2 claimOK002_s004 h6
  have h2 := stitchAt 2 2 claimOK002_s002 h4
  have h0 := stitchAt 0 2 claimOK002_s000 h2
  simpa only [List.drop_zero] using h0


end RKCert.ReviewedNative.WeakFourFirstOnly.Replay.High
