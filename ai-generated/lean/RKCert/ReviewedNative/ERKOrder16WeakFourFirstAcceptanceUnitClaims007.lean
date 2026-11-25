module

public import RKCert.ReviewedNative.ERKOrder16WeakFourFirstRanksUnit

@[expose] public section

namespace RKCert.ReviewedNative.WeakFourFirstOnly.Replay.Unit
open RKCert.ReviewedNative.WeakFourFirstOnly.DataUnit
open RKCert.ReviewedNative.PolynomialCertificate (checkChain)
set_option maxRecDepth 12000
set_option maxHeartbeats 4000000

private theorem claimOK021_s000 : ((claims021.drop 0).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK021_s002 : ((claims021.drop 2).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK021_s004 : ((claims021.drop 4).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK021_s006 : ((claims021.drop 6).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK021_s008 : ((claims021.drop 8).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK021_s010 : ((claims021.drop 10).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK021_s012 : ((claims021.drop 12).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK021_s014 : ((claims021.drop 14).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK021_s016 : ((claims021.drop 16).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK021_s018 : ((claims021.drop 18).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK021_s020 : ((claims021.drop 20).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK021_end : (claims021.drop 22).all claimTest=true := by
  decide +kernel

theorem claimOK021 : claims021.all claimTest=true := by
  have h20 := stitchAt 20 2 claimOK021_s020 claimOK021_end
  have h18 := stitchAt 18 2 claimOK021_s018 h20
  have h16 := stitchAt 16 2 claimOK021_s016 h18
  have h14 := stitchAt 14 2 claimOK021_s014 h16
  have h12 := stitchAt 12 2 claimOK021_s012 h14
  have h10 := stitchAt 10 2 claimOK021_s010 h12
  have h8 := stitchAt 8 2 claimOK021_s008 h10
  have h6 := stitchAt 6 2 claimOK021_s006 h8
  have h4 := stitchAt 4 2 claimOK021_s004 h6
  have h2 := stitchAt 2 2 claimOK021_s002 h4
  have h0 := stitchAt 0 2 claimOK021_s000 h2
  simpa only [List.drop_zero] using h0


end RKCert.ReviewedNative.WeakFourFirstOnly.Replay.Unit
