module

public import RKCert.ReviewedNative.ERKOrder16WeakFourFirstRanksHigh

@[expose] public section

namespace RKCert.ReviewedNative.WeakFourFirstOnly.Replay.High
open RKCert.ReviewedNative.WeakFourFirstOnly.DataHigh
open RKCert.ReviewedNative.PolynomialCertificate (checkChain)
set_option maxRecDepth 12000
set_option maxHeartbeats 4000000

private theorem claimOK009_s000 : ((claims009.drop 0).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK009_s002 : ((claims009.drop 2).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK009_s004 : ((claims009.drop 4).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK009_s006 : ((claims009.drop 6).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK009_s008 : ((claims009.drop 8).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK009_s010 : ((claims009.drop 10).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK009_s012 : ((claims009.drop 12).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK009_s014 : ((claims009.drop 14).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK009_s016 : ((claims009.drop 16).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK009_s018 : ((claims009.drop 18).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK009_s020 : ((claims009.drop 20).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK009_s022 : ((claims009.drop 22).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK009_end : (claims009.drop 24).all claimTest=true := by
  decide +kernel

theorem claimOK009 : claims009.all claimTest=true := by
  have h22 := stitchAt 22 2 claimOK009_s022 claimOK009_end
  have h20 := stitchAt 20 2 claimOK009_s020 h22
  have h18 := stitchAt 18 2 claimOK009_s018 h20
  have h16 := stitchAt 16 2 claimOK009_s016 h18
  have h14 := stitchAt 14 2 claimOK009_s014 h16
  have h12 := stitchAt 12 2 claimOK009_s012 h14
  have h10 := stitchAt 10 2 claimOK009_s010 h12
  have h8 := stitchAt 8 2 claimOK009_s008 h10
  have h6 := stitchAt 6 2 claimOK009_s006 h8
  have h4 := stitchAt 4 2 claimOK009_s004 h6
  have h2 := stitchAt 2 2 claimOK009_s002 h4
  have h0 := stitchAt 0 2 claimOK009_s000 h2
  simpa only [List.drop_zero] using h0

private theorem claimOK010_s000 : ((claims010.drop 0).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK010_s002 : ((claims010.drop 2).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK010_s004 : ((claims010.drop 4).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK010_s006 : ((claims010.drop 6).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK010_s008 : ((claims010.drop 8).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK010_s010 : ((claims010.drop 10).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK010_s012 : ((claims010.drop 12).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK010_s014 : ((claims010.drop 14).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK010_s016 : ((claims010.drop 16).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK010_s018 : ((claims010.drop 18).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK010_s020 : ((claims010.drop 20).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK010_s022 : ((claims010.drop 22).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK010_end : (claims010.drop 24).all claimTest=true := by
  decide +kernel

theorem claimOK010 : claims010.all claimTest=true := by
  have h22 := stitchAt 22 2 claimOK010_s022 claimOK010_end
  have h20 := stitchAt 20 2 claimOK010_s020 h22
  have h18 := stitchAt 18 2 claimOK010_s018 h20
  have h16 := stitchAt 16 2 claimOK010_s016 h18
  have h14 := stitchAt 14 2 claimOK010_s014 h16
  have h12 := stitchAt 12 2 claimOK010_s012 h14
  have h10 := stitchAt 10 2 claimOK010_s010 h12
  have h8 := stitchAt 8 2 claimOK010_s008 h10
  have h6 := stitchAt 6 2 claimOK010_s006 h8
  have h4 := stitchAt 4 2 claimOK010_s004 h6
  have h2 := stitchAt 2 2 claimOK010_s002 h4
  have h0 := stitchAt 0 2 claimOK010_s000 h2
  simpa only [List.drop_zero] using h0

private theorem claimOK011_s000 : ((claims011.drop 0).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK011_s002 : ((claims011.drop 2).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK011_s004 : ((claims011.drop 4).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK011_s006 : ((claims011.drop 6).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK011_s008 : ((claims011.drop 8).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK011_s010 : ((claims011.drop 10).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK011_s012 : ((claims011.drop 12).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK011_s014 : ((claims011.drop 14).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK011_s016 : ((claims011.drop 16).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK011_s018 : ((claims011.drop 18).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK011_s020 : ((claims011.drop 20).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK011_s022 : ((claims011.drop 22).take 2).all claimTest=true := by
  decide +kernel

private theorem claimOK011_end : (claims011.drop 24).all claimTest=true := by
  decide +kernel

theorem claimOK011 : claims011.all claimTest=true := by
  have h22 := stitchAt 22 2 claimOK011_s022 claimOK011_end
  have h20 := stitchAt 20 2 claimOK011_s020 h22
  have h18 := stitchAt 18 2 claimOK011_s018 h20
  have h16 := stitchAt 16 2 claimOK011_s016 h18
  have h14 := stitchAt 14 2 claimOK011_s014 h16
  have h12 := stitchAt 12 2 claimOK011_s012 h14
  have h10 := stitchAt 10 2 claimOK011_s010 h12
  have h8 := stitchAt 8 2 claimOK011_s008 h10
  have h6 := stitchAt 6 2 claimOK011_s006 h8
  have h4 := stitchAt 4 2 claimOK011_s004 h6
  have h2 := stitchAt 2 2 claimOK011_s002 h4
  have h0 := stitchAt 0 2 claimOK011_s000 h2
  simpa only [List.drop_zero] using h0


end RKCert.ReviewedNative.WeakFourFirstOnly.Replay.High
