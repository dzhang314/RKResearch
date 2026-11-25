module

public import RKCert.ReviewedNative.WeakFiveThreeInteriorPortCoordinates
public import RKCert.ReviewedNative.WeakFiveThreeInteriorStripPackets042

@[expose] public section

namespace RKCert.ReviewedNative.ThreeInteriorPencil

set_option maxRecDepth 16000
set_option maxHeartbeats 2000000

private theorem packet1008_port_checked : checkPortRow packet1008.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet1009_port_checked : checkPortRow packet1009.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet1010_port_checked : checkPortRow packet1010.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet1011_port_checked : checkPortRow packet1011.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet1012_port_checked : checkPortRow packet1012.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet1013_port_checked : checkPortRow packet1013.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet1014_port_checked : checkPortRow packet1014.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet1015_port_checked : checkPortRow packet1015.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet1016_port_checked : checkPortRow packet1016.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet1017_port_checked : checkPortRow packet1017.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet1018_port_checked : checkPortRow packet1018.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet1019_port_checked : checkPortRow packet1019.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet1020_port_checked : checkPortRow packet1020.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet1021_port_checked : checkPortRow packet1021.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet1022_port_checked : checkPortRow packet1022.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet1023_port_checked : checkPortRow packet1023.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet1024_port_checked : checkPortRow packet1024.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet1025_port_checked : checkPortRow packet1025.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet1026_port_checked : checkPortRow packet1026.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet1027_port_checked : checkPortRow packet1027.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet1028_port_checked : checkPortRow packet1028.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet1029_port_checked : checkPortRow packet1029.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet1030_port_checked : checkPortRow packet1030.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet1031_port_checked : checkPortRow packet1031.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

theorem packets042_ports_checked :
    packets042.all (fun q => checkPortRow q.row) = true := by
  simp only [packets042,List.all_cons,List.all_nil,Bool.true_and,
    packet1008_port_checked, packet1009_port_checked, packet1010_port_checked, packet1011_port_checked,
    packet1012_port_checked, packet1013_port_checked, packet1014_port_checked, packet1015_port_checked,
    packet1016_port_checked, packet1017_port_checked, packet1018_port_checked, packet1019_port_checked,
    packet1020_port_checked, packet1021_port_checked, packet1022_port_checked, packet1023_port_checked,
    packet1024_port_checked, packet1025_port_checked, packet1026_port_checked, packet1027_port_checked,
    packet1028_port_checked, packet1029_port_checked, packet1030_port_checked, packet1031_port_checked]

end RKCert.ReviewedNative.ThreeInteriorPencil
