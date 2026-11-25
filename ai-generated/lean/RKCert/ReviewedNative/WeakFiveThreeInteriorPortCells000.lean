module

public import RKCert.ReviewedNative.WeakFiveThreeInteriorPortCoordinates
public import RKCert.ReviewedNative.WeakFiveThreeInteriorStripPackets000

@[expose] public section

namespace RKCert.ReviewedNative.ThreeInteriorPencil

set_option maxRecDepth 16000
set_option maxHeartbeats 2000000

private theorem packet0000_port_checked : checkPortRow packet0000.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0001_port_checked : checkPortRow packet0001.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0002_port_checked : checkPortRow packet0002.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0003_port_checked : checkPortRow packet0003.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0004_port_checked : checkPortRow packet0004.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0005_port_checked : checkPortRow packet0005.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0006_port_checked : checkPortRow packet0006.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0007_port_checked : checkPortRow packet0007.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0008_port_checked : checkPortRow packet0008.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0009_port_checked : checkPortRow packet0009.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0010_port_checked : checkPortRow packet0010.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0011_port_checked : checkPortRow packet0011.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0012_port_checked : checkPortRow packet0012.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0013_port_checked : checkPortRow packet0013.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0014_port_checked : checkPortRow packet0014.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0015_port_checked : checkPortRow packet0015.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0016_port_checked : checkPortRow packet0016.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0017_port_checked : checkPortRow packet0017.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0018_port_checked : checkPortRow packet0018.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0019_port_checked : checkPortRow packet0019.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0020_port_checked : checkPortRow packet0020.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0021_port_checked : checkPortRow packet0021.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0022_port_checked : checkPortRow packet0022.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0023_port_checked : checkPortRow packet0023.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

theorem packets000_ports_checked :
    packets000.all (fun q => checkPortRow q.row) = true := by
  simp only [packets000,List.all_cons,List.all_nil,Bool.true_and,
    packet0000_port_checked, packet0001_port_checked, packet0002_port_checked, packet0003_port_checked,
    packet0004_port_checked, packet0005_port_checked, packet0006_port_checked, packet0007_port_checked,
    packet0008_port_checked, packet0009_port_checked, packet0010_port_checked, packet0011_port_checked,
    packet0012_port_checked, packet0013_port_checked, packet0014_port_checked, packet0015_port_checked,
    packet0016_port_checked, packet0017_port_checked, packet0018_port_checked, packet0019_port_checked,
    packet0020_port_checked, packet0021_port_checked, packet0022_port_checked, packet0023_port_checked]

end RKCert.ReviewedNative.ThreeInteriorPencil
