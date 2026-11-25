module

public import RKCert.ReviewedNative.WeakFiveThreeInteriorPortCoordinates
public import RKCert.ReviewedNative.WeakFiveThreeInteriorStripPackets041

@[expose] public section

namespace RKCert.ReviewedNative.ThreeInteriorPencil

set_option maxRecDepth 16000
set_option maxHeartbeats 2000000

private theorem packet0984_port_checked : checkPortRow packet0984.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0985_port_checked : checkPortRow packet0985.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0986_port_checked : checkPortRow packet0986.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0987_port_checked : checkPortRow packet0987.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0988_port_checked : checkPortRow packet0988.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0989_port_checked : checkPortRow packet0989.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0990_port_checked : checkPortRow packet0990.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0991_port_checked : checkPortRow packet0991.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0992_port_checked : checkPortRow packet0992.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0993_port_checked : checkPortRow packet0993.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0994_port_checked : checkPortRow packet0994.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0995_port_checked : checkPortRow packet0995.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0996_port_checked : checkPortRow packet0996.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0997_port_checked : checkPortRow packet0997.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0998_port_checked : checkPortRow packet0998.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0999_port_checked : checkPortRow packet0999.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet1000_port_checked : checkPortRow packet1000.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet1001_port_checked : checkPortRow packet1001.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet1002_port_checked : checkPortRow packet1002.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet1003_port_checked : checkPortRow packet1003.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet1004_port_checked : checkPortRow packet1004.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet1005_port_checked : checkPortRow packet1005.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet1006_port_checked : checkPortRow packet1006.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet1007_port_checked : checkPortRow packet1007.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

theorem packets041_ports_checked :
    packets041.all (fun q => checkPortRow q.row) = true := by
  simp only [packets041,List.all_cons,List.all_nil,Bool.true_and,
    packet0984_port_checked, packet0985_port_checked, packet0986_port_checked, packet0987_port_checked,
    packet0988_port_checked, packet0989_port_checked, packet0990_port_checked, packet0991_port_checked,
    packet0992_port_checked, packet0993_port_checked, packet0994_port_checked, packet0995_port_checked,
    packet0996_port_checked, packet0997_port_checked, packet0998_port_checked, packet0999_port_checked,
    packet1000_port_checked, packet1001_port_checked, packet1002_port_checked, packet1003_port_checked,
    packet1004_port_checked, packet1005_port_checked, packet1006_port_checked, packet1007_port_checked]

end RKCert.ReviewedNative.ThreeInteriorPencil
