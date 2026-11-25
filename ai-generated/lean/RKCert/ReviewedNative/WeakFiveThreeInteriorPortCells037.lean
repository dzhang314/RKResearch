module

public import RKCert.ReviewedNative.WeakFiveThreeInteriorPortCoordinates
public import RKCert.ReviewedNative.WeakFiveThreeInteriorStripPackets037

@[expose] public section

namespace RKCert.ReviewedNative.ThreeInteriorPencil

set_option maxRecDepth 16000
set_option maxHeartbeats 2000000

private theorem packet0888_port_checked : checkPortRow packet0888.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0889_port_checked : checkPortRow packet0889.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0890_port_checked : checkPortRow packet0890.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0891_port_checked : checkPortRow packet0891.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0892_port_checked : checkPortRow packet0892.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0893_port_checked : checkPortRow packet0893.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0894_port_checked : checkPortRow packet0894.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0895_port_checked : checkPortRow packet0895.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0896_port_checked : checkPortRow packet0896.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0897_port_checked : checkPortRow packet0897.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0898_port_checked : checkPortRow packet0898.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0899_port_checked : checkPortRow packet0899.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0900_port_checked : checkPortRow packet0900.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0901_port_checked : checkPortRow packet0901.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0902_port_checked : checkPortRow packet0902.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0903_port_checked : checkPortRow packet0903.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0904_port_checked : checkPortRow packet0904.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0905_port_checked : checkPortRow packet0905.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0906_port_checked : checkPortRow packet0906.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0907_port_checked : checkPortRow packet0907.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0908_port_checked : checkPortRow packet0908.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0909_port_checked : checkPortRow packet0909.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0910_port_checked : checkPortRow packet0910.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0911_port_checked : checkPortRow packet0911.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

theorem packets037_ports_checked :
    packets037.all (fun q => checkPortRow q.row) = true := by
  simp only [packets037,List.all_cons,List.all_nil,Bool.true_and,
    packet0888_port_checked, packet0889_port_checked, packet0890_port_checked, packet0891_port_checked,
    packet0892_port_checked, packet0893_port_checked, packet0894_port_checked, packet0895_port_checked,
    packet0896_port_checked, packet0897_port_checked, packet0898_port_checked, packet0899_port_checked,
    packet0900_port_checked, packet0901_port_checked, packet0902_port_checked, packet0903_port_checked,
    packet0904_port_checked, packet0905_port_checked, packet0906_port_checked, packet0907_port_checked,
    packet0908_port_checked, packet0909_port_checked, packet0910_port_checked, packet0911_port_checked]

end RKCert.ReviewedNative.ThreeInteriorPencil
