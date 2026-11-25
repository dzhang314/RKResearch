module

public import RKCert.ReviewedNative.WeakFiveThreeInteriorPortCoordinates
public import RKCert.ReviewedNative.WeakFiveThreeInteriorStripPackets021

@[expose] public section

namespace RKCert.ReviewedNative.ThreeInteriorPencil

set_option maxRecDepth 16000
set_option maxHeartbeats 2000000

private theorem packet0504_port_checked : checkPortRow packet0504.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0505_port_checked : checkPortRow packet0505.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0506_port_checked : checkPortRow packet0506.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0507_port_checked : checkPortRow packet0507.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0508_port_checked : checkPortRow packet0508.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0509_port_checked : checkPortRow packet0509.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0510_port_checked : checkPortRow packet0510.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0511_port_checked : checkPortRow packet0511.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0512_port_checked : checkPortRow packet0512.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0513_port_checked : checkPortRow packet0513.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0514_port_checked : checkPortRow packet0514.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0515_port_checked : checkPortRow packet0515.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0516_port_checked : checkPortRow packet0516.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0517_port_checked : checkPortRow packet0517.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0518_port_checked : checkPortRow packet0518.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0519_port_checked : checkPortRow packet0519.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0520_port_checked : checkPortRow packet0520.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0521_port_checked : checkPortRow packet0521.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0522_port_checked : checkPortRow packet0522.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0523_port_checked : checkPortRow packet0523.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0524_port_checked : checkPortRow packet0524.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0525_port_checked : checkPortRow packet0525.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0526_port_checked : checkPortRow packet0526.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0527_port_checked : checkPortRow packet0527.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

theorem packets021_ports_checked :
    packets021.all (fun q => checkPortRow q.row) = true := by
  simp only [packets021,List.all_cons,List.all_nil,Bool.true_and,
    packet0504_port_checked, packet0505_port_checked, packet0506_port_checked, packet0507_port_checked,
    packet0508_port_checked, packet0509_port_checked, packet0510_port_checked, packet0511_port_checked,
    packet0512_port_checked, packet0513_port_checked, packet0514_port_checked, packet0515_port_checked,
    packet0516_port_checked, packet0517_port_checked, packet0518_port_checked, packet0519_port_checked,
    packet0520_port_checked, packet0521_port_checked, packet0522_port_checked, packet0523_port_checked,
    packet0524_port_checked, packet0525_port_checked, packet0526_port_checked, packet0527_port_checked]

end RKCert.ReviewedNative.ThreeInteriorPencil
