module

public import RKCert.ReviewedNative.WeakFiveThreeInteriorPortCoordinates
public import RKCert.ReviewedNative.WeakFiveThreeInteriorStripPackets015

@[expose] public section

namespace RKCert.ReviewedNative.ThreeInteriorPencil

set_option maxRecDepth 16000
set_option maxHeartbeats 2000000

private theorem packet0360_port_checked : checkPortRow packet0360.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0361_port_checked : checkPortRow packet0361.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0362_port_checked : checkPortRow packet0362.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0363_port_checked : checkPortRow packet0363.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0364_port_checked : checkPortRow packet0364.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0365_port_checked : checkPortRow packet0365.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0366_port_checked : checkPortRow packet0366.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0367_port_checked : checkPortRow packet0367.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0368_port_checked : checkPortRow packet0368.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0369_port_checked : checkPortRow packet0369.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0370_port_checked : checkPortRow packet0370.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0371_port_checked : checkPortRow packet0371.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0372_port_checked : checkPortRow packet0372.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0373_port_checked : checkPortRow packet0373.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0374_port_checked : checkPortRow packet0374.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0375_port_checked : checkPortRow packet0375.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0376_port_checked : checkPortRow packet0376.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0377_port_checked : checkPortRow packet0377.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0378_port_checked : checkPortRow packet0378.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0379_port_checked : checkPortRow packet0379.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0380_port_checked : checkPortRow packet0380.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0381_port_checked : checkPortRow packet0381.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0382_port_checked : checkPortRow packet0382.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0383_port_checked : checkPortRow packet0383.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

theorem packets015_ports_checked :
    packets015.all (fun q => checkPortRow q.row) = true := by
  simp only [packets015,List.all_cons,List.all_nil,Bool.true_and,
    packet0360_port_checked, packet0361_port_checked, packet0362_port_checked, packet0363_port_checked,
    packet0364_port_checked, packet0365_port_checked, packet0366_port_checked, packet0367_port_checked,
    packet0368_port_checked, packet0369_port_checked, packet0370_port_checked, packet0371_port_checked,
    packet0372_port_checked, packet0373_port_checked, packet0374_port_checked, packet0375_port_checked,
    packet0376_port_checked, packet0377_port_checked, packet0378_port_checked, packet0379_port_checked,
    packet0380_port_checked, packet0381_port_checked, packet0382_port_checked, packet0383_port_checked]

end RKCert.ReviewedNative.ThreeInteriorPencil
