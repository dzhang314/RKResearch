module

public import RKCert.ReviewedNative.NativePencilCubicDAGPart056

@[expose] public section
namespace RKResearch.Certified.Graded.NativePencilCubicDAG
open NativeHornerWitness NativeHornerCheckpoints

set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

abbrev input_one : V3 := b2
abbrev input_r : V3 := b5
abbrev input_a : V3 := b13
abbrev input_h : V3 := b61
abbrev input_p : V3 := b70
abbrev input_v : V3 := b89
abbrev input_uR : V3 := b220
abbrev input_uA : V3 := b255
abbrev input_uP : V3 := b337

theorem modular_certificate : o3.mul input_v input_h = o3.add input_one (o3.add (o3.mul input_uR input_r) (o3.add (o3.mul input_uA input_a) (o3.mul input_uP input_p))) := by
  have h23 := (congrArg₂ o3.add e5391 e7886).trans e7983
  have h123 := (congrArg₂ o3.add e4556 h23).trans e8258
  have hRight := (congrArg (o3.add input_one) h123).trans e8263
  exact e3624.trans hRight.symm

end RKResearch.Certified.Graded.NativePencilCubicDAG
