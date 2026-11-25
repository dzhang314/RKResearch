module

public import RKCert.ReviewedNative.NativePencilQuarticDAGPart014

@[expose] public section
namespace RKResearch.Certified.Graded.NativePencilQuarticDAG
open NativeHornerWitness NativeHornerCheckpoints

set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

abbrev input_one : V3 := b2
abbrev input_r : V3 := b5
abbrev input_a : V3 := b17
abbrev input_h : V3 := b34
abbrev input_p : V3 := (List.nil : V3)
abbrev input_v : V3 := b45
abbrev input_uR : V3 := b70
abbrev input_uA : V3 := b86
abbrev input_uP : V3 := (List.nil : V3)

theorem modular_certificate : o3.mul input_v input_h = o3.add input_one (o3.add (o3.mul input_uR input_r) (o3.add (o3.mul input_uA input_a) (o3.mul input_uP input_p))) := by
  have h23 := (congrArg₂ o3.add e1295 e1296).trans e1294
  have h123 := (congrArg₂ o3.add e707 h23).trans e1345
  have hRight := (congrArg (o3.add input_one) h123).trans e1349
  exact e542.trans hRight.symm

end RKResearch.Certified.Graded.NativePencilQuarticDAG
