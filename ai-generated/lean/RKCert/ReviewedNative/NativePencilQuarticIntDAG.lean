module

public import RKCert.ReviewedNative.NativePencilQuarticIntDAGPart009

@[expose] public section
namespace RKResearch.Certified.Graded.NativePencilQuarticIntDAG
open NativeHornerWitness NativeHornerCheckpoints

set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

abbrev input_a : V2 := b10
abbrev input_b : V2 := b22
abbrev input_u : V2 := b33
abbrev input_v : V2 := b43
abbrev input_scale : V2 := b45
abbrev input_r : V2 := b47

theorem integer_certificate : o2.add (o2.mul input_u input_a) (o2.mul input_v input_b) = o2.mul input_scale input_r :=
  ((congrArg₂ o2.add e410 e812).trans e851).trans e857.symm

end RKResearch.Certified.Graded.NativePencilQuarticIntDAG
