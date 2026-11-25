module

public import RKCert.ReviewedNative.NativePencilCubicIntDAGPart004

@[expose] public section
namespace RKResearch.Certified.Graded.NativePencilCubicIntDAG
open NativeHornerWitness NativeHornerCheckpoints

set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

abbrev input_a : V2 := b6
abbrev input_b : V2 := b13
abbrev input_u : V2 := b19
abbrev input_v : V2 := b25
abbrev input_scale : V2 := b27
abbrev input_r : V2 := b29

theorem integer_certificate : o2.add (o2.mul input_u input_a) (o2.mul input_v input_b) = o2.mul input_scale input_r :=
  ((congrArg₂ o2.add e123 e278).trans e299).trans e322.symm

end RKResearch.Certified.Graded.NativePencilCubicIntDAG
