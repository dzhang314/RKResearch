module
public import RKCert.ReviewedNative.ERK13NativePencilCubicBridge
public import RKCert.ReviewedNative.NativePencilFivePrimitive
@[expose] public section
namespace RKResearch.Certified.Graded.ERK13NativePencil
open NativePencilPorts
variable {K : Type*} [Field K] [CharZero K]
theorem certified_cubic_pencil_cut : CubicPencilCut K := by
  intro P pd pn a d k t z bn tn zn z1 rt ru h1 h2 h3 h4 h5
  exact five_physical_ports_coprime P pd pn a d k t z bn tn zn z1 rt ru h1 h2 h3 h4 h5
end RKResearch.Certified.Graded.ERK13NativePencil
