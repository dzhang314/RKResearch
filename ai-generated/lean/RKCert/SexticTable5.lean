module
public import RKCert.SexticFiniteSetup
@[expose] public section
namespace RKCert.Sextic
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem checked_35 : (pack 35).all checkQuint=true := by decide +kernel
theorem checked_36 : (pack 36).all checkQuint=true := by decide +kernel
theorem checked_37 : (pack 37).all checkQuint=true := by decide +kernel
theorem checked_38 : (pack 38).all checkQuint=true := by decide +kernel
theorem checked_39 : (pack 39).all checkQuint=true := by decide +kernel
theorem checked_40 : (pack 40).all checkQuint=true := by decide +kernel
theorem checked_41 : (pack 41).all checkQuint=true := by decide +kernel
end RKCert.Sextic
