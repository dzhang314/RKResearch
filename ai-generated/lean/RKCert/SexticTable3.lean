module
public import RKCert.SexticFiniteSetup
@[expose] public section
namespace RKCert.Sextic
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem checked_21 : (pack 21).all checkQuint=true := by decide +kernel
theorem checked_22 : (pack 22).all checkQuint=true := by decide +kernel
theorem checked_23 : (pack 23).all checkQuint=true := by decide +kernel
theorem checked_24 : (pack 24).all checkQuint=true := by decide +kernel
theorem checked_25 : (pack 25).all checkQuint=true := by decide +kernel
theorem checked_26 : (pack 26).all checkQuint=true := by decide +kernel
theorem checked_27 : (pack 27).all checkQuint=true := by decide +kernel
end RKCert.Sextic
