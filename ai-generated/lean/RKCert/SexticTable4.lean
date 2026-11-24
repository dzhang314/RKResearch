module
public import RKCert.SexticFiniteSetup
@[expose] public section
namespace RKCert.Sextic
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem checked_28 : (pack 28).all checkQuint=true := by decide +kernel
theorem checked_29 : (pack 29).all checkQuint=true := by decide +kernel
theorem checked_30 : (pack 30).all checkQuint=true := by decide +kernel
theorem checked_31 : (pack 31).all checkQuint=true := by decide +kernel
theorem checked_32 : (pack 32).all checkQuint=true := by decide +kernel
theorem checked_33 : (pack 33).all checkQuint=true := by decide +kernel
theorem checked_34 : (pack 34).all checkQuint=true := by decide +kernel
end RKCert.Sextic
