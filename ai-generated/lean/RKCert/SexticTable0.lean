module
public import RKCert.SexticFiniteSetup
@[expose] public section
namespace RKCert.Sextic
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem checked_0 : (pack 0).all checkQuint=true := by decide +kernel
theorem checked_1 : (pack 1).all checkQuint=true := by decide +kernel
theorem checked_2 : (pack 2).all checkQuint=true := by decide +kernel
theorem checked_3 : (pack 3).all checkQuint=true := by decide +kernel
theorem checked_4 : (pack 4).all checkQuint=true := by decide +kernel
theorem checked_5 : (pack 5).all checkQuint=true := by decide +kernel
theorem checked_6 : (pack 6).all checkQuint=true := by decide +kernel
end RKCert.Sextic
