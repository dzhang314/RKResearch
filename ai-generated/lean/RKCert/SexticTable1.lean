module
public import RKCert.SexticFiniteSetup
@[expose] public section
namespace RKCert.Sextic
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem checked_7 : (pack 7).all checkQuint=true := by decide +kernel
theorem checked_8 : (pack 8).all checkQuint=true := by decide +kernel
theorem checked_9 : (pack 9).all checkQuint=true := by decide +kernel
theorem checked_10 : (pack 10).all checkQuint=true := by decide +kernel
theorem checked_11 : (pack 11).all checkQuint=true := by decide +kernel
theorem checked_12 : (pack 12).all checkQuint=true := by decide +kernel
theorem checked_13 : (pack 13).all checkQuint=true := by decide +kernel
end RKCert.Sextic
