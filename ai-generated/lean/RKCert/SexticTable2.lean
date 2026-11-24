module
public import RKCert.SexticFiniteSetup
@[expose] public section
namespace RKCert.Sextic
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem checked_14 : (pack 14).all checkQuint=true := by decide +kernel
theorem checked_15 : (pack 15).all checkQuint=true := by decide +kernel
theorem checked_16 : (pack 16).all checkQuint=true := by decide +kernel
theorem checked_17 : (pack 17).all checkQuint=true := by decide +kernel
theorem checked_18 : (pack 18).all checkQuint=true := by decide +kernel
theorem checked_19 : (pack 19).all checkQuint=true := by decide +kernel
theorem checked_20 : (pack 20).all checkQuint=true := by decide +kernel
end RKCert.Sextic
