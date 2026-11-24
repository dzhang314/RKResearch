module
public import RKCert.PortGridSetup
@[expose] public section
namespace RKCert.PortRank
set_option maxHeartbeats 0
set_option maxRecDepth 50000
theorem verified_chunk40 : (caseChunk 40).all portCase=true := by decide +kernel
theorem verified_chunk41 : (caseChunk 41).all portCase=true := by decide +kernel
theorem verified_chunk42 : (caseChunk 42).all portCase=true := by decide +kernel
theorem verified_chunk43 : (caseChunk 43).all portCase=true := by decide +kernel
theorem verified_chunk44 : (caseChunk 44).all portCase=true := by decide +kernel
theorem verified_chunk45 : (caseChunk 45).all portCase=true := by decide +kernel
theorem verified_chunk46 : (caseChunk 46).all portCase=true := by decide +kernel
theorem verified_chunk47 : (caseChunk 47).all portCase=true := by decide +kernel
end RKCert.PortRank
