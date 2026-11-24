module
public import RKCert.PortGridSetup
@[expose] public section
namespace RKCert.PortRank
set_option maxHeartbeats 0
set_option maxRecDepth 50000
theorem verified_chunk0 : (caseChunk 0).all portCase=true := by decide +kernel
theorem verified_chunk1 : (caseChunk 1).all portCase=true := by decide +kernel
theorem verified_chunk2 : (caseChunk 2).all portCase=true := by decide +kernel
theorem verified_chunk3 : (caseChunk 3).all portCase=true := by decide +kernel
theorem verified_chunk4 : (caseChunk 4).all portCase=true := by decide +kernel
theorem verified_chunk5 : (caseChunk 5).all portCase=true := by decide +kernel
theorem verified_chunk6 : (caseChunk 6).all portCase=true := by decide +kernel
theorem verified_chunk7 : (caseChunk 7).all portCase=true := by decide +kernel
end RKCert.PortRank
