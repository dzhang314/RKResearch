module
public import RKCert.PortResidueBridge
public import RKCert.PortGridChecks0
public import RKCert.PortGridChecks1
public import RKCert.PortGridChecks2
public import RKCert.PortGridChecks3
public import RKCert.PortGridChecks4
public import RKCert.PortGridChecks5
public import RKCert.PortGridChecks6
public import RKCert.PortGridChecks7

@[expose] public section
namespace RKCert.PortRank
open Polynomial RKCert.FixedFactor
universe u

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem checked_port : portChecked allKnots=true := by
  have part : allKnots.sublists = caseChunk 0 ++ caseChunk 1 ++ caseChunk 2 ++ caseChunk 3 ++ caseChunk 4 ++ caseChunk 5 ++ caseChunk 6 ++ caseChunk 7 ++ caseChunk 8 ++ caseChunk 9 ++ caseChunk 10 ++ caseChunk 11 ++ caseChunk 12 ++ caseChunk 13 ++ caseChunk 14 ++ caseChunk 15 ++ caseChunk 16 ++ caseChunk 17 ++ caseChunk 18 ++ caseChunk 19 ++ caseChunk 20 ++ caseChunk 21 ++ caseChunk 22 ++ caseChunk 23 ++ caseChunk 24 ++ caseChunk 25 ++ caseChunk 26 ++ caseChunk 27 ++ caseChunk 28 ++ caseChunk 29 ++ caseChunk 30 ++ caseChunk 31 ++ caseChunk 32 ++ caseChunk 33 ++ caseChunk 34 ++ caseChunk 35 ++ caseChunk 36 ++ caseChunk 37 ++ caseChunk 38 ++ caseChunk 39 ++ caseChunk 40 ++ caseChunk 41 ++ caseChunk 42 ++ caseChunk 43 ++ caseChunk 44 ++ caseChunk 45 ++ caseChunk 46 ++ caseChunk 47 ++ caseChunk 48 ++ caseChunk 49 ++ caseChunk 50 ++ caseChunk 51 ++ caseChunk 52 ++ caseChunk 53 ++ caseChunk 54 ++ caseChunk 55 ++ caseChunk 56 ++ caseChunk 57 ++ caseChunk 58 ++ caseChunk 59 ++ caseChunk 60 ++ caseChunk 61 ++ caseChunk 62 ++ caseChunk 63 := by decide +kernel
  rw [portChecked,part]
  simp only [List.all_append,verified_chunk0,verified_chunk1,verified_chunk2,verified_chunk3,verified_chunk4,verified_chunk5,verified_chunk6,verified_chunk7,verified_chunk8,verified_chunk9,verified_chunk10,verified_chunk11,verified_chunk12,verified_chunk13,verified_chunk14,verified_chunk15,verified_chunk16,verified_chunk17,verified_chunk18,verified_chunk19,verified_chunk20,verified_chunk21,verified_chunk22,verified_chunk23,verified_chunk24,verified_chunk25,verified_chunk26,verified_chunk27,verified_chunk28,verified_chunk29,verified_chunk30,verified_chunk31,verified_chunk32,verified_chunk33,verified_chunk34,verified_chunk35,verified_chunk36,verified_chunk37,verified_chunk38,verified_chunk39,verified_chunk40,verified_chunk41,verified_chunk42,verified_chunk43,verified_chunk44,verified_chunk45,verified_chunk46,verified_chunk47,verified_chunk48,verified_chunk49,verified_chunk50,verified_chunk51,verified_chunk52,verified_chunk53,verified_chunk54,verified_chunk55,verified_chunk56,verified_chunk57,verified_chunk58,verified_chunk59,verified_chunk60,verified_chunk61,verified_chunk62,verified_chunk63,Bool.and_self]

theorem port_det_integral {K : Type u} [Field K] [CharZero K] (P:K[X]) (w:K)
    (pm:P.Monic) (pd:P∣F.map (Int.castRingHom K)) (deg:P.natDegree≤5)
    (hw:(H.map (Int.castRingHom K)).eval w=0) (pw:P.eval w=0) : portDet P w≠0 :=
  port_det_integral_of_checked checked_port P w pm pd deg hw pw

end RKCert.PortRank
