module

public import RKCert.ReviewedNative.DIRKRealIntegerFlagData

@[expose] public section

namespace RKResearch.Certified.DIRKRealOrderTenIntegerChecks
open DIRKRealIntegerFlagReplay DIRKRealOrderTenIntegerData
set_option maxHeartbeats 0
set_option maxRecDepth 50000

def blockA (d : Nat) : Bool := (List.finRange (packet.size d)).all (checkA packet d)
def blockC (d : Nat) : Bool := (List.finRange (packet.size d)).all (checkC packet d)
def blockS (d : Nat) : Bool := (List.finRange (packet.size d)).all (checkSilent packet d)
def blockP (d e : Nat) : Bool := (List.finRange (packet.size d)).all fun i =>
  (List.finRange (packet.size e)).all (checkProduct packet d e i)

end RKResearch.Certified.DIRKRealOrderTenIntegerChecks
