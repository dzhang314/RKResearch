module

public import RKCert.ReviewedNative.DIRK11Width14IntegerData

@[expose] public section
namespace RKResearch.Certified.DIRK11Width14IntegerChecks
open DIRK11Width14IntegerCore DIRK11Width14IntegerData
set_option maxHeartbeats 0
set_option maxRecDepth 50000


def blockARow (d i : Nat) : Bool :=
  if hi : i < packet.size d then checkA packet d ⟨i,hi⟩ else true
def blockC (d : Nat) : Bool := (List.finRange (packet.size d)).all (checkC packet d)
def blockS (d : Nat) : Bool := (List.finRange (packet.size d)).all (checkSilent packet d)
def blockP (d e : Nat) : Bool := (List.finRange (packet.size d)).all fun i =>
  (List.finRange (packet.size e)).all (checkProduct packet d e i)

end RKResearch.Certified.DIRK11Width14IntegerChecks
