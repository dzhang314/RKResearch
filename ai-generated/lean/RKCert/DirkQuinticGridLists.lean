module
public import RKCert.DirkQuinticTools
public import Mathlib.Tactic.NormNum.Prime
@[expose] public section
namespace RKCert.DirkQuintic
def grid9 : List (ZMod 10709) := [0,1103,3759,4862,5525,7562,7742,7829,8009,10046]
instance prime10709 : Fact (Nat.Prime 10709):=⟨by norm_num⟩
def grid10 : List (ZMod 15727) := [0,1069,1186,6796,7356,7876,8398,8920,9440,10000,15610]
instance prime15727 : Fact (Nat.Prime 15727):=⟨by norm_num⟩
end RKCert.DirkQuintic
