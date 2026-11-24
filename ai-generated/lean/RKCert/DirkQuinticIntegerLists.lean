module
public import RKCert.DirkQuinticSorted
@[expose] public section
namespace RKCert.DirkQuintic
def integers9 : List ℤ := [0,1103,3759,4862,5525,7562,7742,7829,8009,10046]
theorem map_integers9 : grid9=integers9.map (Int.castRingHom (ZMod 10709)) :=by decide +kernel
def integers10 : List ℤ := [0,1069,1186,6796,7356,7876,8398,8920,9440,10000,15610]
theorem map_integers10 : grid10=integers10.map (Int.castRingHom (ZMod 15727)) :=by decide +kernel
end RKCert.DirkQuintic
