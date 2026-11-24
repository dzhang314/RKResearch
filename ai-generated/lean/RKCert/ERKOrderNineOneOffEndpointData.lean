module

public import RKCert.ERKGoodPrimeDense

@[expose] public section

/-! # Exact nondegeneracy of the one-off endpoint curve

The small integer identity used here replaces the manuscript's
modular resultant representation. No rational elimination command is trusted. -/
namespace RKCert.Paired.OneOff
open RKCert.GoodPrimeDense
def endpointEData : List (List ℤ) := [[5, -105, 910, -3990, 9212, -10584, 4704]]

def endpointFData : List (List ℤ) := [[5, -70, 280, -336], [-35, 560, -2408, 3024], [70, -1204, 5432, -7056], [-42, 756, -3528, 4704]]

def endpointGData : List (List ℤ) := [[0, 0, 0, 4], [0, 0, 2, -48], [0, -9, 216, -1512, 4480, -4032], [3, -72, 504, -1344, 1008]]

def endpointBData : List (List ℤ) := [[-35, 630, -3654, 9212, -10584, 4704], [70, -1246, 6188, -10584, 4704], [-42, 756, -3528, 4704]]

def endpointUData : List (List ℤ) := [[118189410, -2155279254, 15577916664, -51579715936, 76798691424, -40850753664], [-375881316, 6925316958, -50481722550, 168803868772, -253280119176, 135416884512], [244370943, -4512695649, 33213961158, -112173839652, 169370114256, -90862990848]]

def endpointVData : List (List ℤ) := [[658887586, -11373653550, 76458798948, -240888225368, 351739356192, -186475478784], [-560198898, 9602657106, -63820431024, 200916801120, -296135020944, 158797453248]]

def endpointWData : List (List ℤ) := [[827452082, -12602326716, 51738283520, -76798691424, 40850753664], [-4285820952, 65462735058, -247640403052, 294130872840, -135416884512], [7965726069, -120512009142, 388307877132, -185331708464, -68973133824], [-6973928808, 107932205892, -327123958224, 32008565568, 136112102784], [2388835260, -38518447968, 123128138448, -34028025696]]

end RKCert.Paired.OneOff
