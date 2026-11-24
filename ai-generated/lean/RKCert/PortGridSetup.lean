module
public import RKCert.PortMomentMatrix
public import RKCert.MarkedFactorTransfer
public import RKCert.LobattoFactorTables

@[expose] public section
namespace RKCert.PortRank
open Polynomial RKCert.FixedFactor
universe u

noncomputable def H : ℤ[X]:=(X-C 429)*grid7
noncomputable def F : ℤ[X]:=X*H

def derivativeKnots : List (ZMod 1361) := [51,378,478,609,1181,1312]
def nonzeroKnots : List (ZMod 1361) := 429::derivativeKnots
def allKnots : List (ZMod 1361) := 0::nonzeroKnots

set_option maxRecDepth 50000 in
instance portPrime : Fact (Nat.Prime 1361) := ⟨by decide +kernel⟩

theorem monic_H : H.Monic := (monic_X_sub_C _).mul monic_grid7
theorem monic_F : F.Monic := monic_X.mul monic_H

theorem derivative_split : grid7.map (Int.castRingHom (ZMod 1361))=linearProduct id derivativeKnots := by
  apply z_grid_split _ _ (by decide); intro i hi
  change i≤6 at hi; interval_cases i <;> decide

theorem H_split : H.map (Int.castRingHom (ZMod 1361))=linearProduct id nonzeroKnots := by
  rw [H,Polynomial.map_mul,Polynomial.map_sub,map_X,map_C,derivative_split]
  rfl

theorem F_split : F.map (Int.castRingHom (ZMod 1361))=linearProduct id allKnots :=
  splitX _ _ H_split

def portCase {R : Type*} [CommRing R] [DecidableEq R] (t:List R) : Bool :=
  decide (5<t.length) || t.all fun w=>decide (w=0) || decide (smallDet 5 (portMatrix (coeffs t) w)≠0)

def portChecked {R : Type*} [CommRing R] [DecidableEq R] (l:List R) : Bool := l.sublists.all portCase

theorem portCheckSound {E : Type*} [Field E] [DecidableEq E] {l t:List E} (h:portChecked l=true)
    (sub:t.Sublist l) (deg:t.length≤5) {w:E} (mem:w∈t) (nz:w≠0) :
    portDet (linearProduct id t) w≠0 := by
  have ht := List.all_eq_true.mp h t (List.mem_sublists.mpr sub)
  simp only [portCase,Bool.or_eq_true,decide_eq_true_eq] at ht
  have hw:=List.all_eq_true.mp (ht.resolve_left (Nat.not_lt_of_ge deg)) w mem
  simp only [Bool.or_eq_true,decide_eq_true_eq] at hw
  rw [portDet_product]
  exact hw.resolve_left nz


def caseChunk (i:ℕ) : List (List (ZMod 1361)) := (allKnots.sublists.drop (i*4)).take 4

end RKCert.PortRank
