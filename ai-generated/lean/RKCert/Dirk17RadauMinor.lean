module
public import RKCert.Dirk17RadauGrid
public import RKCert.SexticNative
@[expose] public section
namespace RKCert.RadauEight
open Polynomial RKCert.FixedFactor RKCert.DirkQuintic RKCert.Paired RKCert.Sextic
def oldFour {R:Type*} (v:Fin 5→R):List R := List.ofFn (fun i:Fin 4=>v i.castSucc)

def tupleFour {R:Type*} [CommRing R] (v:Fin 5→R):R := minor (coeffs (oldFour v)) (v (Fin.last 4))

noncomputable def universalFour : MvPolynomial (Fin 5) ℤ := tupleFour MvPolynomial.X

theorem map_tupleFour {R S:Type*} [CommRing R] [CommRing S] (f:R→+*S) (v:Fin 5→R):
    f (tupleFour v)=tupleFour (f ∘ v) := by
  have h:oldFour (f ∘ v)=(oldFour v).map f:=List.ofFn_comp' _ _
  simp [tupleFour,Sextic.minor,Sextic.row,h,Sextic.map_coeffs]

theorem eval_universalFour {R:Type*} [CommRing R] (v:Fin 5→R) : zEval universalFour v=tupleFour v := by
  let f:=MvPolynomial.eval₂Hom (Int.castRingHom R) v
  change f (tupleFour MvPolynomial.X)=_
  rw [map_tupleFour];congr 1;funext i;simp [f]

theorem tupleFour_scale {K:Type*} [Field K] (v:Fin 5→K) (c:K) :
    tupleFour (fun i=>c*v i)=c^8*tupleFour v := by
  have h:oldFour (fun i=>c*v i)=(oldFour v).map (c*·):=List.ofFn_comp' _ _
  have d:(linearProduct id (oldFour v)).natDegree=4:=by rw [degree_product];simp [oldFour]
  have cf (l:List K):FixedFactor.coeffs l=(linearProduct id l).coeff:=funext fun i=>(coeff_product l i).symm
  simp only [tupleFour,h,cf,scale_product,minor,row_scale,d]
  ring

end RKCert.RadauEight
