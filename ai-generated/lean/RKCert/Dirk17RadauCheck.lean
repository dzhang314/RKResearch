module
public import RKCert.Dirk17RadauGrid
public import RKCert.SexticResidueBridge
@[expose] public section
namespace RKCert.RadauEight
open Polynomial RKCert.FixedFactor RKCert.DirkQuintic RKCert.Paired RKCert.Sextic
set_option maxHeartbeats 0
set_option maxRecDepth 150000
def checkFour (l:List ℤ):Bool:=
  let c:=coeffs l
  let a:=c 0;let b:=c 1;let q:=c 2;let d:=c 3;let e:=c 4;let f:=c 5
  integers.all fun u=>decide (u∈l) || decide ((Sextic.quick a b q d e f u)%293177≠0)

def pack (i:ℕ):List (List ℤ):=((integers.sublistsLen 4).drop (i*7)).take 7
private theorem b0:(pack 0).all checkFour=true:=by decide +kernel
private theorem b1:(pack 1).all checkFour=true:=by decide +kernel
private theorem b2:(pack 2).all checkFour=true:=by decide +kernel
private theorem b3:(pack 3).all checkFour=true:=by decide +kernel
private theorem b4:(pack 4).all checkFour=true:=by decide +kernel
private theorem b5:(pack 5).all checkFour=true:=by decide +kernel
private theorem b6:(pack 6).all checkFour=true:=by decide +kernel
private theorem b7:(pack 7).all checkFour=true:=by decide +kernel
private theorem b8:(pack 8).all checkFour=true:=by decide +kernel
private theorem b9:(pack 9).all checkFour=true:=by decide +kernel
private theorem b10:(pack 10).all checkFour=true:=by decide +kernel
private theorem b11:(pack 11).all checkFour=true:=by decide +kernel
private theorem b12:(pack 12).all checkFour=true:=by decide +kernel
private theorem b13:(pack 13).all checkFour=true:=by decide +kernel
private theorem b14:(pack 14).all checkFour=true:=by decide +kernel
private theorem b15:(pack 15).all checkFour=true:=by decide +kernel
private theorem b16:(pack 16).all checkFour=true:=by decide +kernel
private theorem b17:(pack 17).all checkFour=true:=by decide +kernel
theorem checked:(integers.sublistsLen 4).all checkFour=true:=by
  have eqn:integers.sublistsLen 4=pack 0 ++ pack 1 ++ pack 2 ++ pack 3 ++ pack 4 ++ pack 5 ++ pack 6 ++ pack 7 ++ pack 8 ++ pack 9 ++ pack 10 ++ pack 11 ++ pack 12 ++ pack 13 ++ pack 14 ++ pack 15 ++ pack 16 ++ pack 17:=by decide +kernel
  rw [eqn];simp only [List.all_append,b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15,b16,b17,Bool.and_self]
end RKCert.RadauEight
