
/-! Exact characteristic-zero arithmetic for the half-half equal-extra
edge-dormant ERK11 chart. The paper binds the finite interpolation
checks to its degree bounds and specialization arguments. -/
namespace RKResearch.ERK11NineSiteHalfSameEdgeGate
set_option maxRecDepth 16000
set_option maxHeartbeats 0

def prime : Int := 101
def hP : List Int := [67, 69, 25, 92, 78]
def cP : List Int := [98, 50, 24, 37, 59]
def mP : List Int := [25, 53, 10, 66, 93, 66, 34, 5, 33]
def nP : List Int := [0, 63, 26, 35, 79, 63, 47, 36]
def deltaP : List Int := [19, 67, 5, 96, 18, 76, 22, 54, 33, 85, 81, 29, 65, 91, 60, 40, 28, 69, 64, 65, 10, 51, 76, 78, 60, 83, 0, 10, 62, 63, 61]
def uP : List Int := [88, 40, 82, 79, 6, 22, 13, 3, 35, 20, 17, 39, 39, 57, 82, 84, 8, 3, 9, 90, 35, 15, 80, 75, 8, 92, 94, 61, 98, 46, 1]
def vP : List Int := [83, 70, 92, 76, 46, 70, 70, 60, 17, 7, 36, 16, 58, 72, 6, 28, 1, 10, 70, 30, 3, 48, 54, 12, 23, 29, 57, 11, 62, 2, 78]
def psiP : List Int := [0, 8, 97, 80, 3, 45, 8, 47, 14, 19, 1, 54, 10, 8, 43, 46, 54, 42, 36, 68, 56, 88, 67, 15, 69, 41, 95, 44, 34, 88, 99, 26, 5, 31, 74, 64, 55, 10, 73, 50, 27, 8, 3, 21, 9, 62, 78, 51, 34, 25, 12, 80, 57, 5, 59, 90, 87, 68, 44, 66, 4, 59, 16, 46, 99, 15, 52, 63, 67]
def gP : List Int := [0, 0, 0, 0, 0, 0, 0, 75, 28, 96, 77, 5, 27, 74, 44, 47, 90, 90, 30, 76, 94, 70, 3, 58, 41, 29, 38, 85, 20, 79, 17, 84, 47, 10, 6, 23, 23, 86, 97, 28, 35, 68, 82, 45, 13, 25, 72, 51, 54, 58, 3, 93, 74, 51, 36, 26, 31, 16, 66, 76, 12, 95, 94, 87, 60, 91, 48, 87, 54, 1, 18, 4, 5, 81, 52, 12, 99, 20, 3]
def bh : List Int := [42, 13, 17, 86]
def bc : List Int := [96, 62, 2, 1]
def bm : List Int := [97, 41, 28, 98, 63, 90, 66]
def bn : List Int := [40, 78, 70, 91, 96, 70, 28, 91]
def bd : List Int := [35, 94, 97, 76, 16, 83, 83, 7, 40, 82, 75, 2, 36, 33, 20, 30, 27, 72, 68, 64, 37, 94, 21, 54, 44, 31, 12, 17, 52, 7]
def bu : List Int := [20, 53, 51, 50, 44, 52, 46, 37, 41, 53, 57, 42, 26, 10, 11, 80, 45, 5, 79, 70, 21, 38, 70, 98, 51, 18, 45, 99, 71, 78]
def bv : List Int := []
def bq : List Int := [25, 0, 53, 55, 26, 62, 9, 3, 54, 17, 11, 40, 51, 87, 34, 100, 69, 19, 22, 86, 71, 96, 48, 48, 68, 90, 97, 76, 6, 13, 21, 6, 89, 93, 83, 15, 30, 76, 39, 48, 59, 36, 29, 61, 50, 65, 28, 70, 22, 100, 0, 41, 71, 63, 46, 77, 9, 18, 55, 86, 49, 67, 75, 3, 96, 20, 51, 87, 11, 85, 54, 4, 38, 49, 12, 39]
def bg : List Int := [65, 27, 61, 81, 71, 6, 36, 77, 50, 58, 54, 11, 96, 99, 58, 66, 31, 60, 38, 23, 80, 31, 56, 78, 94, 73, 16, 36, 99, 69, 13, 92, 78, 90, 21, 47, 38, 4, 81, 6, 66, 21, 6, 90, 32, 51, 97, 69, 20, 22, 69, 100, 75, 20, 75, 48, 83, 87, 69, 74, 68, 72, 4, 93, 40, 38]

def red (x : Int) : Int := x % prime
def add (x y : Int) : Int := red (x+y)
def mul (x y : Int) : Int := red (x*y)
def sum (xs : List Int) : Int := xs.foldl add 0
def ev (xs : List Int) (t : Int) : Int := xs.foldr (fun a z => add a (mul z t)) 0
def pg (xs : List Int) (i : Nat) : Int := xs[i]?.getD 0

def pa : List Int → List Int → List Int
  | [], ys => ys
  | xs, [] => xs
  | x::xs, y::ys => add x y :: pa xs ys

def pm (xs ys : List Int) : List Int :=
  if ys.isEmpty then [] else
    xs.foldr (fun c z => pa (ys.map (mul c)) (0::z)) []
def pprod (ps : List (List Int)) : List Int := ps.foldl pm [1]
def clean (ps : List Int) : List Int := (ps.reverse.dropWhile (· == 0)).reverse
def invI : List Int := [0,1,51,34,76,81,17,29,38,45,91,46]

def integ (ps : List Int) (shift : Nat) : Int :=
  sum (ps.zipIdx.map (fun (x,i) => mul x (pg invI (i+shift+1))))

def gram : List (List Int) :=
  [[3,-32,108,-144,66],[-32,388,-1404,1956,-924],[108,-1404,5316,-7644,3696],
   [-144,1956,-7644,11256,-5544],[66,-924,3696,-5544,2772]]
def t4 : List Int := [1,-32,216,-480,330]
def u44 : List (List Int) :=
  [[1,-32,216,-480,330],[-32,992,-6480,13920,-9240],[216,-6480,41040,-85680,55440],
   [-480,13920,-85680,174720,-110880],[330,-9240,55440,-110880,69300]]

def valueAt (a : Int) : List Int :=
  let b := red (2-a)
  let d := red (a-1)
  let h := mul a 51
  let vB := pprod [[1,-2,1],[d*d,-2*d,1]]
  let w := pm [0,0,a*a,-2*a,1] vB
  let jv := [0,0,0,mul (10*a*a) 64,mul (-15*a) 64,mul 6 64]
  let hv := pm jv vB
  let H := integ hv 0
  let C := integ hv 1
  let I0 := integ w 0
  let I1 := integ w 1
  let I2 := integ w 2
  let M := red (I1*H-I0*C)
  let N := red (I2*H-I1*C)
  let P := pprod [[-a,1],[-h,1],[-d,1],[-C,H],[0,1,-1]]
  let es := (List.range 4).map (fun i => red (M*integ P (i+1)-N*integ P i))
  let E0 := pg es 0
  let E1 := pg es 1
  let E2 := pg es 2
  let E3 := pg es 3
  let D := red (E0*E2-E1*E1)
  let U := red (E1*E2-E0*E3)
  let V := red (E1*E3-E2*E2)
  let L0 := red (a*a*D+a*U+V)
  let L1 := red (-V)
  let R0 := red (d*d*D+d*U+V)
  let R1 := red (-D-U-V)
  let Z := u44.foldr (fun xs z => add (ev xs b) (mul z a)) 0
  let Q := red (L0*R0+(ev t4 a)*L1*R0+(ev t4 b)*L0*R1+Z*L1*R1)
  let ds := (List.range 5).map (fun i =>
    red (a^5*N^(i+1)*M^(4-i)-a^(i+1)*N^3*(6*N^2-15*a*N*M+10*a^2*M^2)))
  let rs := (List.range 5).map (fun j =>
    red (R0+R1*(d^j-b*Int.ofNat j*d^(j-1))))
  let G := sum ((List.range 5).map (fun i =>
    sum ((List.range 5).map (fun j =>
      red ((pg ds i)*(pg (gram[i]?.getD []) j)*(pg rs j))))))
  [H,C,M,N,D,U,V,Q,G]

def tabs : List (List Int) := [hP,cP,mP,nP,deltaP,uP,vP,psiP,gP]
def check (start len : Nat) : Bool :=
  (List.range len).all (fun j =>
    let z := Int.ofNat (start+j)
    valueAt z == tabs.map (fun f => ev f z))

theorem primeAndInv :
    (List.range 99).all (fun i => 101 % (i+2) != 0) = true ∧
    (List.range 11).all (fun i => mul (Int.ofNat (i+1)) (pg invI (i+1)) == 1) = true ∧
    mul 30 64=1 := by decide +kernel

theorem leadingDegrees :
    (clean hP).length=5 ∧ (clean mP).length=9 ∧
    (clean deltaP).length=31 ∧ (clean psiP).length=69 := by decide +kernel

theorem bezoutCentroid :
    clean (pa (pm bh hP) (pm bc cP))=[1] ∧
    clean (pa (pm bm mP) (pm bn nP))=[1] := by decide +kernel

theorem bezoutSingular :
    clean (pa (pm bd deltaP) (pa (pm bu uP) (pm bv vP)))=[1] := by decide +kernel

theorem bezoutContact :
    clean (pa (pm bq psiP) (pm bg gP))=[0,99,1] := by decide +kernel

theorem grid0 : check 0 10 = true := by decide +kernel
theorem grid1 : check 10 10 = true := by decide +kernel
theorem grid2 : check 20 10 = true := by decide +kernel
theorem grid3 : check 30 10 = true := by decide +kernel
theorem grid4 : check 40 10 = true := by decide +kernel
theorem grid5 : check 50 10 = true := by decide +kernel
theorem grid6 : check 60 10 = true := by decide +kernel
theorem grid7 : check 70 10 = true := by decide +kernel
theorem grid8 : check 80 2 = true := by decide +kernel

end RKResearch.ERK11NineSiteHalfSameEdgeGate
#print axioms RKResearch.ERK11NineSiteHalfSameEdgeGate.primeAndInv
#print axioms RKResearch.ERK11NineSiteHalfSameEdgeGate.leadingDegrees
#print axioms RKResearch.ERK11NineSiteHalfSameEdgeGate.bezoutCentroid
#print axioms RKResearch.ERK11NineSiteHalfSameEdgeGate.bezoutSingular
#print axioms RKResearch.ERK11NineSiteHalfSameEdgeGate.bezoutContact
#print axioms RKResearch.ERK11NineSiteHalfSameEdgeGate.grid0
#print axioms RKResearch.ERK11NineSiteHalfSameEdgeGate.grid8
