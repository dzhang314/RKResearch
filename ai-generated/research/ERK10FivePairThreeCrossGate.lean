import Lean

/-! Exact scalar checks for the all-live three-crossing ERK10 equality exit. -/
namespace RKResearch.ERK10FivePairThreeCrossGate
open Lean.Grind
variable {K : Type} [Field K]

def mixed (p q : K) : K :=
  70*p^2*q^2-80*p^2*q+25*p^2-60*p*q^2+75*p*q-25*p+
    15*q^2-20*q+7

def mixSame (u : K) : K := 10*u^4-5*u^2+1
def hullSame (u : K) : K := 126*u^6-138*u^4+51*u^2-5
theorem mixAtSame (u : K) : mixed (1+u) u=7*mixSame u := by
  unfold mixed mixSame
  grind
theorem sameBezout (u : K) :
    (1475-450*u^2)*hullSame u+(11103-21960*u^2+5670*u^4)*mixSame u=3728 := by
  unfold hullSame mixSame
  grind

def e (h : K) : K := -160*h-35
def f (h : K) : K := 100*h^2+50*h+7
def quad (k h : K) : K := 70*k^2+e h*k+f h
theorem mixActivated (m h : K) :
    mixed (1+m+h) (m-h)=quad (m^2-h^2) h := by
  unfold mixed quad e f
  grind

def a (k h : K) : K := 35*k^2-35*k*h+14*k+14*h^2-7*h-1
def b (k h : K) : K := -21*k+14*h-1
def c (k h : K) : K := 21*k^2-21*k*h+24*k+18*h^2-9*h-1
def d (k h : K) : K := -9*k+6*h-1
def cZero (h : K) : K := 21*h^4+21*h^3-6*h^2-9*h-1
def mixZero (h : K) : K := 70*h^4+160*h^3+135*h^2+50*h+7

theorem zeroSubstitution (h : K) :
    c (-h^2) h=cZero h ∧ quad (-h^2) h=mixZero h := by
  unfold c cZero quad e f mixZero
  constructor <;> grind

theorem zeroBezout (h : K) :
    (-62335-376275*h-772950*h^2-526050*h^3)*cZero h+
      (-8817-70920*h+28980*h^2+157815*h^3)*mixZero h=616 := by
  unfold cZero mixZero
  grind

def a1 (h : K) : K := 1440*h^3+47760*h^2+45780*h+7287
def a0 (h : K) : K := -480*h^4-62640*h^3-84708*h^2-33838*h-4473
def b1 (h : K) : K := -11520*h^2-9660*h-2331
def b0 (h : K) : K := 15600*h^3+17460*h^2+6622*h+805

theorem firstMinorRemainder (k h : K) :
    280*(a k h*c k h-3*(k+h^2)*(b k h)^2)-(a1 h*k+a0 h)=
      (2940*k^2+840*k*h+714*k-936*h^2+624*h+679)*quad k h := by
  unfold a b c a1 a0 quad e f
  grind

theorem secondMinorRemainder (k h : K) :
    35*(3*a k h*d k h-b k h*c k h)-(b1 h*k+b0 h)=
      (-252*k-156*h-105)*quad k h := by
  unfold a b c d b1 b0 quad e f
  grind

theorem linearNorm (k h u v : K) :
    70*v^2-e h*u*v+f h*u^2 =
      u^2*quad k h-(70*u*k+e h*u-70*v)*(u*k+v) := by
  unfold quad
  grind

def r1 (h : K) : K :=
  18000*h^8-9000*h^7+3646800*h^6+13056600*h^5+
    18844890*h^4+14077260*h^3+5722775*h^2+1196265*h+100674
def r2 (h : K) : K :=
  13860000*h^6+39654000*h^5+46761450*h^4+29293950*h^3+
    10354120*h^2+1969310*h+158221

theorem firstNorm (h : K) :
    70*(a0 h)^2-e h*a1 h*a0 h+f h*(a1 h)^2=6272*r1 h := by
  unfold e f r1 a1 a0
  grind

theorem secondNorm (h : K) :
    70*(b0 h)^2-e h*b1 h*b0 h+f h*(b1 h)^2=112*r2 h := by
  unfold e f r2 b1 b0
  grind

def term (a : List Int) (i : Nat) : Int := (a[i]?).getD 0
def product (a b : List Int) : List Int :=
  (List.range (a.length+b.length-1)).map (fun k =>
    (List.range (k+1)).foldl (fun s i => s+term a i*term b (k-i)) 0)

def R1 : List Int :=
  [100674,1196265,5722775,14077260,18844890,13056600,3646800,-9000,18000]
def R2 : List Int :=
  [158221,1969310,10354120,29293950,46761450,39654000,13860000]
def bezoutU : List Int :=
  [-1543973141177890764191721622763177350803671359566,
    -17239189689527380257421358471311515661047699876640,
    -78887136983743048529126893415351116794967938027330,
    -184243625712894544455851096642628656592418611328500,
    -218467831349985855104111542190048459574216853272000,
    -104362358336280153677902662034996499619630356520000]
def bezoutV : List Int :=
  [982411778890759707450816879740663917697946733895,
    10414963072204618701572354620142212610574617615900,
    42459808747741781887414794630525701889003007167870,
    82646133416630068056240142232746904284267413842460,
    77132033416934035920930180874004030553848684460840,
    27591209715573861493278393683580604236878962193400,
    -171815741667741489776094116816045921982554200800,
    135535530306857342438834626019475973531987476000]
def bezoutConst : Int := 222052931916878338314879387469107278019730653311

theorem fullIntegerBezout :
    let u := product bezoutU R1
    let v := product bezoutV R2
    (List.range (max u.length v.length)).map
      (fun i => term u i+term v i) = bezoutConst::List.replicate 13 0 := by
  decide

theorem smallBezout37 :
    let u := product [2,14,-11,16,3,6] R1
    let v := product [9,-9,3,16,18,-13,10,-15] R2
    (List.range (max u.length v.length)).map
      (fun i => (term u i+term v i)%37) = 1::List.replicate 13 0 := by
  decide

def scaledMixed (p q : Int) : Int :=
  let left := [0,0,0,20*p^2,-30*p,12]
  let right := product (product [1,-1] [1,-1]) (product [-q,1] [-q,1])
  (product left right).zipIdx.foldl (fun s (g,j) => s+g*(2520/(j+1):Int)) 0
def mixedInt (p q : Int) : Int :=
  70*p^2*q^2-80*p^2*q+25*p^2-60*p*q^2+75*p*q-25*p+
    15*q^2-20*q+7

/-- P and q each have degree at most two in this coefficient calculation. -/
theorem mixedIntegralGrid : ∀ i j : Fin 3,
    let p := Int.ofNat i.val
    let q := Int.ofNat j.val
    scaledMixed p q=12*mixedInt p q := by decide

def centeredMoment (m h : Int) (j : Nat) : Int :=
  let P := product [m^2-h^2,-2*m,1] [4*m^2-(2*h+1)^2,-4*m,1]
  P.zipIdx.foldl (fun s (v,k) =>
    s+if (j+k)%2=0 then v*(315/((j+k+1)*(j+k+3)):Nat) else 0) 0
def momentModels (m h : Int) : List Int :=
  let k := m^2-h^2
  [12*(35*k^2-35*k*h+14*k+14*h^2-7*h-1),
    12*m*(-21*k+14*h-1),
    4*(21*k^2-21*k*h+24*k+18*h^2-9*h-1),
    12*m*(-9*k+6*h-1)]

/-- Both m and h have degree at most four. -/
theorem centeredMomentGrid : ∀ i j : Fin 5, ∀ r : Fin 4,
    let m := Int.ofNat i.val
    let h := Int.ofNat j.val
    centeredMoment m h r.val=term (momentModels m h) r.val := by decide

def uExact (h : K) : K :=
  (-1543973141177890764191721622763177350803671359566+h*(-17239189689527380257421358471311515661047699876640+h*(-78887136983743048529126893415351116794967938027330+h*(-184243625712894544455851096642628656592418611328500+h*(-218467831349985855104111542190048459574216853272000+h*-104362358336280153677902662034996499619630356520000)))))
def vExact (h : K) : K :=
  (982411778890759707450816879740663917697946733895+h*(10414963072204618701572354620142212610574617615900+h*(42459808747741781887414794630525701889003007167870+h*(82646133416630068056240142232746904284267413842460+h*(77132033416934035920930180874004030553848684460840+h*(27591209715573861493278393683580604236878962193400+h*(-171815741667741489776094116816045921982554200800+h*135535530306857342438834626019475973531987476000)))))))

theorem genericBezout (h : K) :
    uExact h*r1 h+vExact h*r2 h=222052931916878338314879387469107278019730653311 := by
  unfold uExact vExact r1 r2
  grind

section FinalScalar
variable [IsCharP K 0]

theorem sameClockImpossible (u : K) (hull : hullSame u=0) (seam : mixed (1+u) u=0) :
    False := by
  have hy := mixAtSame u
  have hz := sameBezout u
  grind

theorem differentClockImpossible (m h v : K)
    (moment0 : 12*m*b (m^2-h^2) h=v*(12*a (m^2-h^2) h))
    (moment1 : 4*c (m^2-h^2) h=v*(12*m*b (m^2-h^2) h))
    (moment2 : 12*m*d (m^2-h^2) h=v*(4*c (m^2-h^2) h))
    (seam : mixed (1+m+h) (m-h)=0) : False := by
  have hz := mixActivated m h
  by_cases hm : m=0
  · subst m
    have hsub := zeroSubstitution h
    have hz0 : cZero h=0 ∧ mixZero h=0 := by grind
    have hbad := zeroBezout h
    grind
  · let k := m^2-h^2
    have hk0 : k+h^2=m^2 := by grind
    have heq : quad k h=0 := by grind
    have hmin1 : a k h*c k h-3*(k+h^2)*(b k h)^2=0 := by
      have ma : m*b k h=v*a k h := by grind
      have mc : c k h=3*v*m*b k h := by grind
      grind
    have hmin2 : 3*a k h*d k h-b k h*c k h=0 := by
      have ma : m*b k h=v*a k h := by grind
      have md : 3*m*d k h=v*c k h := by grind
      have der : m*(3*a k h*d k h-b k h*c k h)=0 := by grind
      grind
    have ha := firstMinorRemainder k h
    have hb := secondMinorRemainder k h
    have ha0 : a1 h*k+a0 h=0 := by grind
    have hb0 : b1 h*k+b0 h=0 := by grind
    have haN := linearNorm k h (a1 h) (a0 h)
    have hbN := linearNorm k h (b1 h) (b0 h)
    have hA := firstNorm h
    have hB := secondNorm h
    have bad := genericBezout h
    grind

end FinalScalar

/-- Cleared scalar seam: two supported quadrature reads force the second
    contact from the first. No sign assumption occurs. -/

theorem twoReadContact (a b ft fz rt rz beta : K)
    (bLive : b ≠ 0)
    (moment : a*ft+b*fz=0)
    (pair : a*rt=-b*rz)
    (firstContact : ft+4*beta*rt=0) :
    fz+4*beta*rz=0 := by
  have key : b*(fz+4*beta*rz)=0 := by grind
  grind

section PhysicalCut
variable {R : Type}
def zeroBefore (z : R) (x : Fin 14 → R) (n : Nat) : Prop :=
  ∀ i : Fin 14, i.val<n → x i=z
def zeroFrom (z : R) (x : Fin 14 → R) (n : Nat) : Prop :=
  ∀ i : Fin 14, n≤i.val → x i=z

/-- The boundary proof works for any two strict advancement operators.
The stages here are indexed starting at zero: physical row 7 has index 6. -/
theorem noCrossover (o : R) (A Astar : (Fin 14 → R) → Fin 14 → R)
    (leftAdvance : ∀ x n, zeroBefore o x n → zeroBefore o (A x) (n+1))
    (rightAdvance : ∀ x n, zeroFrom o x (n+1) → zeroFrom o (Astar x) n)
    (x y : Fin 14 → R)
    (leftStart : zeroBefore o x 5) (rightStart : zeroFrom o y 9)
    (contact : A x (6 : Fin 14)=o) :
    ∀ i, A (A x) i=o ∨ Astar y i=o := by
  have left6 := leftAdvance x 5 leftStart
  have left7 : zeroBefore o (A x) 7 := by
    intro i hi
    by_cases hv : i.val<6
    · exact left6 i hv
    · have hi6 : i=(6 : Fin 14) := Fin.ext (by omega)
      rw [hi6]
      exact contact
  have left8 := leftAdvance (A x) 7 left7
  have right8 := rightAdvance y 8 rightStart
  intro i
  by_cases hi : i.val<8
  · exact Or.inl (left8 i hi)
  · exact Or.inr (right8 i (by omega))
end PhysicalCut

end RKResearch.ERK10FivePairThreeCrossGate
#print axioms RKResearch.ERK10FivePairThreeCrossGate.mixAtSame
#print axioms RKResearch.ERK10FivePairThreeCrossGate.sameBezout
#print axioms RKResearch.ERK10FivePairThreeCrossGate.mixActivated
#print axioms RKResearch.ERK10FivePairThreeCrossGate.zeroSubstitution
#print axioms RKResearch.ERK10FivePairThreeCrossGate.zeroBezout
#print axioms RKResearch.ERK10FivePairThreeCrossGate.firstMinorRemainder
#print axioms RKResearch.ERK10FivePairThreeCrossGate.secondMinorRemainder
#print axioms RKResearch.ERK10FivePairThreeCrossGate.linearNorm
#print axioms RKResearch.ERK10FivePairThreeCrossGate.firstNorm
#print axioms RKResearch.ERK10FivePairThreeCrossGate.secondNorm
#print axioms RKResearch.ERK10FivePairThreeCrossGate.fullIntegerBezout
#print axioms RKResearch.ERK10FivePairThreeCrossGate.smallBezout37
#print axioms RKResearch.ERK10FivePairThreeCrossGate.mixedIntegralGrid
#print axioms RKResearch.ERK10FivePairThreeCrossGate.centeredMomentGrid
#print axioms RKResearch.ERK10FivePairThreeCrossGate.genericBezout
#print axioms RKResearch.ERK10FivePairThreeCrossGate.sameClockImpossible
#print axioms RKResearch.ERK10FivePairThreeCrossGate.differentClockImpossible
#print axioms RKResearch.ERK10FivePairThreeCrossGate.twoReadContact
#print axioms RKResearch.ERK10FivePairThreeCrossGate.noCrossover
