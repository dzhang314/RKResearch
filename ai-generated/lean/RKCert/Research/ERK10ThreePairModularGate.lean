import Lean

/-! Closed prime-59 certificates for the three clock-pair seam.
All elimination samples and local inverse rows are checked directly. -/
namespace RKResearch.ERK10ThreePairModularGate

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def red (x : Int) : Int := x % 59
def inv (x : Int) : Int := red ((red x)^57)
def term (a : List Int) (i : Nat) : Int := a[i]?.getD 0

def product (a b : List Int) : List Int :=
  (List.range (a.length+b.length-1)).map (fun k =>
    red ((List.range (k+1)).foldl (fun s i => s+term a i*term b (k-i)) 0))
def mix (a b : Int) (u v : List Int) : List Int :=
  (List.range (max u.length v.length)).map (fun i => red (a*term u i+b*term v i))
def monic (c : Int) : List Int := [-c,1]
def shift (a : List Int) : List Int := 0::a

def form (a b : List Int) : Int :=
  red (a.zipIdx.foldl (fun s (x,i) =>
    b.zipIdx.foldl (fun t (y,j) =>
      t+x*y*inv (Int.ofNat ((i+1)*(i+j+2)))) s) 0)

def det3 (a b c d e f g h i : Int) : Int :=
  red (a*(e*i-f*h)-b*(d*i-f*g)+c*(d*h-e*g))

def boundary (ul ur D L0 L1 Q0 Q1 : List Int)
    (u v a b : Int) : Int × Int :=
  let P := mix a b L0 L1
  let Q := mix a b Q0 Q1
  let dr := form P D
  let dl := form D Q
  let a0 := red (dr*form ul Q)
  let a1 := red (dr*form (shift ul) Q)
  let a2 := red (dr*form (shift (shift ul)) Q)
  let b0 := red (dl*form P ur)
  let b1 := red (dl*form P (shift ur))
  let l1 := red ((b1-a1-(u-v-1)*a0)*inv ((u-1)*(u-v)))
  let l2 := red (a0+u*l1)
  let l3 := red (a1+u*l2)
  let l4 := red (a2+u*l3)
  let l0 := red ((b0+(v+1)*l1-l2)*inv v)
  let j1 := red (u^2*inv 2)
  let j2 := red (u^3*inv 3)
  let j3 := red (u^4*inv 4)
  let k0 := 1-v
  let k1 := red ((1-v^2)*inv 2)-k0
  let k2 := red ((1-v^3)*inv 3)-k0
  let k3 := red ((1-v^4)*inv 4)-k0
  (det3 l1 l2 l3 l2 l3 l4 j1 j2 j3,
   det3 (l1-l0) (l2-l0) (l3-l0) (l2-l1) (l3-l1) (l4-l1) k1 k2 k3)

def interpolation : List (List Int) := [[1, 0, 0, 0, 0], [52, 4, 56, 21, 44], [58, 35, 49, 37, 57], [34, 31, 57, 11, 44], [32, 49, 15, 49, 32]]

def interpolate (xs : List Int) : List Int :=
  interpolation.map (fun row => red ((row.zip xs).foldl
    (fun u (x,y) => u+x*y) 0))

theorem interpolationCertificate : ∀ i j : Fin 5,
    red ((List.range 5).foldl (fun acc k =>
      acc + (Int.ofNat i.val)^k*(term (interpolation[k]?.getD []) j.val)) 0) =
      (if i=j then 1 else 0) := by decide

def verifies (u w y v : Int) (a b : List Int) : Bool :=
  let ul := product (monic 0) (monic u)
  let ur := product (monic 1) (monic v)
  let D := product ul ur
  let L0 := product ul (monic w)
  let L1 := shift L0
  let R0 := product ur (monic y)
  let R1 := shift R0
  let k00 := form L0 R0
  let k01 := form L0 R1
  let k10 := form L1 R0
  let k11 := form L1 R1
  let Q0 := mix (-k01) k00 R0 R1
  let Q1 := mix (-k11) k10 R0 R1
  let kd := red (k00*k11-k01*k10)
  let dd := red (form L0 D*form D Q1-form L1 D*form D Q0)
  let (fi,gi) := boundary ul ur D L0 L1 Q0 Q1 u v 0 1
  let vals := (List.range 5).map (fun t => boundary ul ur D L0 L1 Q0 Q1 u v 1 (Int.ofNat t))
  let f := interpolate (vals.map Prod.fst)
  let g := interpolate (vals.map Prod.snd)
  let out := mix 1 1 (product a f) (product b g)
  decide (a.length=4 ∧ b.length=4 ∧ red v ≠ 0 ∧ red ((u-1)*(u-v)) ≠ 0 ∧
    kd ≠ 0 ∧ dd ≠ 0 ∧ (fi ≠ 0 ∨ gi ≠ 0) ∧ out=[1,0,0,0,0,0,0,0])

def lobatto (x : Int) : Int := 42*x^4-84*x^3+56*x^2-14*x+1

theorem splitResidues :
    red (lobatto 14)=0 ∧ red (lobatto 23)=0 ∧
    red (lobatto 37)=0 ∧ red (lobatto 46)=0 := by decide
theorem perm1234 : verifies 14 23 37 46 [7, 29, 37, 53] [35, 45, 36, 27] = true := by decide
theorem perm1243 : verifies 14 23 46 37 [10, 43, 10, 28] [9, 41, 52, 15] = true := by decide
theorem perm1324 : verifies 14 37 23 46 [17, 6, 40, 2] [7, 41, 57, 19] = true := by decide
theorem perm1342 : verifies 14 37 46 23 [31, 25, 48, 16] [1, 4, 45, 52] = true := by decide
theorem perm1423 : verifies 14 46 23 37 [51, 13, 48, 24] [44, 37, 36, 25] = true := by decide
theorem perm1432 : verifies 14 46 37 23 [57, 37, 24, 9] [18, 55, 8, 0] = true := by decide
theorem perm2134 : verifies 23 14 37 46 [40, 39, 33, 4] [8, 49, 4, 31] = true := by decide
theorem perm2143 : verifies 23 14 46 37 [31, 45, 55, 44] [35, 40, 21, 19] = true := by decide
theorem perm2314 : verifies 23 37 14 46 [54, 19, 7, 2] [13, 47, 26, 31] = true := by decide
theorem perm2341 : verifies 23 37 46 14 [37, 17, 58, 23] [32, 9, 26, 21] = true := by decide
theorem perm2413 : verifies 23 46 14 37 [12, 19, 23, 26] [24, 0, 1, 42] = true := by decide
theorem perm2431 : verifies 23 46 37 14 [9, 8, 7, 24] [5, 17, 47, 34] = true := by decide
theorem perm3124 : verifies 37 14 23 46 [16, 29, 46, 29] [39, 25, 55, 19] = true := by decide
theorem perm3142 : verifies 37 14 46 23 [18, 48, 1, 38] [47, 23, 53, 8] = true := by decide
theorem perm3214 : verifies 37 23 14 46 [31, 53, 8, 12] [52, 0, 27, 45] = true := by decide
theorem perm3241 : verifies 37 23 46 14 [51, 31, 1, 56] [4, 15, 3, 56] = true := by decide
theorem perm3412 : verifies 37 46 14 23 [4, 56, 9, 6] [39, 10, 8, 45] = true := by decide
theorem perm3421 : verifies 37 46 23 14 [32, 48, 58, 1] [7, 51, 14, 8] = true := by decide
theorem perm4123 : verifies 46 14 23 37 [23, 25, 12, 50] [6, 19, 1, 13] = true := by decide
theorem perm4132 : verifies 46 14 37 23 [2, 14, 23, 5] [54, 39, 43, 0] = true := by decide
theorem perm4213 : verifies 46 23 14 37 [53, 38, 33, 36] [36, 5, 32, 21] = true := by decide
theorem perm4231 : verifies 46 23 37 14 [26, 33, 51, 24] [15, 46, 1, 39] = true := by decide
theorem perm4312 : verifies 46 37 14 23 [51, 9, 0, 54] [49, 16, 41, 58] = true := by decide
theorem perm4321 : verifies 46 37 23 14 [33, 43, 49, 18] [11, 45, 42, 19] = true := by decide

end RKResearch.ERK10ThreePairModularGate
#print axioms RKResearch.ERK10ThreePairModularGate.interpolationCertificate
#print axioms RKResearch.ERK10ThreePairModularGate.splitResidues
#print axioms RKResearch.ERK10ThreePairModularGate.perm1234
#print axioms RKResearch.ERK10ThreePairModularGate.perm1243
#print axioms RKResearch.ERK10ThreePairModularGate.perm1324
#print axioms RKResearch.ERK10ThreePairModularGate.perm1342
#print axioms RKResearch.ERK10ThreePairModularGate.perm1423
#print axioms RKResearch.ERK10ThreePairModularGate.perm1432
#print axioms RKResearch.ERK10ThreePairModularGate.perm2134
#print axioms RKResearch.ERK10ThreePairModularGate.perm2143
#print axioms RKResearch.ERK10ThreePairModularGate.perm2314
#print axioms RKResearch.ERK10ThreePairModularGate.perm2341
#print axioms RKResearch.ERK10ThreePairModularGate.perm2413
#print axioms RKResearch.ERK10ThreePairModularGate.perm2431
#print axioms RKResearch.ERK10ThreePairModularGate.perm3124
#print axioms RKResearch.ERK10ThreePairModularGate.perm3142
#print axioms RKResearch.ERK10ThreePairModularGate.perm3214
#print axioms RKResearch.ERK10ThreePairModularGate.perm3241
#print axioms RKResearch.ERK10ThreePairModularGate.perm3412
#print axioms RKResearch.ERK10ThreePairModularGate.perm3421
#print axioms RKResearch.ERK10ThreePairModularGate.perm4123
#print axioms RKResearch.ERK10ThreePairModularGate.perm4132
#print axioms RKResearch.ERK10ThreePairModularGate.perm4213
#print axioms RKResearch.ERK10ThreePairModularGate.perm4231
#print axioms RKResearch.ERK10ThreePairModularGate.perm4312
#print axioms RKResearch.ERK10ThreePairModularGate.perm4321
