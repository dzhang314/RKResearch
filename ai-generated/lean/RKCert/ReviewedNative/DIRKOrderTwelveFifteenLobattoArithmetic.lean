import Init

namespace RKResearch.Certified.Graded.OrderTwelveFifteen.LobattoArithmetic

def L : List Int := [1,-42,420,-1680,3150,-2772,924]
def H : List Int := [0,-42,840,-5040,12600,-13860,5544]

def eval (f : List Int) (x : Int) : Int := f.foldr (fun a v => a+x*v) 0

def moment (f : List Int) (j : Nat) : Int :=
  (((List.range 7).map fun i => (f[i]?.getD 0)*Int.ofNat (27720/(i+j+1))).foldl (· + ·) 0)

theorem moment_identities :
    (List.range 6).map (moment L) = [0,0,0,0,0,0] ∧
    (List.range 6).map (moment H) = [27720,27720,27720,27720,27720,27720] ∧
    eval H 1 = 42 := by decide

def roots : List Nat := (List.range 43).filter (fun x => eval H (Int.ofNat x) % 43 == 0)

theorem split_basis :
    roots = [0,2,9,22,35,42] ∧ H.getLastD 0 % 43 ≠ 0 := by decide

def factors : List (Nat × Nat × Nat) :=
  roots.flatMap fun a => (roots.filter (fun b => a < b)).flatMap fun b =>
    (roots.filter (fun c => b < c)).map fun c => (a,b,c)

def coeff (q : Nat × Nat × Nat) : List Int :=
  let a := Int.ofNat q.1
  let b := Int.ofNat q.2.1
  let c := Int.ofNat q.2.2
  [-a*b*c,a*b+a*c+b*c,-(a+b+c),1]

def zeroMask (q : Nat × Nat × Nat) (u : Nat) : Bool :=
  u != 0 && u != q.1 && u != q.2.1 && u != q.2.2

def primitive2 (q : Nat × Nat × Nat) (u : Nat) : Int :=
  let f := coeff q
  ((List.range 4).map fun j => Int.ofNat (60/(j+3)) *
    (f[j]?.getD 0)*((Int.ofNat u)^(j+3))).foldl (· + ·) 0

def eliminated (q : Nat × Nat × Nat) (u : Nat) : Int :=
  let f := coeff q
  ((List.range 4).map fun j => -Int.ofNat (60/((j+2)*(j+3))) *
    (f[j]?.getD 0)*((Int.ofNat u)^(j+3))).foldl (· + ·) 0

def nonterminal : List ((Nat × Nat × Nat) × Nat) :=
  factors.flatMap (fun q => (roots.filter (zeroMask q)).map (fun u => (q,u)))

theorem nonterminal_receipts :
    nonterminal.length = 50 ∧
    nonterminal.all (fun (q,u) => eliminated q u % 43 != 0) = true := by decide

theorem terminal_receipts :
    factors.length = 20 ∧ factors.all (fun q => primitive2 q 1 % 43 != 0) = true ∧
    (factors.filter (fun q => eliminated q 1 % 43 == 0)).length = 2 := by decide

theorem all_pure_primitive_receipts :
    nonterminal.all (fun (q,u) => primitive2 q u % 43 != 0) = true := by decide

#print axioms moment_identities
#print axioms split_basis
#print axioms nonterminal_receipts
#print axioms terminal_receipts
#print axioms all_pure_primitive_receipts

end RKResearch.Certified.Graded.OrderTwelveFifteen.LobattoArithmetic
