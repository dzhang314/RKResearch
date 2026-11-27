"""Generate the kernel-checked integer Gram certificate for the 13-stage DIRK.

Run in the ai-generated tree:
  python3 generate_lean.py path/to/tableau.json > /tmp/DIRK10RationalThirteenGram.lean
The existing Gram replay is a source generator, not trusted by the Lean proof.
"""
import sys, math, argparse
from pathlib import Path
from fractions import Fraction as Q
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "rooted-tree-gram"))
from check_gram import gram

def load(path):
    import json
    t = json.loads(Path(path).read_text())
    M = [list(map(Q, row)) for row in t["A"]]
    w = list(map(Q,t["b"]))
    s = len(M)
    assert (s, t["order"], t["stages"], len(w)) == (13,10,13,13)
    assert list(map(len,M)) == list(range(1,14))
    d = math.lcm(*(x.denominator for r in M for x in r), *(x.denominator for x in w))
    assert d == 126767366286331069785024000 and d**2 % 2488320 == 0
    N = [[int(d*x) for x in row]+[0]*(s-len(row)) for row in M]
    b = [int(d*x) for x in w]
    assert 2488320 * (11 * sum(w*sum(row)**10 for w,row in zip(b,N)) - d**11) == d**11
    return N,b,d,d,10
if hasattr(sys, 'set_int_max_str_digits'):
    sys.set_int_max_str_digits(0)

def arr(xs):
    return '#['+', '.join(map(str,xs))+']'
def ints_array(name, xs, is_matrix=False):
    if is_matrix:
        return f'def {name} : Array (Array ℤ) := #[\n  '+',\n  '.join(map(arr,xs))+'\n]\n'
    return f'def {name} : Array ℤ := '+arr(xs)+'\n'
def grade_fun(name, typ, vals, default='0'):
    return f'def {name} : Nat → {typ}\n'+''.join(f'  | {j} => {val}\n' for j,val in enumerate(vals))+f'  | _ => {default}\n'
def unpack_matrix(m, a, name):
    return f'def {name} : Matrix (Fin {m}) (Fin {m}) ℤ := fun i j => ({a}[i.val]!)[j.val]!\n'
def content(matrix):
    u=math.gcd(*(a for r in matrix for a in r)) or 1
    return u, [[a//u for a in r] for r in matrix]
def caseProof(header, names):
    return f'private theorem {header} := by\n  fin_cases n\n'+''.join(f'  · exact {name}\n' for name in names)

def generate(path, graded=False):
    M,w,d,e,p=load(path);s=len(M);m=s+1
    C,H,T=gram(M,w,d,e,p)
    a=[];b=[];c=[];cv=[];left=[];right=[]
    for g in range(p):
        v,x=content(C[g]);a.append(v);cv.append(x)
        if g+1<p:
            u,h=content(H[g]);z,t=content(T[g])
            assert u%v==0 and z%u==0
            b.append(u//v);c.append(z//u);left.append(h);right.append(t)
    common=[]; lhs=[]; coeff=[]
    for g in range(p-1):
        raw=[a[i]*a[g-i]*b[g-i]*c[g-i] for i in range(g+1)]
        scale=math.gcd(a[g+1],*raw);common.append(scale)
        lhs.append(a[g+1]//scale);coeff.append([v//scale for v in raw])
    print(f'''module

public import RKCert.ReviewedNative.RootedTreeGram
import Mathlib.Tactic.FinCases

@[expose] public section

/-! Generated from the literal rational DIRK tableau. The supplied
finite integer arithmetic is rechecked in the Lean kernel. -/

namespace RKResearch.Certified.DIRK10RationalThirteen
open RootedTreeGram
open scoped Matrix
set_option maxRecDepth 22000
set_option maxHeartbeats 0
set_option Elab.async false
''')
    print(ints_array('rawRows', M, True))
    print(ints_array('rawWeights',w))
    print(ints_array('rawClocks',[sum(row) for row in M]))
    print(f'''def D : ℤ := {d}
def M : Matrix (Fin {s}) (Fin {s}) ℤ :=
  fun i j => if i < j then 0 else (rawRows[i.val]!)[j.val]!
def w : Fin {s} → ℤ := fun i => rawWeights[i.val]!
def c : Fin {s} → ℤ := fun i => rawClocks[i.val]!
''')
    for prefix,k in [('cov',cv),('left',left),('right',right)]:
        for g,x in enumerate(k):
            print(ints_array(f'{prefix}Rows{g}',x,True))
            print(unpack_matrix(m,f'{prefix}Rows{g}',f'{prefix}{g}'))
        print(grade_fun(prefix,f'Cov {s}',[prefix+str(g) for g in range(len(k))]))

    for name,values in [('covScale',a),('leftScale',b),('rightScale',c),('common',common),('lhs',lhs)]:
        print(grade_fun(name,'ℤ',values))
    print(ints_array('coeffs', coeff,True))
    print('def coeff (n i : Nat) : ℤ := (coeffs[n]!)[i]!\n')
    print(f'''private theorem extOfCheck (X Y : Cov {s})
    (h : (List.finRange {m}).all (fun i => (List.finRange {m}).all (fun j => decide (X i j = Y i j))) = true) :
    X = Y := by
  ext i j
  have hi := List.all_eq_true.mp h _ (List.mem_finRange i)
  exact of_decide_eq_true (List.all_eq_true.mp hi j (List.mem_finRange j))

private theorem checkedBase : covScale 0 • cov 0 = outer 1 := by
  exact extOfCheck _ _ (by decide +kernel)
''')
    for g in range(p-1):
        print(f'''private theorem prodL{g} : branch M D 1 * cov {g} = leftScale {g} • left {g} := by
  exact extOfCheck _ _ (by decide +kernel)
private theorem prodR{g} : left {g} * (branch M D 1)ᵀ = rightScale {g} • right {g} := by
  exact extOfCheck _ _ (by decide +kernel)
private theorem hLhs{g} : covScale ({g}+1) = common {g} * lhs {g} := by decide +kernel
private theorem hCoeff{g} : ∀ i : Fin ({g}+1),
    covScale i.val * (covScale ({g}-i.val) * leftScale ({g}-i.val) * rightScale ({g}-i.val)) =
      common {g} * coeff {g} i.val := by decide +kernel
private theorem hNext{g} : lhs {g} • cov ({g}+1) =
    ((List.finRange ({g}+1)).map fun i => coeff {g} i.val •
      entryMul (cov i.val) (reweight ({g}-i.val+1) (right ({g}-i.val)))).sum := by
  exact extOfCheck _ _ (by decide +kernel)
''',flush=True)
        if graded:print(f'#check hNext{g}',flush=True)
    for g in range(p):
        print(f'private theorem hEnergy{g} : energy (cov {g}) (output w D ({g}+1)) = 0 := by decide +kernel')
    band=p-1
    print(caseProof(f'prodLAll (n : Fin {band}) : branch M D 1 * cov n.val = leftScale n.val • left n.val',
                   [f'prodL{g}' for g in range(band)]))
    print(caseProof(f'prodRAll (n : Fin {band}) : left n.val * (branch M D 1)ᵀ = rightScale n.val • right n.val',
                   [f'prodR{g}' for g in range(band)]))
    print(caseProof(f'hLhsAll (n : Fin {band}) : covScale (n.val+1) = common n.val * lhs n.val',
                   [f'hLhs{g}' for g in range(band)]))
    print(caseProof(f'''hCoeffAll (n : Fin {band}) : ∀ i : Fin (n.val+1),
    covScale i.val * (covScale (n.val-i.val) * leftScale (n.val-i.val) * rightScale (n.val-i.val)) =
      common n.val * coeff n.val i.val''',[f'hCoeff{g}' for g in range(band)]))
    print(caseProof(f'''hNextAll (n : Fin {band}) : lhs n.val • cov (n.val+1) =
    ((List.finRange (n.val+1)).map fun i => coeff n.val i.val •
      entryMul (cov i.val) (reweight (n.val-i.val+1) (right (n.val-i.val)))).sum''',
      [f'hNext{g}' for g in range(band)]))
    print(caseProof(f'hEnergyAll (n : Fin {p}) : energy (cov n.val) (output w D (n.val+1)) = 0',
                   [f'hEnergy{g}' for g in range(p)]))
    print(f'''private def trace : FactoredTrace M D {p} where
  cov := cov
  left := left
  right := right
  covScale := covScale
  leftScale := leftScale
  rightScale := rightScale
  common := common
  lhs := lhs
  coeff := coeff
  base := checkedBase
  hleft n hn := prodLAll ⟨n, by omega⟩
  hright n hn := prodRAll ⟨n, by omega⟩
  hlhs n hn := hLhsAll ⟨n, by omega⟩
  hcoeff n hn := hCoeffAll ⟨n, by omega⟩
  next n hn := hNextAll ⟨n, by omega⟩

theorem order_scaled {{R : Type*}} [CommRing R]
    (f : ℤ →+* R) (U : Matrix (Fin {s}) (Fin {s}) R) (b : Fin {s} → R)
    (hA : M.map f = f D • U) (hb : f ∘ w = f D • b) (hd : IsUnit (f D)) :
    HasOrder {p} U b :=
  trace.hasOrder (fun n hn => hEnergyAll ⟨n,hn⟩) f U b hA hb hd hd

end RKResearch.Certified.DIRK10RationalThirteen
'''.rstrip())

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('tableau')
    parser.add_argument('--graded',action='store_true')
    args=parser.parse_args()
    generate(args.tableau,args.graded)
