#!/usr/bin/env python3
"""Generate a content-factored integer Gram certificate over 25 coordinates."""
from argparse import ArgumentParser
from fractions import Fraction as F
from math import gcd, lcm
from pathlib import Path
import json

HERE=Path(__file__).resolve().parent
NAME="ERK12UniversalTwentyFour"
NS="RKResearch.Certified."+NAME
PREFIX="RKCert.ReviewedNative."
W=25
P=12

def arr(v):return "#["+", ".join(map(str,v))+"]"
def ar2(a):return "#[\n  "+",\n  ".join(map(arr,a))+"\n]"
def product(A,B):
    BT=list(zip(*B,strict=True))
    return [[sum(x*y for x,y in zip(a,b,strict=True) if x and y)for b in BT]for a in A]
def factor(A):
    g=gcd(*(e for r in A for e in r))
    assert g
    return [[a//g for a in r]for r in A],g

def write(p,name,im,data,extra=()):
    imports=[*(f"public import {PREFIX}{i}"for i in im),*extra]
    (p/(name+".lean")).write_text(
        "module\n\n"+"\n".join(imports)+"\n\n@[expose] public section\n\n"+
        "/-! Generated content-factored exact integer Gram certificate. -/\n\n"+
        "namespace "+NS+"\nopen RootedTreeGram\nopen scoped Matrix FiniteRootedTree\n"+
        "set_option maxHeartbeats 0\nset_option maxRecDepth 40000\nset_option Elab.async false\n\n"+
        data+"\n\nend "+NS+"\n"
    )

def calc(A,w,D):
    B=[r+[0]for r in A]+[[0]*24+[D]]
    BT=list(zip(*B,strict=True))
    C=[[[1]*W for _ in range(W)]]
    L,R=[],[]
    cs,ls,rs=[1],[],[]
    common,lhs,coeff=[],[],[]
    for n in range(P-1):
        u,g=factor(product(B,C[n]))
        v,h=factor(product(u,BT))
        L.append(u);ls.append(g)
        R.append(v);rs.append(h)
        scales=[cs[i]*cs[n-i]*ls[n-i]*rs[n-i]for i in range(n+1)]
        c=gcd(*scales)
        a=[l//c for l in scales]
        C1=[[0]*W for _ in range(W)]
        for i,u in enumerate(a):
            k=n-i+1
            f=[k]*24+[1]
            X,Y=C[i],R[n-i]
            for j in range(W):
                for l in range(W):
                    C1[j][l]+=u*X[j][l]*f[j]*f[l]*Y[j][l]
        V,h=factor(C1)
        C.append(V);cs.append(c*h)
        common.append(c);lhs.append(h);coeff.append(a)
    for n,V in enumerate(C,1):
        f=[n*b for b in w]+[-D]
        assert sum(a*x*b for a,r in zip(f,V)for x,b in zip(r,f))==0
    return C,L,R,cs,ls,rs,common,lhs,coeff,B

def data(p,A,w,D,C,L,R,cs,ls,rs,common,lhs,coeff,B):
    mat=lambda x,name:f"def arr{name} : Array (Array ℤ) := {ar2(x)}\ndef {name} : Cov 24 := fun i j => (arr{name}[i.val]!)[j.val]!"
    b=[sum(r)for r in A]
    cv=[sum(a*x**5 for a,x in zip(r,b))for r in A]
    body=f"""def D : ℤ := {D}
def aRows : Array (Array ℤ) := {ar2(A)}
def bVec : Array ℤ := {arr(w)}
def cVec : Array ℤ := {arr(b)}
def ac5Vec : Array ℤ := {arr(cv)}
def aSupport : Array (List ℕ) := {arr(str([j for j,x in enumerate(r)if x])for r in A)}
def lSupport : Array (List ℕ) := {arr(str([j for j,x in enumerate(r)if x])for r in B)}
def bSupport : List ℕ := {list(j for j,x in enumerate(w)if x)}
def M : Matrix (Fin 24) (Fin 24) ℤ :=
  fun i j => if j < i then (aRows[i.val]!)[j.val]! else 0
def w : Fin 24 → ℤ := fun i => bVec[i.val]!
def c : Fin 24 → ℤ := fun i => cVec[i.val]!
def ac5 : Fin 24 → ℤ := fun i => ac5Vec[i.val]!
"""
    write(p,NAME+"Data",[],body,(f"public import {PREFIX}RootedTreeGram",))
    mods=[]
    for n in range(P):
        mod=NAME+"Datum"+str(n)
        vals=[mat(C[n],f"cov{n}")]
        if n+1<P:vals.extend((mat(L[n],f"left{n}"),mat(R[n],f"right{n}")))
        write(p,mod,[NAME+"Data"],"\n\n".join(vals))
        mods.append(mod)
    body=[]
    for x,nm in ((C,"cov"),(L,"left"),(R,"right")):
        body.append(f"def {nm} : ℕ → Cov 24\n"+"\n".join(f"  | {i} => {nm}{i}"for i in range(len(x)))+"\n  | _ => 0")
    for x,nm in ((cs,"covScale"),(ls,"leftScale"),(rs,"rightScale"),(common,"common"),(lhs,"lhs")):
        body.append(f"def {nm} (n : ℕ) : ℤ := ({arr(x)} : Array ℤ)[n]!")
    body.append(f"def coeff (n i : ℕ) : ℤ := (({ar2(coeff)} : Array (Array ℤ))[n]!)[i]!")
    write(p,NAME+"DataAll",mods,"\n\n".join(body))
    return [NAME+"Data",*mods,NAME+"DataAll"]

def certs(p):
    mods=[]
    for n in range(P-1):
        for j,nm in enumerate(("Left","Right","Step")):
            lhs, rhs=(
              (f"fun i j => leftEntry cov{n} i j",f"leftScale {n} • left{n}")
              if j==0 else
              (f"fun i j => rightEntry left{n} i j",f"rightScale {n} • right{n}")
              if j==1 else
              (f"lhs {n} • cov{n+1}",f"factoredStep {n}")
            )
            body=[f"def check{nm}{n} (k : ℕ) : Bool := matrixBlock ({lhs}) ({rhs}) k"]
            base=NAME+"Check"+nm+str(n)
            for i in range(5):
                body.append(f"theorem {nm.lower()}{n}At{i} : check{nm}{n} {i} = true := by decide +kernel")
            imp=[NAME+"Core",NAME+"Datum"+str(n)]
            write(p,base,imp,"\n".join(body))
            mods.append(base)
    body=["theorem checkedBase : covScale 0 • cov 0 = outer 1 := by\n  apply extOfBlocks\n  decide +kernel"]
    for n in range(P):
        body.append(f"theorem energy{n} : energy (cov {n}) (output w D ({n}+1)) = 0 := by decide +kernel")
    mod=NAME+"CheckEnergy"
    write(p,mod,[NAME+"Core"],"\n\n".join(body))
    mods.append(mod)
    fields=[]
    for n in range(P-1):
        for nm,nname,statement,head in (
            ("Left","matrixLeft",f"branch M D 1 * cov {n} = leftScale {n} • left {n}",
                          "  rw [← leftEntry_matrix]\n"),
            ("Right","matrixRight",f"left {n} * (branch M D 1)ᵀ = rightScale {n} • right {n}",
                          "  rw [← rightEntry_matrix]\n"),
            ("Step","matrixStep",f"lhs {n} • cov ({n}+1) = factoredStep {n}",""),
        ):
            fields.append(f"theorem {nname}{n} : {statement} := by\n"+head+
             "  apply extOfBlocks\n  intro k\n  fin_cases k\n"+
             "\n".join(f"  · exact {nm.lower()}{n}At{i}"for i in range(5)))
    for f,n,typ in (
        ("left",11,"branch M D 1 * cov n.val = leftScale n.val • left n.val"),
        ("right",11,"left n.val * (branch M D 1)ᵀ = rightScale n.val • right n.val"),
        ("step",11,"lhs n.val • cov (n.val+1) = factoredStep n.val"),
        ("energy",12,"energy (cov n.val) (output w D (n.val+1)) = 0"),
    ):
        pr = f if f=="energy" else "matrix"+f.title()
        fields.append(f"theorem all_{f} (n : Fin {n}) : {typ} := by\n  fin_cases n\n"+
            "\n".join(f"  · exact {pr}{i}"for i in range(n)))
    fields+=["""theorem all_lhs (n : Fin 11) : covScale (n.val+1) = common n.val * lhs n.val := by
  revert n
  decide +kernel

theorem all_coeff (n : Fin 11) : ∀ i : Fin (n.val+1),
    covScale i.val * (covScale (n.val-i.val) * leftScale (n.val-i.val) * rightScale (n.val-i.val)) =
      common n.val * coeff n.val i.val := by
  revert n
  decide +kernel

def trace : FactoredTrace M D 12 where
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
  hleft n hn := all_left ⟨n, by omega⟩
  hright n hn := all_right ⟨n, by omega⟩
  hlhs n hn := all_lhs ⟨n, by omega⟩
  hcoeff n hn := all_coeff ⟨n, by omega⟩
  next n hn := all_step ⟨n, by omega⟩"""]
    mod=NAME+"Checks"
    write(p,mod,mods,"\n\n".join(fields),("import Mathlib.Tactic.FinCases",))
    return [*mods,mod]

def main():
    a=ArgumentParser()
    a.add_argument('--source',type=Path,default=HERE/'tableau.json')
    a.add_argument('--emit',required=True,type=Path)
    a.add_argument('--modules',required=True,type=Path)
    s=a.parse_args()
    obj=json.loads(s.source.read_text())
    A=[list(map(F,r))+[F(0)]*(24-len(r))for r in obj['A']]
    w=list(map(F,obj['b']))
    D=lcm(*(v.denominator for r in A for v in r),*(v.denominator for v in w))
    assert D==28868710429988352000000000000
    A=[[int(D*x)for x in r]for r in A];w=[int(D*x)for x in w]
    res=calc(A,w,D)
    mods=data(s.emit,A,w,D,*res)
    mods.append(NAME+"Core")
    mods+=certs(s.emit)
    mods.append(NAME)
    s.modules.write_text("\n".join(mods)+"\n")
    print("Finitely factored integer 25x25 covariance trace, grades 0–11.")
    print("Largest covariance entry:",max(len(str(abs(a)))for c in res[0]for r in c for a in r),"decimal digits.")
    print("All 12 integer output energies vanish.")

if __name__=='__main__':main()
