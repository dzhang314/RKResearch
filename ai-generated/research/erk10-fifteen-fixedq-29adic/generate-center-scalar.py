#!/usr/bin/env python3
"""Generate small linear-combination certificates for the normalized center rows.

Only the printed Lean statements and kernel proofs are trusted.
The SymPy derivation is fraction-free after multiplying by the stated guard.
"""
import argparse
import math
from pathlib import Path
import sympy as S

s,t,k,d,is_,it,id_,ir,i2,i3,i4=S.symbols('s t k d iS iT iD iR i2 i3 i4')
iv=[is_,it,id_,ir,i2,i3,i4]
de=[s,t,d,s-1,S.Integer(2),S.Integer(3),S.Integer(4)]
hNames=['hS','hT','hD','hR','h2','h3','h4']
d0=3*s*k-2*t*k+t
g=2*k*(t-2*s)-t
D=12*s*t*d*(s-1)
R=-2-4*k*(s-1)
L=(-2)*(2*s*t*k**2+2*s*t*k-2*s*k**2+s*k-2*t*k+t)*id_
B=s*k*(t-1)*(t-s)*id_*ir
A=k*(t-1)-B
P=2*t*i3+k*(4*s*i3-2)*(t-1)
Q=k*(t-1)+s*k*(t-1)*(t-s)*id_
RR=t**2*i2+k*(s**2-2)*(t-1)-s*k*(s*k-t*k-t+2)*(t-1)*(t-s)*id_
G=-2*(t-s)+(1-t)*R*is_+(s-1)*L*it
es=[
 ('read1','-2*A+R*iS*B','L*i2+1',-2*A+R*is_*B-L*i2-1),
 ('read2','-2*A+R*B','L*t*i3+P',-2*A+R*B-L*t*i3-P),
 ('read3','-2*A+s*R*B','L*t^2*i4+T',-2*A+s*R*B-L*t**2*i4-RR),
 ('readU','A+B','k*(t-1)',A+B-k*(t-1)),
 ('readYU','A+s*B','Q',A+s*B-Q),
 ('vary2','-2*(t-s)+(1-t)*R+(s-1)*L','2*t*i3*G',-2*(t-s)+(1-t)*R+(s-1)*L-2*t*i3*G),
 ('vary3','-2*(t-s)+(1-t)*s*R+(s-1)*t*L','t^2*i2*G',-2*(t-s)+(1-t)*s*R+(s-1)*t*L-t**2*i2*G),
]
def wrap(a):
    a=str(S.factor(a)).replace('**','^')
    return '('+a+')'

def make():
    out=['module','', 'public import Mathlib.Tactic.LinearCombination','', '@[expose] public section','','namespace RKResearch.Certified.ERK10CenterScalar','',
         '/-! Paid denominator-clearance for the first and second center donors. -/',
         'set_option maxHeartbeats 500000','','variable {U : Type*} [CommRing U]',
         'variable (s t k d iS iT iD iR i2 i3 i4 : U)','']
    definitions=[('gainB','-2-4*k*(s-1)','s k'),('gainC','(-2)*(2*s*t*k^2+2*s*t*k-2*s*k^2+s*k-2*t*k+t)*iD','s t k iD'),
        ('pickB','s*k*(t-1)*(t-s)*iD*iR','s t k iD iR'),('pickA','k*(t-1)-pickB s t k iD iR','t k s iD iR'),
        ('modelP','2*t*i3+k*(4*s*i3-2)*(t-1)','s t k i3'),
        ('modelQ','k*(t-1)+s*k*(t-1)*(t-s)*iD','s t k iD'),
        ('modelR','t^2*i2+k*(s^2-2)*(t-1)-s*k*(s*k-t*k-t+2)*(t-1)*(t-s)*iD','s t k iD i2'),
        ('nullGain','-2*(t-s)+(1-t)*gainB s k*iS+(s-1)*gainC s t k iD*iT','s t k iS iT iD')]
    # Explicit parameter order independent of local section inference.
    for name,body,args in definitions:
        if name=='pickA':args='s t k iD iR'
        out.append('def '+name+' ('+args+' : U) : U := '+body)
    out+=['','def clearDen (s t d : U) : U := 12*s*t*d*(s-1)','']
    hypotheses=['hS : s*iS=1','hT : t*iT=1','hD : d*iD=1','hR : (s-1)*iR=1',
                'h2 : 2*i2=1','h3 : 3*i3=1','h4 : 4*i4=1',
                'hdelta : d=3*s*k-2*t*k+t','hk : 2*k*(t-2*s)=t']
    replaces={'A':'pickA s t k iD iR','B':'pickB s t k iD iR','R':'gainB s k',
              'L':'gainC s t k iD','P':'modelP s t k i3','Q':'modelQ s t k iD',
              'T':'modelR s t k iD i2','G':'nullGain s t k iS iT iD'}
    import re
    for nm, lhs,rhs,E in es:
        co=[S.Integer(0) for _ in de]
        rest=S.Integer(0)
        for powers,v in S.Poly(S.expand(E),*iv).terms():
            f=D
            for inverse,den,n in zip(iv,de,powers):
                f/=den**n
            f=S.cancel(f*v)
            assert S.denom(f)==1
            rest+=f
            f1=f
            for j,n in enumerate(powers):
                for _ in range(n):
                    co[j]+=f1
                    f1=f1*de[j]*iv[j]
        qd,rem=S.div(S.expand(rest),d-d0,d)
        qk=S.cancel(rem/g) if rem!=0 else S.Integer(0)
        assert S.denom(qk)==1
        coeffs=co+[qd,qk]
        assert S.expand(D*E-sum(x*(a*b-1) for x,a,b in zip(co,de,iv))-qd*(d-d0)-qk*g)==0
        params=[h for x,h in zip(coeffs,hypotheses) if x!=0]
        names=hNames+['hdelta','hk']
        used=set()
        N=[]
        for x,h in zip(coeffs,names):
            if x!=0:
                N.append(wrap(x)+'*'+h)
                used|=x.free_symbols
        Lh=re.sub(r"\b[A-Z]\b",lambda m:'('+replaces[m[0]]+')',lhs)
        Rh=re.sub(r"\b[A-Z]\b",lambda m:'('+replaces[m[0]]+')',rhs)
        out+=['theorem '+nm+' '+ ' '.join('('+p+')' for p in params)+' :',
              '    clearDen s t d * (('+Lh+')-('+Rh+'))=0 := by',
              '  unfold clearDen '+ ' '.join(fn for fn in ('nullGain','pickA','pickB','gainB','gainC','modelP','modelQ','modelR') if fn in Lh+Rh or (fn=='pickB' and 'pickA' in Lh+Rh)
                  or (fn in ('gainB','gainC') and 'nullGain' in Lh+Rh))]
        if N:
            out+=['  linear_combination '+(' +\n    '.join(N))]
        else:
            out+=['  ring']
        out+=['']
    out+=['end RKResearch.Certified.ERK10CenterScalar',''] + [
          '#print axioms RKResearch.Certified.ERK10CenterScalar.'+nm for nm,*_ in es]+['']
    return '\n'.join(out)

def make_core():
    vars_=[s,t,k,d,*iv]
    code="""module

public import Init

@[expose] public section

namespace RKResearch.Certified.ERK10CenterCore

/-! Core-only arithmetic replay of the two exact normalized center rows.
All eleven variables, including the trial inverses, are formal. -/

set_option maxHeartbeats 0
set_option maxRecDepth 50000

abbrev Term := Nat × Int
structure P where
  xs : List Term
  degreeBound : Nat

def add (a b : P) : P := ⟨a.xs++b.xs,max a.degreeBound b.degreeBound⟩
def neg (a : P) : P := ⟨a.xs.map (fun t => (t.1,-t.2)),a.degreeBound⟩
def mul (a b : P) : P :=
  ⟨a.xs.flatMap (fun t => b.xs.map (fun u => (t.1+u.1,t.2*u.2))),
    a.degreeBound+b.degreeBound⟩

def con (z : Int) : P := ⟨(if z=0 then [] else [(0,z)]),0⟩
def v (i : Nat) : P := ⟨[(64^i,1)],1⟩
instance : Add P := ⟨add⟩
instance : Neg P := ⟨neg⟩
instance : Sub P := ⟨fun a b => a + -b⟩
instance : Mul P := ⟨mul⟩
instance (n : Nat) : OfNat P n := ⟨con (.ofNat n)⟩
def pow (a : P) : Nat → P
  | 0 => 1
  | n+1 => pow a n*a
instance : Pow P Nat := ⟨pow⟩

def packExp (es : List Nat) : Nat := es.foldr (fun a b => a+64*b) 0
def sparse (lhs : List (List Nat × Int)) : P :=
  ⟨lhs.map (fun b => (packExp b.1,b.2)),
    lhs.foldl (fun a b => max a (b.1.foldl Nat.add 0)) 0⟩

def merge : Nat → List Term → List Term → List Term
  | 0, a, b => a++b
  | _+1, [], b => b
  | _+1, a, [] => a
  | n+1, x::a, y::b =>
    if x.1≤y.1 then x::merge n a (y::b) else y::merge n (x::a) b

def mergePairs : List (List Term) → List (List Term)
  | a::b::xs => merge (a.length+b.length) a b::mergePairs xs
  | xs => xs

def sortRuns : Nat → List (List Term) → List Term
  | 0, xs => xs.flatten
  | _+1, [] => []
  | _+1, [a] => a
  | n+1, a::b::xs => sortRuns n (mergePairs (a::b::xs))

def zeroSorted (e : Nat) (a : Int) : List Term → Bool
  | [] => a == 0
  | (f,b)::xs =>
    if e=f then zeroSorted e (a+b) xs
    else (a == 0) && zeroSorted f b xs

/-- A total-degree bound below the radix prevents all exponent carries. -/
def zero (a : P) : Bool :=
  decide (a.degreeBound<64) &&
    (match sortRuns a.xs.length (a.xs.map fun t => [t]) with
     | [] => true
     | (e,b)::xs => zeroSorted e b xs)
"""
    out=[code]
    for j,vv in enumerate(vars_):
        out.append(f"def {vv} : P := v {j}")
    out.extend(["","def RA : P := -2-4*k*(s-1)",
        "def LC : P := (-2)*(2*s*t*k^2+2*s*t*k-2*s*k^2+s*k-2*t*k+t)*iD",
        "def BB : P := s*k*(t-1)*(t-s)*iD*iR",
        "def AA : P := k*(t-1)-BB",
        "def PP : P := 2*t*i3+k*(4*s*i3-2)*(t-1)",
        "def QQ : P := k*(t-1)+s*k*(t-1)*(t-s)*iD",
        "def TT : P := t^2*i2+k*(s^2-2)*(t-1)-s*k*(s*k-t*k-t+2)*(t-1)*(t-s)*iD",
        "def GG : P := -2*(t-s)+(1-t)*RA*iS+(s-1)*LC*iT",
        "def pay : P := 12*s*t*d*(s-1)",""])
    lookup={'A':'AA','B':'BB','R':'RA','L':'LC','P':'PP','Q':'QQ','T':'TT','G':'GG'}
    import re
    eqs=["s*iS-1","t*iT-1","d*iD-1","(s-1)*iR-1","2*i2-1","3*i3-1","4*i4-1",
         "d-(3*s*k-2*t*k+t)","2*k*(t-2*s)-t"]
    def coeff(x):
        terms=S.Poly(S.expand(x),*vars_).terms()
        return "sparse ["+','.join("("+str(list(ee))+","+str(int(a))+")" for ee,a in terms if a!=0)+"]"
    for nm,lhs,rhs,E in es:
        co=[S.Integer(0) for _ in de]; rest=S.Integer(0)
        for powers,vv in S.Poly(S.expand(E),*iv).terms():
            u=D
            for den,n in zip(de,powers): u/=den**n
            u=S.cancel(u*vv)
            assert S.denom(u)==1
            rest+=u; rr=u
            for j,n in enumerate(powers):
                for _ in range(n):
                    co[j]+=rr
                    rr=rr*de[j]*iv[j]
        qd,rem=S.div(S.expand(rest),d-d0,d)
        qk=S.cancel(rem/g) if rem!=0 else S.Integer(0)
        assert S.denom(qk)==1
        assert S.expand(D*E-sum(a*(b*c-1) for a,b,c in zip(co,de,iv))-qd*(d-d0)-qk*g)==0
        rco = [f"({coeff(a)} : P)*({b})" for a,b in zip(co+[qd,qk],eqs) if a!=0]
        lhs=re.sub(r"\b[A-Z]\b",lambda m:lookup[m[0]],lhs)
        rhs=re.sub(r"\b[A-Z]\b",lambda m:lookup[m[0]],rhs)
        out += [f"def relation_{nm} : P :=",f"  pay*(({lhs})-({rhs}))-({'+'.join(rco) or '0'})",
                f"theorem {nm}_exact : zero relation_{nm}=true := by decide +kernel",""]
    out+=["end RKResearch.Certified.ERK10CenterCore",""]
    out += ["#print axioms RKResearch.Certified.ERK10CenterCore."+nm+"_exact" for nm,*_ in es]
    return "\n".join(out)+"\n"

if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('out',type=Path);p.add_argument('--core',action='store_true');a=p.parse_args()
 a.out.write_text(make_core() if a.core else make())
