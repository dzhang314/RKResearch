#!/usr/bin/env python3
"""Generate a literal CRT kernel packet, not a Hensel theorem."""
from fractions import Fraction as Q
from math import gcd
from pathlib import Path
import json, sys

class E:
    p=0
    m=0
    def __init__(self,z):
        if isinstance(z,E): self.v=z.v
        else:
            a=Q(z);self.v=a.numerator*pow(a.denominator,-1,self.m)%self.m
    def __eq__(self,z):return self.v==E(z).v
    def __bool__(self):return bool(self.v%self.p)
    def __add__(self,z):return E(self.v+E(z).v)
    __radd__=__add__
    def __neg__(self):return E(-self.v)
    def __sub__(self,z):return self+-E(z)
    def __rsub__(self,z):return E(z)+-self
    def __mul__(self,z):return E(self.v*E(z).v)
    __rmul__=__mul__
    def __pow__(self,k):return E(pow(self.v,k,self.m))
    def __truediv__(self,z):return self*E(z)**-1
    def __rtruediv__(self,z):return E(z)*self**-1

def dot(a,b):return sum((u*v for u,v in zip(a,b)),E(0))
def combo(v, gs, pivots):
    n=len(gs)
    M=[[g[k] for g in gs]+[v[k]] for k in pivots[:n]]
    for i in range(n):
        j=next(j for j in range(i,n) if M[j][i])
        M[i],M[j]=M[j],M[i]
        pivot=M[i][i]
        M[i]=[y/pivot for y in M[i]]
        for j in range(n):
            if i!=j:
                pivot=M[j][i]
                M[j]=[y-pivot*z for y,z in zip(M[j],M[i])]
    coeff=[r[-1] for r in M]
    assert all(v[k]==dot(coeff,[g[k] for g in gs]) for k in range(15))
    return coeff+[E(0)]*(3-n)

def packet(lit,K,e):
    from construct import construct,ev,support
    E.p=lit['p'];E.m=E.p**e
    def lift(cs,seed):
        ds=[i*E(s) for i,s in enumerate(cs) if i]
        r=E(seed)
        assert ev(ds,r)
        for _ in range((e-1).bit_length()):r-=ev(cs,r)/ev(ds,r)
        assert ev(cs,r)==0 and r.v%E.p==seed
        return r
    a=E(Q(1,2));x=lift(K['x'],lit['x'])
    def ex(xs):return ev([Q(*q) for q in xs],x)
    y,t=ex(K['y']),ex(K['t'])
    assert (a.v%E.p,y.v%E.p,t.v%E.p)==(lit['a'],lit['y'],lit['t'])
    f=lift([ex(r) for r in K['f']],lit['f'])
    _,s,p,_=support(a,x,y,t,f)
    d=lift([p,-s,E(1)],lit['d'])
    A,b,c=construct(a,x,y,t,f,d,E)
    assert [[z.v%E.p for z in r] for r in A]==lit['A']
    assert [v.v%E.p for v in b]==lit['b'] and [v.v%E.p for v in c]==lit['c']
    assert all(b[i]==0 for i in range(1,5))
    assert A[0][0]==0 and A[1][1]
    assert all(sum(r)==v and all(w==0 for w in r[i+1:]) for i,(r,v) in enumerate(zip(A,c)))
    N=list(zip(*A))
    y=[1-z for z in c]
    def sd(k,u,v):return [k*x-z for x,z in zip(u,v)]
    def times(u,v):return [x*y for x,y in zip(u,v)]
    def act(M,u):return [dot(r,u) for r in M]
    X=[[z**i for z in c] for i in range(13)]
    W=[times(b,[z**j for z in y]) for j in range(6)]
    FB=[sd(j+1,act(A,X[j]),X[j+1]) for j in range(6)]
    BB=[sd(j+1,act(N,W[j]),W[j+1]) for j in range(5)]
    G=[FB[2],times(c,FB[2]),times(X[2],FB[2])]
    h=sd(1,act(N,BB[2]),[(d/2)*x for x in BB[2]])
    H=[BB[2],h,times(y,h)]
    C=[[] for _ in range(6)]
    for k in range(5):
        m=max(0,k-2);mp=max(0,k-1)
        arrays=([act(A,z) for z in G[:m]],[times(c,z) for z in G[:m]],[FB[k]],
                [act(N,z) for z in H[:m]],[times(y,z) for z in H[:m]],[BB[k]])
        for i,arr in enumerate(arrays):
            gens,pivs=(G,[1,2,3]) if i<3 else (H,[13,12,10])
            vals=[combo(v,gens[:mp],pivs) for v in arr]
            C[i].append(vals+[[E(0)]*3]*(3-len(vals)))
    for k in range(3,6):
        assert all(dot(h,x)==0 for h in H[:k-2] for x in X[:12-k])
    assert all(all(h[i]==0 for i in range(1,5)) for h in H)
    assert all(all(g[i]==0 for i in (0,*range(5,15))) for g in G)
    for u in [FB[5]]+[act(A,z) for z in G]:
        assert all(dot(u,v)==0 for v in H+W)
    assert all((i+1)*dot(b,u)==1 for i,u in enumerate(X[:12]))
    delta=13*dot(b,X[12])-1
    assert delta and delta.v%E.p==lit['defect']
    vals=[A,b,c,G,H,C,delta**-1,A[1][1]**-1,[E(j)**-1 for j in range(1,6)],delta]
    def num(v):return v.v if isinstance(v,E) else list(map(num,v))
    print(f'prime={E.p} exponent={e}: generators {(x.v,f.v,d.v)}, next-star={delta.v}')
    return list(map(num,vals))

def joined(u,v,m,n):
    if isinstance(u,list):
        assert isinstance(v,list) and len(u)==len(v)
        return [joined(x,y,m,n) for x,y in zip(u,v)]
    r=u+m*((v-u)*pow(m,-1,n)%n)
    assert 0<=r<m*n and r%m==u and r%n==v
    return r

def lean(v):
    return '#['+','.join(map(lean,v))+']' if isinstance(v,list) else str(v)

def main(research,out,e):
    sys.path.insert(0,str(research/'dirk12-fifteen-midpoint-real-upper'))
    F=json.loads((research/'dirk12-fifteen-rank3-invisible-midpoint-zero-fourth-projection'/'field.json').read_text())
    d=research/'dirk12-fifteen-midpoint-prime-fields'
    U,V=[json.loads((d/name).read_text()) for name in
        ('witness-131-111-57-85.json','witness-149-103-41-106.json')]
    m,n=U['p']**e,V['p']**e
    assert gcd(m,n)==1 and e>0
    C=joined(packet(U,F,e),packet(V,F,e),m,n)
    with out.open('w') as h:
        print('''module

public import RKCert.ReviewedNative.DualSupport12VectorReplay
public import Mathlib.Data.ZMod.Basic

@[expose] public section

/-! Generated by generate-crt.py from the exact two prime literals. -/
namespace RKResearch.Certified.DIRK12MidpointPrimeCRT
open DualSupport12VectorReplay
''',file=h)
        print(f'abbrev exponent : Nat := {e}\nabbrev M : Nat := (131*149)^exponent\nabbrev K := ZMod M',file=h)
        for key,T,v in zip(
                ('aData','bData','cData','gData','hData','coefData','starInv','diagInv','smallInv','starNum'),
                ('Array (Array Nat)','Array Nat','Array Nat','Array (Array Nat)','Array (Array Nat)',
                 'Array (Array (Array (Array Nat)))','Nat','Nat','Array Nat','Nat'),C):
            print(f'def {key} : {T} :=',lean(v),file=h)
        print('''
def packet : Packet K where
  a := fun i j => ((aData[i.val]!)[j.val]! : Nat)
  b := fun i => (bData[i.val]! : Nat)
  c := fun i => (cData[i.val]! : Nat)
  genF := fun j i => ((gData[j]!)[i.val]! : Nat)
  genB := fun j i => ((hData[j]!)[i.val]! : Nat)
  coeff := fun o d i j => ((((coefData[o]!)[d]!)[i]!)[j]! : Nat)
  starInverse := (starInv : Nat)
  diagInverse := (diagInv : Nat)

end RKResearch.Certified.DIRK12MidpointPrimeCRT''',file=h)

if __name__=='__main__':
    main(Path(sys.argv[1]),Path(sys.argv[2]),int(sys.argv[3]))
