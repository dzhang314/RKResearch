"""Exact nominal projections of the off-Q, regular scale chart."""
from pathlib import Path
import sys

RESEARCH=Path(__file__).resolve().parent.parent
sys.path.insert(0,str(RESEARCH/'sdirk-eight-all-dirty-seven-quadratic-both-s-both-two-s-disjoint-hl'))
from projection_hl import *
Zb=ip(b.n)
def cf(P,j=2):
    a=[{} for _ in range(P.degrees()[j]+1)]
    for ex,c in P.to_dict().items():
        ee=list(ex);ee[j]=0
        a[ex[j]][tuple(ee)]=c
    return list(map(CZ.from_dict,a))
def prem(P,G,var=2,extra=()):
    assert P and G
    comp=cf(G,var)
    d=len(comp)-1;C=comp[-1];z=ip((a if var==1 else b).n)
    while P and (e:=P.degrees()[var])>=d:
        co=cf(P,var)[e]
        P=C*P-z**(e-d)*co*G
        if P:
            assert P.degrees()[var]<e
            P=strip(P,extra)
    return P
def compatibility(gam):
    phi=N(a/2)/D(a/2)
    n=ip((a+b-2*H-H*(phi-1)*(H-b)/a).n)
    M=ip((a+b-2*H-H*(k(b)-1)*(H-a)/b).n)
    assert gam.degrees()==(4,8,2)
    Q,= [z for z,e in n.resultant(M,'b').factor()[1] if z.degrees()==(2,4,0)]
    return Q
def data(mode):
    eq,m=frame(mode,'regular');gam,E,G,Y=eq
    G0,=cf(gam)[-1:]
    q=compatibility(gam)
    base=[z for z in sum(m.values(),[]) if not z.degrees()[2]]
    pure=[z for z in base if not z.degrees()[1]]
    return eq,m,G0,q,base,pure
def cross_rows(mode):
    eq,m,g,q,base,pure=data(mode)
    gam,E,G,Y=eq
    guards=base+[g,q]
    W=[prem(z,gam,2,guards) for z in (E,G,Y)]
    rows=[cf(z) for z in W]
    print('reduced affine',[z.degrees() for z in W],flush=True)
    assert all(len(L)==2 for L in rows)
    X=[strip(x*v-y*u,guards) for ((x,y),(u,v)) in combinations(rows,2)]
    P=[]
    for r in X:
        f=r.factor()[1]
        print('minor',r.degrees(),[(z.degrees(),n) for z,n in f],flush=True)
        P.append(r)
    return P,eq,m,g,q,base,pure

def linear_drop(mode):
    eq,m,g0,q,base,pure=data(mode)
    gam,E,G,Y=eq
    c0,c1,c2=cf(gam)
    lin=c0+c1*Zb
    ep=[strip(lin.resultant(z,'b'),base+[q]) for z in (E,G,Y)]
    print('degree one remainder',[z.degrees() for z in ep],flush=True)
    out=[]
    for x in ep:
        r=strip(g0.resultant(x,'a'),pure)
        print('res',r.degrees(),flush=True)
        out.append(r)
    g=out[0].gcd(out[1]).gcd(out[2])
    print('linear-drop common factors',[(f.degrees(),e) for f,e in g.factor()[1]],flush=True)
    return g,(g0,*ep),eq,m,lin,q,base,pure
def residual_rows(mode):
    X,eq,m,c2,q,base,pure=cross_rows(mode)
    gam,E,G,Y=eq
    U=[strip(gam.resultant(z,'b'),base+[c2,q]) for z in (E,G,Y)]
    W=[prem(z,gam,2,base+[c2,q]) for z in (E,G,Y)]
    assert all(U) and all(W)
    return X+U,eq+W,pure
