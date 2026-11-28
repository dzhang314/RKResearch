"""Exact four-ordinary field replay for a zero quartic first-middle signal."""
from argparse import ArgumentParser
from pathlib import Path
from runpy import run_path
import sympy as S

def check(args):
    F=run_path(str(args.beta_one/'finite.py'))
    A=F['A']
    G,seq,fs=A['projection']()
    assert sorted((q.degree(),e)for q,e in fs)==[(4,2),(4,9),(8,1),(24,1)]
    p24=next(q for q,r in fs if q.degree()==24).monic()
    J4,J5=F['J4'],F['J5']
    ev,pc,prim,mul,plus,scale,rat=(F[n]for n in ('ev','pc','prim','mul','plus','scale','rat'))
    arith=run_path(str(args.research/'dirk11-thirteen-invisible-six-constant-exclusion/replay.py'))
    Ring,quot=(arith[k]for k in ('Ring','quot'))
    P=Ring('prime',prime=103)
    K=Ring('ordinary degree24',P,[P.to(rat(p24.nth(i)))for i in range(24)])
    v=K.gen()
    linear=S.Poly(seq[-2],A['B'])
    assert linear.degree()==1
    B=-pc(linear.nth(0),v)/pc(linear.nth(1),v)
    assert ev([pc(G.nth(i),v)for i in range(4)],B)==0
    F4=A['F']
    assert ev([pc(F4.nth(i),v)for i in range(5)],B)==0
    lam=-J5(v)/J4(v)
    T5=[(K.to(c)+lam*d)/132 for c,d in zip((-1,20,-120,300,-330,132),(1,-14,56,-84,42,0))]
    R=quot(quot(T5,v),B)
    z,o=K.to(0),K.to(1)
    assert T5==mul(R,mul([-v,o],[-B,o]))
    c0,c1,c2,_=R
    Fn=[-c0*c1*c1,-12*c0*c1+12*c0*c2*c2-c1*c1*c2,-36*c0-4*c1*c2,12*c2]
    K1=Ring('direct Fn profile',K,[a/Fn[-1]for a in Fn[:-1]])
    s=K1.gen(); c2,c1,v,B=(K1.to(a)for a in (c2,c1,v,B))
    rr=6*c2*s/(c1+6*s)
    R=list(map(K1.to,R))
    z,o=K1.to(0),K1.to(1)
    P0=[z,*R]; L0=prim(P0)[1:]
    old=Ring('old cubic',K1,R[:-1]);y=old.gen()
    m=y*y+old.to(rr)*y+old.to(s)
    M=(J4(y)/m).v
    W=(ev([old.to(a)for a in L0],y)/m).v
    J=[K1.to(i)for i in (1,-14,56,-84,42)]
    C=plus(mul(L0,M),scale(mul(J,W),-o))
    D=[z]*(len(C)-3)
    for k in range(len(C)-1,2,-1):
        d=C[k]; D[k-3]=d
        for j in range(3):C[k-3+j]-=d*R[j]
    assert C[:3]==[0,0,0]
    t=-ev(D,v)/ev(L0,v)
    U=plus(M,scale(R,t))
    Db=ev(D,B)+t*ev(L0,B);ub=ev(U,B)
    b=o-B
    # Independent Y-endpoint formula for the forward first-clean J(b).
    ip=prim(mul([o,-o],U))
    Jb=(ev(ip,o)-ev(ip,B))/b
    Jb2=ev(prim([z,*F['refl'](U)]),b)/b
    assert Jb==Jb2
    gate=((B-v)*ub-Jb)*Db-(B-v)*Jb*ub
    gate.inv()
    print('Direct Fn rank72: beta-one zero-effective-adjacency gate is a unit at 103')

if __name__=='__main__':
    root=Path(__file__).resolve().parent.parent
    p=ArgumentParser()
    p.add_argument('--research',type=Path,default=root)
    p.add_argument('--beta-one',type=Path,default=root/'dirk11-thirteen-invisible-six-alpha-two-live-cubic-beta-one')
    check(p.parse_args())
