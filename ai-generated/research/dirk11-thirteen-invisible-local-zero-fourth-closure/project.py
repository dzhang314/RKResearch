#!/usr/bin/env python3
"""Finish the absent-fourth boundary by its true fifth-head quadratic."""
import argparse
from fractions import Fraction
from hashlib import sha256
from pathlib import Path
from runpy import run_path
import sympy as S

def verify(f,h):
    assert sha256(f.read_bytes()).hexdigest()==h.read_text().strip()

def run(research,core,data,p):
    assert S.isprime(p) and p>11
    here=Path(__file__).resolve().parent
    path=research/'dirk11-thirteen-invisible-six-constant-exclusion'/'replay.py'
    verify(path,here/'ring.sha256')
    Ring=run_path(str(path))['Ring']
    H,G,K,u0,u1=data
    rat,ev,pm,prim=(core[q] for q in ('rat','ev','pm','prim'))
    F=Ring('residue',prime=p); F.to(rat(K.LC())).inv()
    A=Ring('literal fourth V',F,pm(K.monic(),F)[:-1]); V=A.gen()
    def pc(q): return ev(pm(q,A),V)
    B=-pc(u0)/pc(u1)
    cs=[pc(H.nth(i))/pc(H.LC()) for i in range(5)]
    assert ev(cs,B)==ev([pc(G.nth(i)) for i in range(4)],B)==0
    c2=cs[3]+B;c1=cs[2]+B*c2;c0=cs[1]+B*c1
    assert 30*c0+20*c1+15*c2+12==0
    one,zero=A.to(1),A.to(0)
    de=A.to(Fraction(3,100))/(c0-c2*Fraction(3,10)-Fraction(9,25))
    l=A.to(Fraction(1,4))-de; l0=-de*c0*Fraction(10,3)
    Delta=de/(l+l0); de.inv()
    m=[one*Fraction(3,10),-one*Fraction(6,5),one]
    P=[zero,*m]; P0=[zero,c0,c1,c2,one]; IP=prim(P); IP0=prim(P0); I2P=prim(IP)
    R=Ring('old interpolation',A,[c0,c1,c2]); y=R.gen()
    def oe(c):return ev(list(map(R.to,c)),y)
    mi=oe(m).inv()
    W0=(oe(IP0[1:])*mi).v
    rho=(oe(I2P[1:])*mi).v
    def mm(a,b):
        c=[zero]*(len(a)+len(b)-1)
        for i,v in enumerate(a):
            for j,w in enumerate(b): c[i+j]+=v*w
        return c
    pB,p0B,iB,i0B,i2B=[ev(c,B) for c in (P,P0,IP,IP0,I2P)]
    (B-1).inv(); p0B.inv()
    ell=l*B+l0; wb=ev(W0,B); rb=ev(rho,B)
    # Linear forms in k_B: f, g, j, u from their actual definitions.
    f=[-pB-Delta*p0B,one]; g=[-iB-Delta*i0B,ell+Delta*wb]
    j=[-i2B,rb];u=[-iB,ell]
    A0=[a-b for a,b in zip(mm(j,f),mm(g,u))]
    v=A0[2].inv()
    C=Ring('any fifth head k_B',A,[A0[0]*v,A0[1]*v]); k=C.gen()
    def ce(q): return ev(list(map(C.to,q)),k)
    assert ce(A0)==0
    fi=ce(f).inv(); ce(g).inv()
    print(f"F{p}: full rank48 true fifth-head equation has live f,g (so d_B is live)",flush=True)
    a=1+(C.to(B)-1)*(k-C.to(pB))*fi
    q=(1-a)*C.to(Delta)
    def gate(x):
        R=x.r
        ell=R.to(l)*x+R.to(l0)
        rh=ev(list(map(R.to,rho)),x); w=ev(list(map(R.to,W0)),x)
        return (x-R.to(a))*((x-R.to(a))*ell-rh+R.to(q)*w)
    D=Ring('any next old repeat',C,list(map(C.to,[c0,c1,c2])))
    for name,x in [('fifth repetition',C.to(B)),('origin-clock slack',C.to(1/V)),('any old repetition',D.gen())]:
        gate(x).inv()
        print(f"F{p}: next {name} excluded by the full product gate",flush=True)

if __name__=='__main__':
    p=argparse.ArgumentParser()
    p.add_argument('--research',type=Path,default=Path(__file__).resolve().parent.parent)
    p.add_argument('--absent-core',type=Path)
    p.add_argument('--prime',type=int,action='append')
    a=p.parse_args()
    f=a.absent_core or a.research/'dirk11-thirteen-invisible-local-zero-fourth-origin'/'project.py'
    verify(f,Path(__file__).with_name('absent-project.sha256'))
    core=run_path(str(f)); data=core['exact']()
    for q in a.prime or [101]:
        run(a.research,core,data,q)
