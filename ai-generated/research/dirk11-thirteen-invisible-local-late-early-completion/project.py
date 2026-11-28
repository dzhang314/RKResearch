#!/usr/bin/env python3
"""All late-silent continuations after an actual pre-fourth completed marked pair."""
import argparse
from hashlib import sha256
from fractions import Fraction
from pathlib import Path
from runpy import run_path

def verify_hash(path,ref):
    assert sha256(path.read_bytes()).hexdigest()==ref.read_text().strip()

def run(research,old_source,prime):
    here=Path(__file__).resolve().parent
    verify_hash(old_source,here/'old-project.sha256')
    O=run_path(str(old_source))
    # Recheck the earlier exact adjacent-repeat and consecutive-fifth tests;
    # both transfer after a genuine early completed marked pair.
    O['ranks'](research,prime)
    p=research/'dirk11-thirteen-invisible-six-constant-exclusion'/'replay.py'
    verify_hash(p,here/'ring.sha256')
    Ring=run_path(str(p))['Ring']
    ev,pm,mul,prim,sub=(O[k] for k in ('ev','pm','mul','prim','sub'))
    D=O['D']; tv,su,pr=O['exact_projection']()
    F=Ring('residue base',prime=prime)
    F.to(O['rat'](D.LC())).inv()
    K=Ring('literal old repeat anchor',F,pm(D.monic(),F)[:-1]); a=K.gen()
    t=ev(pm(tv,K),a); vB=ev(pm(su,K),a); vp=ev(pm(pr,K),a)
    U=Ring('fourth V, fifth B=vB−V',K,[vp,-vB]); V=U.gen(); B=U.to(vB)-V
    W=Ring('either old label different from repeat',U,
           [U.to(t*a*a),-U.to((2*t+Fraction(3,5))*a)])
    a,t=U.to(a),U.to(t)
    zero,one=U.to(0),U.to(1)
    lam=t/(4*t-Fraction(6,5))
    m=[Fraction(3,10)*a*a,-Fraction(6,5)*a,one]; P=[zero,*m]
    R=mul([-a,one],[t*a*a,-(2*t+Fraction(3,5))*a,one]); P0=[zero,*R]
    IP0=prim(P0); IQ=prim(mul([-a,one],P))
    PV,P0V,IP0V,IQV=(ev(f,V) for f in (P,P0,IP0,IQ))
    (IQV*P0V-(V-a)*PV*IP0V).inv()
    print(f"F{prime}: absent fourth G excluded by the full rank48 cleared primitive",flush=True)

    old=Ring('whole old cubic hull',U,R[:-1]); y=old.gen()
    def oe(f): return ev(list(map(old.to,f)),y)
    mi=oe(m).inv()
    W0=(oe(IP0[1:])*mi).v
    rho=(oe(prim(prim(P))[1:])*mi).v
    assert ev(W0,a)==ev(rho,a)==0
    def S(x):
        return (x-x.r.to(a))**2*x.r.to(lam)-ev(list(map(x.r.to,rho)),x)
    fv=sub(mul([PV,P0V/(V-a)],[S(V),ev(W0,V)]),[IQV,IP0V])
    def silent(x):
        g0,g1=S(x),ev(list(map(x.r.to,W0)),x)
        F0,F1,F2=map(x.r.to,fv)
        return F0*g1*g1-F1*g0*g1+F2*g0*g0
    for name,x in [('fifth twin',B),('origin twin',one),('fourth twin',V),('either other old twin',W.gen())]:
        silent(x).inv()
        print(f"F{prime}: immediate slack {name} excluded by the full fixed resultant",flush=True)

if __name__=='__main__':
    p=argparse.ArgumentParser()
    p.add_argument('--research',type=Path,default=Path(__file__).resolve().parent.parent)
    p.add_argument('--old-core',type=Path)
    p.add_argument('--prime',type=int,action='append')
    a=p.parse_args()
    old=a.old_core or (a.research/'dirk11-thirteen-invisible-local-slack-old-twin'/'project.py')
    for prime in a.prime or [101]:
        run(a.research,old,prime)
