"""S,D,D versus rear D,S,S star: terminal is a reused front D."""
from sympy.polys.fields import field
from sympy.polys.rings import ring
from itertools import combinations
import sympy as S
from star_scalars import op,strip,assoc,rvalue,audit
F,H=field('H',S.QQ)
m=(H+2)/2;c=H-1
def lp(z,j):
    t=z-H/2
    return t**3-3*m*m*t/5 if j==3 else t**4-6*m*m*t*t/7+3*m**4/35
def project():
 for fm in 'AS':
    d=2*H if fm=='A' else 2-H
    (fa,fb),gs=op(H,fm)
    c=H-1
    F0=lp(H,3)/lp(H,4)
    F1=(lp(d,3)/lp(d,4)-F0)/(d-H)
    T,y=ring('y',F.to_domain())
    t=y-T(H/2)
    L3=t**3-T(3*m*m/5)*t
    L4=t**4-t*t*T(6*m*m/7)+T(3*m**4/35)
    M=(L3-(T(F0)+T(F1)*(y-T(H)))*L4).exquo((y-T(H))*(y-T(d)))
    e=-M.get((2,),F.zero)/M.LC-2*c
    ds=[H,d,e]
    gg=list(gs)+[m,H,H-2,F1,M.get((0,),F.zero)]
    base=gg[:len(gs)+3]+ds+[x-y for x,y in combinations(ds,2)]+[lp(x,4) for x in ds]
    assert all(base)
    gg += ds+[x-y for x,y in combinations(ds,2)]
    gg += [2*x-H for x in ds]+[x+y-H for x,y in combinations(ds,2)]
    gg += [lp(x,4) for x in ds]
    assert all(gg)
    guards=[z.numer for z in gg]+[z.denom for z in gg]
    # F*, M and e only divide by actual anchor Legendre values, the anchor
    # clock difference and the nonzero projection slope.
    denbase=[z.numer for z in base if z]
    denbase += [F1.numer]
    assert all(strip(z.denom,denbase).degree()==0 for z in gg)
    pol=M.evaluate(y,e)
    assert strip(pol.denom,guards).degree()==0
    hp=strip(pol.numer,guards)
    expected=15 if fm=='A' else 10
    assert [(f.degree(),n) for f,n in hp.factor_list()[1]]==[(expected,1)]
    print(fm,'terminal reused, projected H factors' ,[(f.degree(),n) for f,n in hp.factor_list()[1]],flush=True)
    for p,n in hp.factor_list()[1]:
        E,x=assoc(p)
        ev=lambda f:rvalue(f,E,x)
        if not all(ev(q) for q in gg):
            print(fm,p.degree(),'exact scalar guard lost',flush=True);continue
        U,z=ring('y',E)
        Mz=U.from_dict({ix:ev(q) for ix,q in M.items()})
        W=Mz.exquo(z-U(ev(e))).monic()
        out=audit(E,x,x,ev(d),ev(e),W,ev(fa),ev(fb))
        print(fm,p.degree(),'terminal reused',out,flush=True)
        yield fm,p.degree(),out
if __name__=='__main__':
    assert list(project())==[('A',15,'excluded'),('S',10,'excluded')]
    print('both reused-terminal phase families excluded')
