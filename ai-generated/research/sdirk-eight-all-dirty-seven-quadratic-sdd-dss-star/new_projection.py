"""S,D,D versus rear D,S,S-star, terminal uses a third D label."""
from sympy.polys.fields import field
from sympy.polys.rings import ring
from flint import fmpz_mpoly_ctx as MC
from itertools import combinations
from math import lcm
import sympy as S
from star_scalars import op
F,H,u=field('H,u',S.QQ)
G=MC.get(('H','u'),'lex')
m=(H+2)/2;c=H-1
def lp(z,j):
    t=z-H/2
    return t**3-3*m*m*t/5 if j==3 else t**4-6*m*m*t*t/7+3*m**4/35
def pp(f):
    if not f:return G.constant(0)
    z=lcm(*(int(S.Rational(a).q) for a in f.values()))
    return G.from_dict({tuple(map(int,ix)):int(a*z) for ix,a in f.items()})
def num(f):return pp(f.numer)
def strip(p,gg):
    for a in gg:
        while p and (b:=p.gcd(a)).total_degree()>0:
            p,q=divmod(p,b);assert not q
    return p
def setup(fm):
    a=u;b=2*u if fm=='A' else 2-u
    ds=(H,a,b)
    (fa,fb),oo=op(a,fm)
    gs=list(oo)+[m,H,H-2,u-2]+list(ds)+[j-k for j,k in combinations(ds,2)]
    gs+=[2*j-H for j in ds]+[j+k-H for j,k in combinations(ds,2)]
    gs+=[lp(j,4) for j in ds]
    assert all(gs)
    P1=lp(H,3)/lp(H,4)
    P2=(lp(a,3)/lp(a,4)-P1)/(a-H)
    T,y=ring('y',F.to_domain())
    t=y-T(H/2)
    L3=t**3-t*T(3*m*m/5)
    L4=t**4-t*t*T(6*m*m/7)+T(3*m**4/35)
    M=(L3-(T(P1)+T(P2)*(y-T(H)))*L4).exquo((y-T(H))*(y-T(a)))
    base=[num(x) for x in gs]
    assert all(pp(x.denom).total_degree()==0 for x in gs)
    gs += [P2,M.get((0,),F.zero)]
    assert all(strip(pp(x.denom),base).total_degree()==0 for x in gs)
    assert M.degree()==3 and all(gs)
    ps=[num(x) for x in gs]+[pp(x.denom) for x in gs]
    rows=[M.evaluate(y,b),M.get((2,),F.zero)+(b+2*c)*M.LC]
    assert all(rows) and all(strip(pp(q.denom),ps).total_degree()==0 for q in rows)
    vv=[strip(num(x),ps) for x in rows]
    return vv,ps,gs,(H,a,b,fa,fb,M)
def project():
  for fm in 'AS':
    vv,ps,gs,data=setup(fm)
    res=strip(vv[0].resultant(vv[1],'u'),[g for g in ps if g.degrees()[1]==0])
    assert res
    fs=res.factor()[1]
    assert sorted((g.total_degree(),n) for g,n in fs)==({'A':[(2,2),(24,1)],'S':[(2,6)]}[fm])
    print(fm,'new terminal projected mesh',[(g.total_degree(),n) for g,n in fs],flush=True)
    yield fm,fs,vv,ps,gs,data
if __name__=='__main__':list(project())
