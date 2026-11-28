"""Unique singleton endpoint; both real prefixes have two D sites and only one shared D label."""
import sympy as S
from sympy.polys.fields import field
from sympy.polys.rings import ring
from flint import fmpz_mpoly_ctx as MC
from itertools import combinations,product
from math import lcm
def K(u):return 1+2*u-u*u
def DD(u):return -2+u+4*u*u-u**3
def NN(u):return (1+4*u-4*u*u)*DD(u)+4*u*u*(3*u-2)
def op(u,ph):
    if ph=='S':return (K(u)/2,K(u)/2),[u,u-1,u-2,K(u)]
    return (K(u)/2,NN(u)/(2*DD(u))),[u,DD(u),NN(u),K(u),3*u-2]
F,H,d=field('H,d',S.QQ)
C=MC.get(('H','d'),'lex')
m=(H+2)/2
def lp(x,j=4):
    t=x-H/2
    return t**3-3*m*m*t/5 if j==3 else t**4-6*m*m*t*t/7+3*m**4/35
def pairs(mode,d):
    if mode=='A2':
        u=d;s=2*d;(fd,fs),gg=op(u,'A')
    elif mode=='A3':
        u=d/2;s=u;(fs,fd),gg=op(u,'A')
    else:
        u=d;s=2-d;(fd,fs),gg=op(u,'S')
    return s,fd,fs,gg
def back(fo):
    v=H-d
    ts,gd,gs,rr=pairs(fo,v)
    return H-ts,gd,gs,rr
def poly(q):
    if not q:return C.constant(0)
    d=lcm(*(int(S.Rational(c).q) for c in q.values()))
    return C.from_dict({tuple(map(int,ix)):int(d*c) for ix,c in q.items()})
def num(q):return poly(q.numer)
def strip(p,gs):
    for x in gs:
        while p and (z:=p.gcd(x)).total_degree()>0:
            p,r=divmod(p,z);assert not r
    return p
def ip(y,pts):
    a=F.zero
    for x,t in pts:
        for z,_ in pts:
            if z!=x:t*= (y-z)/(x-z)
        a+=t
    return a
def frame(which,fo,ro):
    ds0=H if which=='terminal' else d
    ds1=d if which=='terminal' else H
    s,ff,fs,guards=pairs(fo,ds0)
    t,gd,gt,rg=back(ro)
    rg0,rg1=(F.one/2,gd) if which=='terminal' else (gd,F.one/2)
    gu=ds0/2 if fo=='A3' else ds0
    guards += rg+[m,H,gu-2]+[x-y for x,y in combinations([F.zero,s,t,H,d],2)]
    guards += [lp(H),lp(d),2*d-H]
    if not all(guards):return None
    base=[num(x) for x in guards]
    assert all(poly(x.denom).total_degree()==0 for x in guards)
    T,y=ring('y',F.to_domain())
    x=y-T(H/2)
    L3=x**3-T(3*m*m/5)*x
    L4=x**4-T(6*m*m/7)*x*x+T(3*m**4/35)
    a0=lp(H,3)/lp(H);a1=(lp(d,3)/lp(d)-a0)/(d-H)
    M=(L3-(T(a0)+T(a1)*(y-T(H)))*L4).exquo((y-T(H))*(y-T(d)))
    M0=M.get((0,),F.zero)
    Ms=M.evaluate(y,s);Mt=M.evaluate(y,t)
    z0=2*M0;z1=(Ms/fs-z0)/s
    a=(fs-F.one/2)/s
    b=M.LC/z1
    e=-z0/z1
    E=M.get((2,),F.zero)*z1-z1*z1*a-M.LC*(z0-z1*s)
    r=lambda u:F.one/2+a*u+b*u*(u-s)
    lam=r(t)/gt
    be=-lp(ds0)/(ff*rg0)
    U=[(F.zero,-be/2),(ds0,-be*ff),(ds1,lp(ds1)/rg1)]
    V=[(F.zero,2*lp(F.zero)),(ds0,-be*rg0),(ds1,-be*rg1)]
    eq1=fs*ip(s,U)+be*fs*fs+lam*(fs*ip(s,V)-lp(s))
    eq2=gt*ip(t,U)-lp(t)+lam*(gt*ip(t,V)+be*gt*gt)
    guards += [a1,M0,Ms,Mt,z0,z1]
    assert all(guards)
    assert all(strip(poly(x.denom),base).total_degree()==0 for x in guards)
    base += [num(z1)]
    guards += [b,e,e-H,e-d,e-s,e-t,2*e-H,e+d-H,lp(e),r(t),lam*rg0-ff]
    assert all(guards)
    assert all(strip(poly(x.denom),base).total_degree()==0 for x in guards)
    gg=[num(x) for x in guards]+[poly(x.denom) for x in guards]
    assert all(strip(poly(x.denom),gg).total_degree()==0 for x in [E,eq1,eq2])
    rows=[strip(num(x),gg) for x in [E,eq1,eq2]]
    return rows,gg,(s,t,ds0,ds1,ff,fs,rg0,rg1,gt,lam,be,U,V,e,r)
def project(modes=('terminal',)):
 for w,fo,ro in product(modes,('A2','A3','S'),('A2','A3','S')):
    fm=frame(w,fo,ro)
    if fm is None:
        print(w,fo,ro,'literal clash',flush=True);continue
    rows,gs,data=fm
    assert all(rows)
    E,X,Y=rows
    hs=[z for z in gs if not z.degrees()[1]]
    P=[strip(E.resultant(z,'d'),hs) for z in (X,Y)]
    assert all(P)
    q=P[0].gcd(P[1])
    assert q
    f=q.factor()[1]
    if w=='terminal':
        expected={
          ('A2','A2'):([252,172],[24]), ('A2','A3'):([364,284],[4,24]),
          ('A2','S'):([162,24],[]),('A3','A2'):([149,119],[13]),
          ('A3','A3'):([195,165],[13]),('A3','S'):([102,72],[13]),
          ('S','A2'):([162,118],[15]),('S','A3'):([238,194],[15]),('S','S'):([99,24],[])
        }
        assert [z.total_degree() for z in P]==expected[fo,ro][0]
        assert sorted(z.total_degree() for z,k in f)==expected[fo,ro][1]
        assert all(k==1 for z,k in f)
    print(w,fo,ro,'projection degrees' ,[z.total_degree() for z in P],
        'H factors',[(a.total_degree(),e) for a,e in f],flush=True)
    yield w,fo,ro,f,rows,gs,data
if __name__=='__main__':list(project())
