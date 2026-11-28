"""Two S front and genuine rear D,S,S arithmetic, new terminal."""
import sympy as S
from sympy.polys.fields import field
from sympy.polys.rings import ring
from flint import fmpz_mpoly_ctx as MC
from math import lcm
from itertools import combinations
def K(u):return 1+2*u-u*u
def DD(u):return -2+u+4*u*u-u**3
def NN(u):return (1+4*u-4*u*u)*DD(u)+4*u*u*(3*u-2)
def op(u,ph):
    if ph=='S':return (K(u)/2,K(u)/2),[u,u-1,u-2,K(u)]
    return (K(u)/2,NN(u)/(2*DD(u))),[u,DD(u),NN(u),K(u),3*u-2]
F,H,d,v=field('H,d,v',S.QQ)
C=MC.get(('H','d','v'),'lex')
m=(H+2)/2;p=H-v;q=H-2*v
D=DD(v);k=K(v);g=D-v*(v-2)*(3*v-2)
assert NN(v)==k*g
def lp(x,j=4):
    t=x-H/2
    return t**3-3*m*m*t/5 if j==3 else t**4-6*m*m*t*t/7+3*m**4/35
def phase(fo):
    if fo=='A2':
        u=d;s=2*d;(fd,fs),gg=op(u,'A')
    elif fo=='A3':
        u=d/2;s=u;(fs,fd),gg=op(u,'A')
    else:
        u=d;s=2-d;(fd,fs),gg=op(u,'S')
    return s,fd,fs,gg+[u-2]
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
def core(fo):
    s,fd,fs,gg=phase(fo)
    gg += [m,H,d,d-H,2*d-H,v,D,k,g,3*v-2,lp(H),lp(d)]
    gg += [a-b for a,b in combinations([F.zero,s,p,q,H,d],2)]
    assert all(gg)
    base=[num(a) for a in gg]
    assert all(poly(a.denom).total_degree()==0 for a in gg)
    T,y=ring('y',F.to_domain())
    t=y-T(H/2)
    L3=t**3-T(3*m*m/5)*t
    L4=t**4-T(6*m*m/7)*t*t+T(3*m**4/35)
    A0=lp(H,3)/lp(H)
    A1=(lp(d,3)/lp(d)-A0)/(d-H)
    M=(L3-(T(A0)+T(A1)*(y-T(H)))*L4).exquo((y-T(H))*(y-T(d)))
    M0=M.get((0,),F.zero)
    Ms=M.evaluate(y,s)
    ell0=2*M0
    ell1=(Ms/fs-ell0)/s
    aa=(fs-F.one/2)/s
    bb=M.LC/ell1
    e=-ell0/ell1
    assert M.degree()==3 and M0 and Ms and ell1 and bb
    R=T(F.one/2)+T(aa)*y+T(bb)*y*(y-T(s))
    E=M.get((2,),F.zero)*ell1-ell1*ell1*aa-M.LC*(ell0-ell1*s)
    rp=R.evaluate(y,p);rq=R.evaluate(y,q);rh=R.evaluate(y,H);rd=R.evaluate(y,d)
    s4=y*(y-T(s))*(y-T(p))*(y-T(q))
    W=R.exquo(T(bb))
    rm=L4%W;sm=s4%W
    l0,l1=[rm.get((i,),F.zero) for i in range(2)]
    z0,z1=[sm.get((i,),F.zero) for i in range(2)]
    NOD=l0*z1-l1*z0
    mu=2*rp
    Rv=D*(bb*(2*H-3*v-s)+aa)-(v-2)*(3*v-2)*rp
    assert D*rq-g*rp==-v*Rv
    LL=s*p*(p-s)
    Z=T(2*mu*lp(F.zero)*(p-s))*(y-T(s))*(y-T(p)) - T(mu*lp(s)*p/fs)*y*(y-T(p)) + T(2*D*lp(p)*s/g)*y*(y-T(s))
    EQ=g*Z.evaluate(y,q)-2*D*LL*lp(q)
    c=fd*(fd-rd);J=mu*LL*lp(d)-fd*Z.evaluate(y,d)
    EP=c*(4*k*k*LL*lp(H)-2*k*Z.evaluate(y,H))-J*(mu-2*k*rh)
    gg += [A1,M0,Ms,ell0,ell1]
    assert all(strip(poly(w.denom),base).total_degree()==0 for w in gg)
    base += [num(ell1),num(M0)]
    gg += [bb,e,e-H,e-d,e-s,e-p,e-q,2*e-H,e+d-H,lp(e),rp,rq,c]
    assert all(gg)
    assert all(strip(poly(w.denom),base).total_degree()==0 for w in gg)
    gs=[num(w) for w in gg]+[poly(w.denom) for w in gg]
    assert all(strip(poly(w.denom),gs).total_degree()==0 for w in [E,Rv,NOD,EQ,EP])
    rows=[strip(num(w),gs) for w in [E,Rv,NOD,EQ,EP]]
    named={'scale':num(m),'first graph value':num(M0),'terminal Legendre':num(lp(H)),
      'front Legendre':num(lp(d)),'anchor slope':num(A1),'paid affine slope':num(ell1)}
    return rows,gs,named

def ingress():
    rows,guards,named=core('A2')
    expected=[(18,18,0),(10,11,3),(22,26,2),(16,17,8),(26,27,8)]
    assert [z.degrees() for z in rows]==expected
    E,R,N,X,Y=rows
    q = strip(R.resultant(N,'v'),[z for z in guards if not z.degrees()[2]])
    assert q and q.degrees()==(84,100,0)
    print('verified nominal row degrees',expected,flush=True)
    print('verified first nodal projection',q.degrees(),flush=True)
    print('terminal-new A2 exclusion not certified',flush=True)
    return rows,guards,q,named
if __name__=='__main__':ingress()
