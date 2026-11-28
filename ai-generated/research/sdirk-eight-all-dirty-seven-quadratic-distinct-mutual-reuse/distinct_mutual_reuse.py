"""Both distinct doubled endpoints, extra D labels mutually reusing them."""
import sympy as S
from itertools import combinations_with_replacement
from sympy.polys.fields import field
from sympy.polys.rings import ring
from flint import fmpz_mpoly_ctx as MC
from math import lcm
from time import monotonic

F,h,d=field('h,d',S.QQ)
X=S.Symbol('h')
C=MC.get(('h','d'),'lex')
hh,dd=C.gens()
m=h+1
def L(t):return t**4-F(6)*m*m*t*t/7+F(3)*m**4/35
def k(u):return 1+2*u-u*u
def D(u):return -2+u+4*u*u-u**3
def N(u):return (1+4*u-4*u*u)*D(u)+4*u*u*(3*u-2)
kap=k(2*h)/2
delta=35*h*h-21*m*m
S0=(21*m*m*h*h-15*m**4)/delta
Th=35*hh*hh*dd*dd-21*(hh+1)**2*(hh*hh+dd*dd)+15*(hh+1)**4
ThF=35*h*h*d*d-21*m*m*(h*h+d*d)+15*m**4
def shape(lab):
    if lab=='A':
        return 3*h,N(2*h)/(2*D(2*h)),[D(2*h),N(2*h),6*h-2]
    return 2-3*h,kap,[2*h-1,2*h-2]
def integer(p):
    if not p:return C.constant(0)
    den=lcm(*(int(S.Rational(c).q) for c in p.values()))
    return C.from_dict({tuple(map(int,ij)):int(c*den) for ij,c in p.items()})
def strip(f,gs):
    if not f:return f
    for g in gs:
        while (p:=f.gcd(g)).total_degree()>0:
             f,r=divmod(f,p);assert not r
    return f

def case(f,r,kind):
    l,gf,g1=shape(f);q,gr,g2=shape(r);q=-q
    if kind=='split':
       W=lambda t:t*(t+d)
       ds=[-h,h,d]
    else:
       W=lambda t:t*t-S0
       ds=[-h,h,F.zero]
    rg=gf/W(l);lam=rg*W(q)/gr
    beta=-2*L(h)/kap
    gs=[m,h,delta,L(h),kap]+g1+g2+[W(l),W(q),l-q,lam,
        F.one/2-lam*kap,kap-lam/2]+[a-b for a in (l,q) for b in ds]
    if kind=='split':
        gs+=[d,d-h,d+h,L(d)]
    if not all(gs):
        print('identical guard',kind,f,r,flush=True);return None
    vals=[(-h,-beta*(F.one/2+lam*kap)+beta*rg*W(-h)),
          (h,-beta*(kap+lam/2)+beta*rg*W(h)),
          (l,lam*L(l)/gf)]
    def ip(y):
        ans=F.zero
        for i,(a,z) in enumerate(vals):
            for j,(b,_) in enumerate(vals):
                if i!=j:z=z*(y-b)/(a-b)
            ans+=z
        return ans
    rel=ip(q)-L(q)/gr
    ints=[integer(p.numer) for p in gs]
    ivs=[integer(p.denom) for p in gs]
    assert strip(integer(rel.denom),ints+ivs).total_degree()==0
    return rel,ints,gs,vals,rg,lam,beta,W,ds,l,q,gf,gr

def run():
 for kind in ('even','split'):
  for f,r in combinations_with_replacement(('A','S'),2):
    seq=case(f,r,kind)
    if not seq:continue
    rel,gs,*_=seq
    S0=strip(integer(rel.numer),gs)
    if not S0:
        print(kind,f,r,'IDENTITY',flush=True)
        continue
    Ch=S0 if kind=='even' else Th.resultant(S0,'d')
    if not Ch:
        print(kind,f,r,'IDENTICAL On theta',S0.degrees(),flush=True);continue
    Ch=strip(Ch,[a for a in gs if a.degrees()[-1]==0])
    ff=Ch.factor()[1]
    print(kind,f,r,'projection factors',[(a.total_degree(),b) for a,b in ff],flush=True)
    # Keep exact factors for the subsequent trace/chronology.
    yield kind,f,r,Ch,seq
if __name__=='__main__':list(run())
