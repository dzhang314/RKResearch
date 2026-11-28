"""Distinct all-dirty D,S,S / D,S,S; genuinely split quadratic graph."""
import sympy as S
from sympy.polys.fields import field
from flint import fmpz_mpoly_ctx as MC
from math import lcm
from scalar_geometry import D,k,N
F,h,d,u,v=field('h,d,u,v',S.QQ)
C=MC.get(('h','d','u','v'),'lex')
hh,dd,uu,vv=C.gens()
m=h+1;den=35*h*h-21*m*m
a=6*m*m/7;b=3*m**4/35
L=lambda t:t**4-a*t*t+b
W=lambda t:t*(t+d)
theta=den*d*d-21*m*m*h*h+15*m**4
RF=D(u)*(2*h-d-3*u)-(u-2)*(3*u-2)*W(u-h)
RR=D(v)*(2*h+d-3*v)-(v-2)*(3*v-2)*W(h-v)
s1,s2,s3,s4=u-h,2*u-h,h-v,h-2*v
NF=lambda x:(x-s1)*(x-s2)
NR=lambda x:(x-s3)*(x-s4)
n0=NF(0)*NR(0)
E=L(d)*n0-b*NF(-d)*NR(-d)
assert D(u)*k(u)*W(s2)-N(u)*W(s1)==-u*k(u)*RF
assert D(v)*k(v)*W(s4)-N(v)*W(s3)==-v*k(v)*RR
gs0=[m,h,d,d-h,d+h,den,L(h),L(d)]
gs=gs0+[u,v,k(u),k(v),D(u),D(v),N(u),N(v),3*u-2,3*v-2]
from itertools import combinations
gs+=[x-y for x,y in combinations([s1,s2,s3,s4,-h,h,d],2)]
gs+=[W(x) for x in [s1,s2,s3,s4]]
def intp(p):
    if not p:return C.constant(0)
    lc=lcm(*(int(S.Rational(c).q) for c in p.values()))
    return C.from_dict({tuple(map(int,i)):int(c*lc) for i,c in p.items()})
def strip(p,gs):
    for g in gs:
        while p and (q:=p.gcd(g)).total_degree()>0:
            p,r=divmod(p,q);assert not r
    return p
def num(x):return intp(x.numer)
def pi():
    assert all(gs)
    gg=[num(x) for x in gs]
    pp=[num(x) for x in [theta,RF,RR,E]]
    for f in (theta,RF,RR,E):assert strip(intp(f.denom),gg).total_degree()==0
    print('split raw',[p.degrees() for p in pp],flush=True)
    q=strip(pp[2].resultant(pp[3],'v'),[g for g in gg if not g.degrees()[3]])
    print('split v',q.degrees(),flush=True)
    r=strip(pp[1].resultant(q,'u'),[g for g in gg if g.degrees()[2:]==(0,0)])
    print('split u',r.degrees(),flush=True)
    out=strip(pp[0].resultant(r,'d'),[g for g in gg if g.degrees()[1:]==(0,0,0)])
    fac=out.factor()[1]
    assert sorted((j.total_degree(),e) for j,e in fac)==[(4,6),(60,2)]
    print('split projected factors',[(g.degrees(),n) for g,n in fac],flush=True)
    return fac,pp,q,r
if __name__=='__main__':pi()
