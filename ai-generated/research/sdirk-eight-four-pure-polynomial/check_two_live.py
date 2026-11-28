#!/usr/bin/env python3
"""Nonsplit 5-site quadrature candidates in the pure polynomial support branch."""
from flint import nmod_poly,fq_default_ctx,fq_default_poly_ctx
from itertools import permutations
from math import lcm,isqrt
refs=[]
for p in (103,149):
    assert all(p%n for n in range(2,isqrt(p)+1))
    Q=nmod_poly([2,3,-12,4],p)
    dQ=lcm(*(f.degree() for f,e in Q.factor()[1]))
    F=fq_default_ctx(p,2*dQ,'w');R=fq_default_poly_ctx(F);Y=R.gen()
    O=F.one();Z=F.zero()
    I=lambda P:sum((c/(i+1) for i,c in enumerate(P.coeffs()) if i%2==0),Z)
    def J(P):
        T=R([Z]+[c/(2*(i+1)) for i,c in enumerate(P.coeffs())])
        return T-T(-O)
    def card(xs,j):
        t=R.one()
        for i,r in enumerate(xs):
            if i!=j:t=t*(Y-r)/(xs[j]-r)
        return t
    for u,e in (4*Y**3-12*Y**2+3*Y+2).roots():
        if u+2==0:continue
        ga=O/(u+2);s=2*ga-1
        if (21*s**4-14*s*s+1)*(945*s**4-90*s*s+1)!=0:continue
        for d in (s,-s):
            G=(Y-d)*(Y*Y-9*s*s)
            M=[I(G*Y**i) for i in range(5)]
            piv=M[0]*M[2]-M[1]*M[1]
            assert piv!=0
            q=(M[1]*M[3]-M[2]*M[2])/piv
            k=(M[1]*M[2]-M[0]*M[3])/piv
            P=Y*Y+k*Y+q
            assert I(G*P)==I(Y*G*P)==I(Y*Y*G*P)==0
            r2=[y for y,e in P.roots()]
            print(p,'u',u,'gamma',ga,'d',d,'qpoly',P,'remaining zeros',r2,flush=True)
            assert len(r2)==2
            zs=[-3*s,*r2,3*s]
            assert all(zs[i]!=zs[j] for i in range(4) for j in range(i)) and d not in zs
            nd=[d,*zs]
            W=[I(card(nd,i)) for i in range(5)]
            if p==103:
                assert W[0]==0
                refs.append((p,int(d),0))
                continue
            assert all(w!=0 for w in W)
            assert all(sum((b*x**j for b,x in zip(W,nd)),Z)==I(Y**j) for j in range(8))
            nu=[card(zs,i)(d) for i in range(4)]
            r=Y*Y-s*s
            diag=sum((r(y)*b*(2*ga-b)/n for y,b,n in zip(zs,W[1:],nu)),Z)
            assert diag!=0
            refs.append((p,int(d),int(diag)))
            print('diag',diag,'nodes',nd,'weights',W,flush=True)
assert refs==[(103,54,0),(103,49,0),(149,137,62),(149,12,62)]



# The only separate canceled-aggregate control, and the n=1 last-pin check.
p=103
QQ=nmod_poly([2,3,-12,4],p)
LL=nmod_poly([3,0,-30,0,35],p)
KK=nmod_poly([1,2,-1],p)
ds=lcm(*(f.degree() for P in (QQ,LL,KK) for f,e in P.factor()[1]))
F=fq_default_ctx(p,ds,'w');R=fq_default_poly_ctx(F);Y=R.gen()
O=F.one();Z=F.zero()
ys=[y for y,e in (35*Y**4-30*Y*Y+3).roots()]
vs=[v for v,e in (1+2*Y-Y*Y).roots()]
assert len(ys)==4 and len(vs)==2
out=[]
for u,e in (4*Y**3-12*Y*Y+3*Y+2).roots():
    if u+2==0 or 3*u/(u+2) not in ys:continue
    ga=O/(u+2);s=2*ga-1
    assert s not in ys and -s not in ys
    assert all((u-2*v)/(u+2) not in ys for v in vs)
    wt=lambda y:(y*y-11*O/21)/(4*(y*y-3*O/7))
    assert all(wt(y)!=0 for y in ys)
    for d in (s,-s):
        nu=lambda a:((35*d**4-30*d*d+3)/(d-a))/(140*a**3-60*a)
        assert all(nu(y)!=0 for y in ys)
        v=sum(((y*y-s*s)*wt(y)*(2*ga-wt(y))/nu(y) for y in ys),Z)
        out.append(tuple(map(int,(u,ga,d,v))))
assert out==[(28,79,54,85),(28,79,49,85)]
print('canceled Gaussian controls and no one-live last pin',out)
