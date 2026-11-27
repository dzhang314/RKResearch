#!/usr/bin/env python3
from flint import fmpz_mpoly_ctx, fmpz_poly, nmod_poly
from sympy import primerange
from fractions import Fraction
from math import prod
from itertools import combinations
P=fmpz_mpoly_ctx.get(('u','x'),'lex')
u,x=P.gens()

def degree(P):
    return tuple(max((m[i] for m in P.to_dict()),default=-1) for i in range(2))

def sat(q,den):
    if not q:return q
    for d in den:
        if not d:raise Exception("invalid saturation")
        dv=degree(d)
        if dv==(0,0):continue
        while True:
            g=q.gcd(d)
            if degree(g)==(0,0): break
            q,r=divmod(q,g)
            assert not r
    return q

def rtless(q):
    for p in primerange(2,1000):
       n=nmod_poly(q.coeffs(),p)
       if n.degree()==q.degree() and not n.roots():return p

def univ(q,j=0):
    a=q.to_dict()
    return fmpz_poly([int(a.get((k,0) if j==0 else (0,k),0)) for k in range(degree(q)[j]+1)])

def rational_roots(q):
    c,fs=q.factor()
    assert q ==c*prod(f**e for f,e in fs)
    return [(Fraction(-int(f[0]),int(f[1])) if f.degree()==1 else f.degree(),
      (e,rtless(f)) if f.degree()>1 else e) for f,e in fs]

def term(kind,U):
 M=U*U-4*U+2
 if kind=='reflection':
    v=4-U;T=1+0*U;V=1+0*U
    q0,q1,q2=2,-4,1
 else:
    v=2*U-1;T=U**3-7*U*U+10*U-2;V=4*U**3-24*U*U+39*U-17
    q0,q1,q2=2*(U-2)*(U-1)**2,-2*(U-3)*(U-1)*(2*U-3),(U-3)*(U-2)**2
 G=lambda y:6*q0*(y-1)+3*q1*(y*y-2*y)+2*q2*(y**3-3*y*y)
 E=lambda y:-6*M*q1+q2*(-8*M+4*(1-M)*(y-1))-12*T*(1-y)
 return v,M,T,V,G,E

def model(kind,z,u,X,coeffj,DD=1):
 v,M,T,V,G,E=term(kind,u)
 # z below is the center, not the reciprocal diagonal.
 m0,m2,m4,m6=105,35*z*z,21*z**4,15*z**6
 X0,X1,X2=X
 K0=m6*DD**3-sum(X)*m4*DD**2+(X0*X1+X0*X2+X1*X2)*m2*DD-X0*X1*X2*m0
 KK=[K0]+[(m6*DD**2-sum(XX)*m4*DD+prod(XX)*m2)*DD for j in range(3) if (XX:=X[:j]+X[j+1:])]
 i,j,k=coeffj
 L1,Lu,Lv=-T*KK[i],M*T*KK[j],M*V*KK[k]
 W=lambda y:(u-y)*L1+(y-1)*Lu
 terminal=(u-1)*Lv-W(v)
 fourth=lambda c,k: 2*T*(u-1)*M*G(c)*KK[k]+E(c)*W(c)
 def iso():
   Pp=[-prod(X)]+[2*t*prod(t-r for j,r in enumerate(X) if j!=i) for i,t in enumerate(X)]
   weights=[p*k for p,k in zip(Pp,KK)]
   cross=[prod(v for j,v in enumerate(weights) if j!=i) for i in range(4)]
   L0=cross[0]+2*sum(cross[1:])
   L2=2*sum(a*t for a,t in zip(cross[1:],X))
   L4=2*sum(a*t*t for a,t in zip(cross[1:],X))
   A,B=W(z),Lu-L1
   return (A*A*DD*L0+B*B*L2)*(A*A*DD*L2+B*B*L4)-4*A*A*B*B*DD*L2**2
 den=[z,u-1,u-2,u-3,M,T,V,v-1,v-u,DD,*X,*KK,*[a-b for a,b in combinations(X,2)]]
 return terminal,fourth,iso,den

def separate(kind):
    v,*_=term(kind,u)
    z=x
    base=[1,u,v]
    X=[(y-z)**2 for y in base]
    terminal,fourth,iso,den=model(kind,z,u,X,[1,2,3])
    den=[P.constant(w) if isinstance(w,int) else w for w in den]
    A=sat(terminal,den)
    print(kind,'all represented terminal',degree(A),flush=True)
    receipts={
      "reflection":[[(4,1,19),(16,1,13)],[(2,4,13),(4,1,11)],
                    [(2,1,5),(10,1,11)],[(4,1,19),(10,1,11)]],
      "arithmetic":[[(7,1,19),(40,1,11)],[(7,1,19),(28,1,17)],
                    [(7,1,11),(28,1,17)],[(7,1,19),(28,1,13)]]}
    for i,c in enumerate([z,*[2*z-y for y in base]]):
       B=sat(fourth(c,i),den)
       q=A.resultant(B,1)
       assert q
       q=sat(q,den[:9])  # remove known nonzero univariate factors only
       roots=rational_roots(univ(q))
       assert all(isinstance(d,int) and t[1] for d,t in roots)
       assert sorted((d,*t) for d,t in roots)==receipts[kind][i]
       print(' fourth',i, degree(B), degree(q), roots,flush=True)

def const(w):
 return P.constant(w) if isinstance(w,int) else w

def coefficient(F,k):
 return P.from_dict({(i,0):n for (i,j),n in F.to_dict().items() if j==k})

def link_patterns(kind):
 U=2*u+1
 V,*_=term(kind,U)
 base=[const(1),U,V]
 for i in range(3):
    yield f'center {i}',base[i],base
 for i,j in combinations(range(3),2):
    yield f'pair {i}{j}',(base[i]+base[j])//2,base

def one_more(kind):
 for label,m,base in link_patterns(kind):
    rr=[]; jj=[]; cs={}
    diffs=[y-m for y in base]
    for r in diffs:
       if not r:
          jj.append(0);continue
       info=[j+1 for j,s in enumerate(rr) if s==r or s==-r]
       if info:jj.append(info[0]);continue
       rr.append(r);jj.append(len(rr))
    # The already certified centered arithmetic case has one known pair.
    if len(rr)!=2:
       assert kind=='arithmetic' and label in ('center 1','pair 02')
       print(kind,label,"covered by previous centered theorem",flush=True)
       continue
    U,V=base[1:]
    A,_,_,den=model(kind,m,U,[rr[0]**2,rr[1]**2,x],jj)
    assert all(j<2 for i,j in A.to_dict())
    N,D=-coefficient(A,0),coefficient(A,1)
    piv_nonzero=[const(w) for w in [*den[:8],rr[0],rr[1],rr[0]**2-rr[1]**2]]
    G=sat(D.gcd(N),piv_nonzero)
    assert degree(G)==(0,0)
    print(kind,label,'pivot',degree(D),"constant exceptional gcd",flush=True)
    X=[rr[0]**2*D,rr[1]**2*D,N]
    _,fourth,iso,den=model(kind,m,U,X,jj,D)
    den=[const(w) for w in den]
    B=sat(iso(),den)
    for c,k in [(m,0),*[(m-r,i+1) for i,r in enumerate(rr)],(m+x,3)]:
       if c in base:continue
       S=sat(fourth(c,k),den)
       if k==3:
          S=S.resultant(D*x*x-N,1)
       G=sat(S.gcd(B),den)
       assert degree(G)==(0,0)
       print(' fourth',k,degree(S),'gram',degree(B),'gcd constant',flush=True)

def fixed_double():
 from flint import fmpq_mpoly_ctx, fmpq
 Q=fmpq_mpoly_ctx.get(('s','r'),'lex')
 s,r=Q.gens()
 for d,ind in [(5,[1,0,1]),(7,[1,1,0])]:
    m=fmpq(5,3);U=fmpq(d,3)
    A,*_=model('reflection',m,U,[fmpq(4,9),r,s*s],ind)
    coeff=lambda k:Q.from_dict({(i,0):v for (i,j),v in A.to_dict().items() if j==k})
    N,D=-coeff(0),coeff(1)
    assert degree(A)[1]==1 and degree(N.gcd(D))==(0,0)
    X=[fmpq(4,9)*D,N,s*s*D]
    _,fourth,iso,den=model('reflection',m,U,X,ind,D)
    den=[Q.constant(w) if not hasattr(w,'to_dict') else w for w in den]
    F=sat(fourth(m+s,3),den)
    G=sat(iso(),den)
    q=F.gcd(G)
    assert degree(q)==(0,0)
    print('reflection double',d,'fourth',degree(F),'gram',degree(G),'gcd constant')

if __name__=='__main__':
    # Rationally nonzero scales used to specialize the two suffix branches.
    _,M,T,J,*_=term('arithmetic',u)
    assert rtless(univ(M))==3 and rtless(univ(T))==3 and rtless(univ(J))==5
    for kind in ('reflection','arithmetic'):
        separate(kind)
        one_more(kind)
    fixed_double()
