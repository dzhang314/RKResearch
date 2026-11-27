#!/usr/bin/env python3
"""Fraction-free candidate projection for the arithmetic, affine-helper chart."""
from flint import fmpz_mpoly_ctx,fmpz_poly,nmod_poly
from math import prod,gcd
from itertools import combinations
from pathlib import Path
import json,argparse
from fractions import Fraction
from sympy import primerange

R=fmpz_mpoly_ctx.get(('u','z'),'lex')
u,z=R.gens()
one,zero=R.constant(1),R.constant(0)

def add(f,g):
    p=[zero]*max(len(f),len(g))
    for i,v in enumerate(f): p[i]+=v
    for i,v in enumerate(g): p[i]+=v
    while len(p)>1 and not p[-1]:p.pop()
    return p

def mul(f,g):
    p=[zero]*(len(f)+len(g)-1)
    for i,v in enumerate(f):
        for j,w in enumerate(g): p[i+j]+=v*w
    return p

def scale(f,s): return [v*s for v in f]

def hull(nodes):
    f=[one]
    for y in nodes:f=mul(f,[-y,one])
    return f

def mom(p,j=0):
    return sum(v*(420//(i+j+1))*z**(i+j) for i,v in enumerate(p))

def value(p,y):return sum(v*y**i for i,v in enumerate(p))

def build():
    v=2*u-1; a=z-1
    Y=[a,v,u,one]
    M=u**2-4*u+2; T=u**3-7*u**2+10*u-2
    E=u**5-11*u**4+42*u**3-62*u**2+34*u-6
    J=5*u**5-46*u**4+148*u**3-191*u**2+90*u-12
    # The terminal affine test divided by its known nonzero common factor.
    S=[(u-2)*(2*u**4-11*u**3+11*u**2+6*u-6),
       -(2*u**5-12*u**4-u**3+105*u**2-178*u+78),
       3*(u-3)*(u-1)*(u**2-6*u+7)]
    H=hull(Y)
    A=[mom(H,j) for j in range(3)]
    B=[mom(mul([-a,one],S),j) for j in range(3)]
    D=A[1]*B[0]-A[0]*B[1]
    s=A[2]*B[0]-A[0]*B[2]
    p=A[2]*B[1]-A[1]*B[2]
    Q=[p,-s,D]
    HH=[hull([y for j,y in enumerate(Y) if i!=j]) for i in range(4)]
    K=[mom(mul(G,Q)) for G in HH]
    Wu=(u*E-J)*M*T*K[2]
    W1=-(E-J)*T*K[3]
    W=[u*W1-Wu,Wu-W1]
    gap=prod(Y[j]-Y[i] for i,j in combinations(range(4),2))
    CP=gap*prod(K)
    UR=[zero]
    for i,y in enumerate(Y):
        aux=(-1)**(3-i)*prod(Y[b]-Y[a] for a,b in combinations(range(4),2) if i not in (a,b))
        UR=add(UR,scale(HH[i],aux*value(W,y)**2*prod(k for j,k in enumerate(K) if i!=j)))
    newK=[D*A[1]-s*A[0],D*A[0]]
    def rem(f):
        while len(f)>2:
            n=len(f)-1
            f=add(scale(f,D),[zero]*(n-2)+scale(Q,-f[-1]))
        return f+[zero]*(2-len(f))
    a0,a1=rem(mul(newK,H));b0,b1=rem(add(scale(mul(W,W),CP),scale(mul(newK,UR),-one)))
    F=a0*b1-a1*b0
    bad=[('z',z),('gap',gap),('h-denom',E),('M',M),('T',T),('D',D),
         *[(f'K{i}',k) for i,k in enumerate(K)],
         *[(f'Q{i}',value(Q,y)) for i,y in enumerate(Y)],
         ('disc',s*s-4*p*D),
         ('Wh',W[0]*E+W[1]*J)]
    return F,bad,D,s,p


def to_uni(poly):
    pol=poly.to_dict()
    assert all(j==0 for i,j in pol)
    return fmpz_poly([int(pol.get((i,0),0)) for i in range(int(poly.degrees()[0])+1)])

def projected_rootless(f,p):
    q=nmod_poly(f.coeffs(),p)
    return q.degree()==f.degree() and all(q(i) for i in range(p))

def receipt(f):
    for p in primerange(2,500):
        if projected_rootless(f,p):
            return p
    raise AssertionError(("no projective receipt",f.degree()))

def pivot(D,s,p):
    polys=[]
    for P,k in zip((D,s,p),(2,3,4)):
        Q,rem=divmod(P,z**k)
        assert not rem and Q.degrees()==(5,6)
        polys.append(Q)
    D,s,p=polys
    j=to_uni(D.resultant(s,1)).gcd(to_uni(D.resultant(p,1)))
    c,fac=j.factor()
    assert j==c*prod(g**e for g,e in fac)
    stat=[]
    for g,e in fac:
        if g.degree()==1:
            r=Fraction(-int(g[0]),int(g[1]))
            assert r in (1,3)
            stat.append((1,e,str(r)))
        else:
            stat.append((g.degree(),e,receipt(g)))
    assert sorted(g.degree() for g,e in fac)==[1,1,2,2,2,30]
    print("Global rational Cramer receipts:",stat)

def rebuild(terms):
    P,bad,D,s,p=build()
    pivot(D,s,p)
    for lab,G in bad:
        while True:
            common=P.gcd(G)
            if all(int(a)==0 for a in common.degrees()):
                break
            P,rem=divmod(P,common)
            assert not rem
    cc=0
    for d in P.to_dict().values():
        cc=gcd(cc,int(d))
    H=P//cc
    assert H==R.from_dict(terms) and H.degrees()==(17,12)
    c,f=H.factor()
    assert H==c*prod(g**m for g,m in f)
    assert len(f)==1 and f[0][1]==1
    print("Verified the primitive bidegree-(17,12) curve after only genuine unit-factor cancellations.")

def project(terms,a,b):
    ans=[0]*13
    if b==0:
        return fmpz_poly([terms.get((17,i),0) for i in range(13)])
    powers=[a**i*b**(17-i) for i in range(18)]
    for (i,j),v in terms.items():ans[j]+=v*powers[i]
    return fmpz_poly(ans)

def cuts(terms):
    f=project(terms,9,1)
    assert f.degree()==12 and projected_rootless(f,31)
    for u in (-1,0,4,5,7,9,11):
        f=project(terms,u,1)
        print("fixed u",u,"rootless mod",receipt(f))
    u=fmpz_poly([0,1]); one=fmpz_poly([1])
    E=u**5-11*u**4+42*u**3-62*u**2+34*u-6
    J=5*u**5-46*u**4+148*u**3-191*u*u+90*u-12
    for label,A,B,deg,p in [
        ('paired terminal arithmetic grid',3*u-1,one,27,29),
        ('other arithmetic endpoint',3-u,one,27,31),
        ('line through residue control',2*u-5,one,27,41),
        ('ghost forward zero',J,E,77,23),
        ('ghost at midpoint',2*J,E,77,11),
    ]:
        F=sum(c*u**i*A**j*B**(12-j) for (i,j),c in terms.items())
        assert F.degree()==deg and projected_rootless(F,p)
        print(label, "degree",deg,"projectively rootless mod",p)

def sieve(terms,B):
    ps={}
    for p in primerange(5,120):
        allowed=set()
        for a in range(p+1):
            F=nmod_poly(project(terms,a,int(a<p)).coeffs(),p)
            if F.degree()!=12 or F.roots():
                allowed.add(a)
        ps[p]=allowed
    seen=kept=0
    found=[]
    for b in range(1,B+1):
        inv={p:pow(b,-1,p) if b%p else None for p in ps}
        for a in range(-B,B+1):
            if a in (b,2*b,3*b) or gcd(a,b)!=1:
                continue
            seen+=1
            if any((a*v%p if v is not None else p) not in ps[p] for p,v in inv.items()):
                continue
            f=project(terms,a,b)
            assert f
            kept+=1
            c,fac=f.factor()
            assert f==c*prod((q**e for q,e in fac),start=fmpz_poly([1]))
            for g,e in fac:
                if g.degree()==1:
                    found.append((Fraction(a,b),Fraction(-int(g[0]),int(g[1]))))
    print("Bounded-u exact diagnostic:",seen,"eligible u,",kept,"factored, projected pairs:",found)

if __name__=='__main__':
    arg=argparse.ArgumentParser()
    arg.add_argument('--rebuild',action='store_true')
    arg.add_argument('--height',type=int)
    args=arg.parse_args()
    raw=json.loads(Path(__file__).with_name("projected-curve.json").read_text())
    terms={tuple(e):int(v) for e,v in raw}
    assert len(terms)==231
    assert sum(a*pow(9,i,19)*pow(13,j,19) for (i,j),a in terms.items())%19==0
    if args.rebuild:
        rebuild(terms)
    cuts(terms)
    if args.height:
        sieve(terms,args.height)
