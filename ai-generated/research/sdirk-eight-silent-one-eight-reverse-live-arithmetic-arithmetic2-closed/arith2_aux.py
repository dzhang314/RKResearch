"""Smaller complete exact fourth guard resultants, not added actual equations."""
from arith2_projection import projections
from arith2_model import model
from arith2_outer import I
from arith_star_diagonal import int_input
from arith_star_fibers import gpoly
from regular_star_projection import Co,red
from rear67_exact import full_native
from silent8_diag import modular_resultant
from geometric_outer import compiler,img
from flint import fmpz_poly,fmpq_poly
from math import gcd,lcm
from sympy import nextprime
from pathlib import Path
from time import perf_counter
from functools import lru_cache

def poly_or(U,p,z):
    A,B,_=U
    return I.from_dict({j:(A.get(j,0)+z*B.get(j,0))%p for j in A.keys()|B.keys()})
def fn(A,B,p,r,ds0,ds1,use_fast=True):
    Q=[]
    for z in (r,p-r):
        U,V=(poly_or(X,p,z) for X in (A,B))
        if U.degrees()[1]!=ds0 or V.degrees()[1]!=ds1:return None
        q=img(U,V,p) if use_fast else None
        if q is None:q=(full_native(U,V,p) if use_fast else modular_resultant(U,V,p))
        assert q
        Q.append(q)
    a,b=pow(2,-1,p),pow(2*r,-1,p)
    return [[(x+y)*a%p for x,y in zip(*Q)],[(x-y)*b%p for x,y in zip(*Q)]]

def tiny(A0,B0,label):
    A,B=(int_input(F) for F in (A0,B0))
    da,ga=A0.degrees()[1:3];db,gb=B0.degrees()[1:3]
    cap=da*gb+db*ga
    bound=A[-1]**db*B[-1]**da
    Q=[[0]*(cap+1) for _ in range(2)];m=1;p=2**60;n=0;t=perf_counter()
    while m<=2*bound:
        p=int(nextprime(p+1000))
        if p%8!=7:continue
        r=pow(2,(p+1)//4,p);assert r*r%p==2
        W=fn(A,B,p,r,da,db)
        if W is None:continue
        if n==0:assert W==fn(A,B,p,r,da,db,False)
        k=pow(m,-1,p)
        for R,V in zip(Q,W):
            for j,a in enumerate(V):R[j]+=m*((a-R[j])*k%p)
        m*=p;n+=1
    Q=[[z if 2*z<m else z-m for z in W] for W in Q]
    assert all(abs(z)<=bound for W in Q for z in W)
    T=fn(A,B,1129,406,da,db,False)
    assert T and all((z-w)%1129==0 for R,V in zip(Q,T) for z,w in zip(R,V))
    h=min(next((j for j,z in enumerate(W) if z),cap+1) for W in Q)
    assert h<=cap
    C,D=[fmpz_poly(W[h:]) for W in Q]
    c=gcd(int(C.content()),int(D.content()))
    C,D=C//c,D//c
    norm=C*C-2*D*D
    assert norm
    norm=norm//norm.content()
    print('aux just guard exact',label,cap,bound.bit_length(),h,
          max(C.degree(),D.degree()),norm.degree(),n,round(perf_counter()-t,2),flush=True)
    return norm

def to_int(P):
    d=lcm(*(int(a.q) for a in P))
    R=fmpz_poly([int(a*d) for a in P])
    return R//R.content()

def Factors(P):
    R=fmpz_poly([1]);ans=[]
    for M,k in P.factor_squarefree()[1]:
        for W,e in M.factor()[1]:
            assert e==1
            W=W if W[W.degree()]>0 else -W
            ans.append((W,k));R*=W**k
    assert R==P or R==-P
    return ans

@lru_cache(None)
def guard_factor_data():
    A,B=projections();gs=model()[5]
    # Whole common leading support, including exact specializations.
    da,db=(gpoly(Co(Q,1)[-1]) for Q in (A,B))
    L=(da.a*da.a-da.b*da.b/2).gcd(db.a*db.a-db.b*db.b/2)
    data=[]
    for H,e in Factors(to_int(L)):data.append(('leading',H,e))
    for key,i in [('anchor',3),('quintic',9),('terminal_h',10)]:
        G=gs[i]
        S=tiny(A,G,key)
        data.extend((key,H,e) for H,e in Factors(S))
    print('aux exact factor records',[(name,H.degree(),e) for name,H,e in data],flush=True)
    return data

def main():
    F=guard_factor_data()
    Path('arith2-guard-proposals.txt').write_text(
        '\n'.join(name+' '+str(e)+' '+' '.join(map(str,H)) for name,H,e in F))

if __name__=='__main__':main()
