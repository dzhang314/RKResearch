"""Deterministic integer resultants via a rigorous coefficient bound and CRT."""
from ctypes import CDLL,POINTER,c_ulong,c_long,c_int,sizeof
from pathlib import Path
from math import isqrt
from sympy import prevprime
from flint import fmpz,fmpz_poly,nmod_mpoly_ctx
from time import monotonic

def data(A):
    h,d=tuple(map(int,A.degrees()))
    rows=[[0]*(h+1) for _ in range(d+1)]
    for (i,j),a in A.to_dict().items():rows[j][i]=int(a)
    l=[sum(abs(x) for x in row) for row in rows]
    return h,d,[x for r in rows for x in r],1+isqrt(sum(x*x for x in l))
def direct_residue(A,B,p,ways):
    C=nmod_mpoly_ctx.get(('H','d'),p,'lex')
    aa,bb=[C.from_dict({ix:int(v)%p for ix,v in a.to_dict().items()}) for a in (A,B)]
    z=aa.resultant(bb,'d')
    coeff=[0]*ways
    for (i,j),a in z.to_dict().items():
        assert not j
        coeff[i]=int(a)
    return coeff
def fast_kernel(path):
    assert sizeof(c_ulong)==8 and sizeof(c_long)==8
    library=CDLL(str(Path(path).resolve()))
    f=library.rk_mp
    f.argtypes=[POINTER(c_ulong),POINTER(c_ulong),c_long,c_long,
                POINTER(c_ulong),c_long,c_long,c_ulong,c_long]
    f.restype=c_int
    def residue(A,B,p,ways):
        ha,da,a,_=A;hb,db,b,_=B
        ai=(c_ulong*len(a))(*(v%p for v in a))
        bi=(c_ulong*len(b))(*(v%p for v in b))
        out=(c_ulong*ways)()
        assert not f(out,ai,ha+1,da,bi,hb+1,db,p,ways)
        return list(out)
    return residue
def resultant(A,B,residue=None):
    a,b=data(A),data(B)
    ha,da,ai,hA=a;hb,db,bi,hB=b
    ways=ha*db+hb*da+1
    bound=hA**db*hB**da
    print('strict CRT coefficient bound bits',bound.bit_length(),
          'degree bound',ways-1,flush=True)
    hs=[0]*ways;M=1;k=0;t=monotonic();p=2**64
    while M<=2*bound:
        p=int(prevprime(p))
        assert fmpz(p).is_prime() and M%p
        # Only use primes preserving both global degrees in the eliminated d.
        if not (any(x%p for x in ai[da*(ha+1):]) and any(x%p for x in bi[db*(hb+1):])):
            continue
        if residue is None:v=direct_residue(A,B,p,ways)
        else:
            v=residue(a,b,p,ways)
            if k==0:assert v==direct_residue(A,B,p,ways)
        inv=pow(M,-1,p)
        hs=[x+M*((y-x)*inv%p) for x,y in zip(hs,v)]
        M*=p;k+=1
        if not k%30:print('CRT modulus bits',M.bit_length(),'elapsed',monotonic()-t,flush=True)
    hs=[x if 2*x<=M else x-M for x in hs]
    assert max(map(abs,hs))<=bound
    R=fmpz_poly(hs)
    # Redundant independent spot check of orientation and specialization.
    points=0
    for z in range(1,40):
        def at(w):
            h,d,l,_=w
            coeff=[]
            for j in range(d+1):
                c=0
                for v in reversed(l[j*(h+1):(j+1)*(h+1)]):c=c*z+v
                coeff.append(c)
            return fmpz_poly(coeff)
        U,V=at(a),at(b)
        if U.degree()!=da or V.degree()!=db:continue
        assert U.resultant(V)==R(z)
        if R(z):points+=1
        if points==3:break
    assert points==3
    print('exact CRT resultant degree',R.degree(),'primes',k,
          'elapsed',monotonic()-t,flush=True)
    return A.context().from_dict({(i,0):int(c) for i,c in enumerate(hs) if c})
