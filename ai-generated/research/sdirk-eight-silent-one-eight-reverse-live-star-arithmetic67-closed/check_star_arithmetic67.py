"""All exact diagonal factors and every guarded fourth-clock component."""
from pathlib import Path
import sys
ROOT=Path(__file__).resolve().parent.parent
for dep in (
    "sdirk-eight-half-quadratic",
    "sdirk-eight-half-star-quadratic",
    "sdirk-eight-silent-one-eight-reverse-live-constant",
    "sdirk-eight-silent-one-eight-reverse-live-exceptional",
    "sdirk-eight-silent-one-eight-reverse-live-regular-finite",
    "sdirk-eight-silent-one-eight-reverse-live-regular-silent-eighth-finite",
    "sdirk-eight-silent-one-eight-reverse-live-star4-regular-closed",
    "sdirk-eight-silent-one-eight-reverse-live-star-silent-eighth-closed",
    "sdirk-eight-silent-one-eight-reverse-live-arithmetic-star567-regular-closed",
    "sdirk-eight-silent-one-eight-reverse-live-arithmetic-silent-eighth-closed",
    "sdirk-eight-silent-one-seven-distinct-anchors",
    "sdirk-eight-silent-one-seven-distinct-coprime",
    "sdirk-eight-silent-one-seven-six-anchored",
    "sdirk-eight-silent-one-seven-six-reverse",
    "sdirk-eight-silent-one-seven-six-shared",
    "sdirk-eight-silent-three-closure",
    "sdirk-eight-silent-two-equal",
    "sdirk-eight-silent-two-high",
    "sdirk-eight-silent-two-unequal",
):
    sys.path.append(str(ROOT/dep))

from rear67_exact import projection
from rear67_model import model
from regular_star_projection import Co
from star4_guarded_fibers import Field,gpoly,modQ,modcoef
from star4_actual_fifth import Bfield,nmod_poly,gcdp,trim,sc,qr,mul
from paired_proposals import prime_series,rat
from flint import fmpq_poly
from sympy import isprime

# Factor degree, exponent -> (exact smaller fourth degree of J, degree
# of exact forbidden support, full local component count).
# None means a full unmodified fourth projection supplies the monic basis.
PLAN={
    11:{
       (224,1):(None,0,5),(225,1):(None,0,5),(666,1):(None,0,7),
       (3,2):(10,0,1),(6,2):(10,0,2),(12,6):(11,1,12),
       (30,6):(11,1,8),(9,12):(11,2,4),(4,18):(11,3,4),
       (21,24):(11,2,2),(4,54):(10,2,2),
    },
    14:{
       (306,1):(None,0,6),(304,1):(None,0,10),(390,2):(None,0,4),
       (24,2):(13,1,5),(9,12):(14,2,4),(12,12):(14,2,12),
       (30,12):(14,2,8),(4,36):(14,6,4),(21,48):(14,4,2),
       (4,96):(12,4,2),
    },
}

_cache={}
def s_coeffs(A):
    k=id(A)
    if k in _cache:return _cache[k][1]
    W={}
    for (j,i),z in A.to_dict().items():W.setdefault(i,{})[j]=int(z)
    U=tuple([W.get(i,{}).get(j,0) for j in range(1+max(W.get(i,{}),default=-1))]
            for i in range(1+max(W)))
    _cache[k]=(A,U)
    return U

def gfiber(A,K):
    return trim([K(nmod_poly([x%K.p for x in L],K.p)) for L in s_coeffs(A)])

def mono(U):
    assert U
    return sc(U,U[-1].inv())

def pol_mod(U,L,p):
    gg=L(nmod_poly([0,1],p))
    return trim([modcoef(s,L,gg,p) for s in U])

def proposed_support(P,G,K,p,t):
    M=modQ(K.M,p)
    assert M.degree()==K.M.degree() and M.leading_coefficient()==1
    L=Bfield(M,p,t);P,G=map(lambda W:pol_mod(W,L,p),(P,G))
    if not P or not G:raise ArithmeticError('invalid proposal leading')
    D=[L(1)]
    while len(P)>1:
        U=gcdp(P,G)
        if len(U)<=1:break
        P,R=qr(P,U);assert P and not R
        D=mul(D,U)
    return D

def exact_support(U,G,K,n):
    """Return U/D, only upon exact checks D|U and D|G^n."""
    assert U and G and n>0
    d=K.M.degree()
    C=[0]*(n*d);m=1
    for j,(p,t) in enumerate(prime_series()):
        if j>=80:break
        try:X=proposed_support(U,G,K,p,t)
        except (ArithmeticError,ZeroDivisionError,ValueError):continue
        if len(X)!=n+1:continue
        Y=[int(a.x[i]) for a in X[:-1] for i in range(d)]
        A=pow(m,-1,p)
        C=[z+m*((y-z)*A%p) for z,y in zip(C,Y)];m*=p
        W=[rat(z,m) for z in C]
        if any(z is None for z in W):continue
        D=[K(fmpq_poly(W[i:i+d])) for i in range(0,len(W),d)]+[K(1)]
        P,R=qr(U,D)
        if R or not P:continue
        V=[K(1)]
        for _ in range(n):V=qr(mul(V,G),D)[1]
        if V:continue
        assert len(U)-len(P)==n
        print('exact fourth support',d,n,m.bit_length(),flush=True)
        return mono(P)
    raise ArithmeticError(('unproved exact supported factor',d,n))

def full_fibers(M,d,pr,t,s_size,n):
    A,B,J,*rest=model()
    J=J[d];guard=rest[-1]['nodal_lead']
    K=Field(fmpq_poly(M));known=None
    if s_size is not None:
        P=trim([K(fmpq_poly(L)) for L in s_coeffs(J)])
        assert len(P)==s_size+1
        known=mono(P)
        if n:
            G=trim([K(gpoly(F)) for F in Co(guard,1)])
            known=exact_support(known,G,K,n)
        assert len(known)==s_size+1-n
    FM=modQ(K.M,pr)
    assert FM.degree()==M.degree() and FM.leading_coefficient()==1
    F=FM.factor()[1]
    cover=nmod_poly([1],pr)
    count=0
    for R,e in F:
        cover*=R**e
        L=Bfield(R,pr,t)
        I=[gfiber(P,L) for P in (A,B,J)]
        if known is None:
            W=next((w for w,s0 in zip(I,(48,54,d)) if len(w)==s0+1),None)
            assert W is not None      # one full selected integral leading unit
        else:
            W=pol_mod(known,L,pr)
            assert len(W)==len(known) and W[-1]==1
        for w in I:W=gcdp(W,w)
        assert len(W)==1               # actual fourth impossible
        count+=1
    assert cover==FM
    return count

def main():
    pr,t=1129,203
    assert isprime(pr) and 2*t*t%pr==1
    counts=[]
    for d,table in PLAN.items():
        F=projection(d)
        assert sorted((M.degree(),e) for M,e in F)==sorted(table)
        n=0
        for M,e in F:
            ss,guards,ex=table[M.degree(),e]
            c=full_fibers(M,d,pr,t,ss,guards)
            assert c==ex
            print('verified complete fourth branch',d,M.degree(),e,c,flush=True)
            n+=c
        counts.append(n)
    assert counts==[52,57]
    print('strict SDIRK8 regular star/ordinary-arithmetic silent6/7 excluded',
          counts,flush=True)

if __name__=='__main__':main()
