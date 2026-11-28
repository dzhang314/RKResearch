"""Exact signed middle projections for arithmetic front and true ordinary star rear."""
from functools import lru_cache
from h567_af_star_shape import signed_model
from h5_arthfront_projection import early,model,gpoly,Co,remove
from aq_rear import red
from h54_split_outer import exact_outer,strip_univariate_guards
from unequal_finite import E

def norm(P):
    return P.a*P.a-P.b*P.b/2

def r22(P,Q):
    p0,p1,p2=Co(P,1);q0,q1,q2=Co(Q,1)
    return red((p2*q0-p0*q2)**2-(p2*q1-p1*q2)*(p1*q0-p0*q1))

@lru_cache(None)
def middle_cuts():
    C,N,F,_=signed_model()
    H,D,A,B,J,Z,gs,_=model(False)
    ans=[]
    for i,V in enumerate((C,N)):
        U=r22(J,V);U0,e=remove(U,gs)
        assert U.degrees()==((32,0,94,1),(38,0,106,1))[i]
        assert U0.degrees()==((26,0,72,1),(29,0,78,1))[i]
        assert e==[4,2,i,0,0,0,0,0]
        print('arithmetic front star rear signed middle cut',U.degrees(),U0.degrees(),e,flush=True)
        ans.append(U0)
    return tuple(ans)

@lru_cache(None)
def project():
    P=early()
    C,N=middle_cuts()
    gs=model(False)[6]
    guards=tuple(q for q in gs if q.degrees()[0]==0)
    out=[]
    for i,V in enumerate((C,N)):
        R=exact_outer(P,V)
        R0,e=strip_univariate_guards(R,guards)
        assert R.degrees()==((0,0,1674,1),(0,0,1821,1))[i]
        assert R0.degree()==(1218,1299)[i]
        assert e==([240,54,0,0],[270,63,0,0])[i]
        print('arithmetic front star rear middle exact diagonal',R.degrees(),R0.degree(),e,flush=True)
        out.append(R0)
    n0,n1=map(norm,out)
    G=n0.gcd(n1)
    I=G//G.gcd(G.derivative())
    M=E(I).monic()
    L=norm(gpoly(Co(P)[-1])).gcd(norm(gpoly(Co(C)[-1]))).gcd(norm(gpoly(Co(N)[-1])))
    assert G.degree()==M.degree()==54 and L.gcd(I).degree()==0
    print('arithmetic front star rear middle common degree',G.degree(),M.degree(),
          'common Y-leading factor degree',L.gcd(I).degree(),flush=True)
    return M,P,C,N
