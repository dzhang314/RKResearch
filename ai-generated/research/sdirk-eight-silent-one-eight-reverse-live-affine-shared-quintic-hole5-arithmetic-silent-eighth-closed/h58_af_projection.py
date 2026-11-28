"""Full exact arithmetic-front projection of the true ordinarily silent eighth."""
from functools import lru_cache
from h58_af_shape import shape
from h58_star_projection import res23_terms
from h5_arthfront_projection import model,early,gpoly,Co,remove,crt,flip
from aq_rear import red
from h54_split_outer import strip_univariate_guards
from h567_recycled_outer import exact_outer

@lru_cache(None)
def gap_law():
    H,D,A,B,J,Z,gs,dat=model(False)
    (C,*terminal),F,data=shape()
    R=red(sum(res23_terms(Co(J,1),C)))
    R0,ge=remove(R,gs)
    print('arithmetic front true silent8 mass-free gap law',R.degrees(),R0.degrees(),ge,flush=True)
    return R0

@lru_cache(None)
def y_project():
    H,D,A,B,J,Z,gs,dat=model(False)
    C,F,data=shape()
    Q=flip(crt(flip(F),flip(gap_law()),'actual silent8 arithmetic-front mass-free gap'))
    Q0,e=remove(Q,gs)
    print('arithmetic front true silent8 mass-free gap projected',Q.degrees(),Q0.degrees(),e,flush=True)
    return Q0

@lru_cache(None)
def project():
    P=early();Q=y_project()
    gs=model(False)[6]
    D=exact_outer(P,Q)
    D0,e=strip_univariate_guards(D,tuple(h for h in gs if h.degrees()[0]==0))
    M=D0.monic()
    n=lambda X:X.a*X.a-X.b*X.b/2
    G=n(gpoly(Co(P)[-1])).gcd(n(gpoly(Co(Q)[-1])))
    h=G.gcd(n(M % type(M)(G)))
    print('arithmetic front true silent8 mass-free outer',D.degrees(),M.degree(),e,
          'common Y-leading norm degree',h.degree(),flush=True)
    return M,P,Q

if __name__=='__main__':project()
