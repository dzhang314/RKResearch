"""Exact six-known-nonhole-peg projection, actual silent sixth or seventh."""
from functools import lru_cache
from h5_star_projection import edges
from h5_regular_projection import model
from aq_rear import u as Y,s as S,g,red,ev,divide
from regular_star_projection import Co,remove,nodal,mul,cof

def sig_mom(poly,k,hr,beta,r):
    return red(hr*sum(q/(j+k+1) for j,q in enumerate(poly))-beta*r**k*ev(poly,r))

@lru_cache(None)
def signed_model():
    H,D,A,B,J,Z,gs,dat=model(False)
    a,b,r,x=dat[-4:]
    F,_,_=edges(False,2)  # The symmetric F has no dependence on the silent clock.
    assert F==edges(False,3)[0]
    F0,F1=Co(F,1)
    assert F1==140*A*g**4
    q=g*S; X=x-g
    E4=nodal([a,b,q,x])
    E=mul(E4,[red(F1*X**2+g*g*F0),red(-2*X*F1),F1])
    assert len(E)==7 and E[-1]==F1
    hr=ev(H,r)
    assert hr==g*gs[4]
    assert all(not sig_mom(H,j,hr,B,r) for j in range(4))
    m0,m1,m2,m3=(sig_mom(E,k,hr,B,r) for k in range(4))
    nu4,nu5=(sig_mom(H,k,hr,B,r) for k in (4,5))
    h3,h4=H[-2:];K=F1
    assert K==2*g**4*h4
    # Divide common h4 polynomialically, not m0; h4 != 0 at the actual tableau.
    C=red(m0*m2-m1*m1-2*g**4*nu4*m0)
    # The secondary signed gate after cancellation of the indicated leading coefficient.
    #  ν4 K/h4 = 2γ^4 ν4. E[5] also has the factor K by construction.
    E5h=divide(E[-2],h4)
    D0=red((E5h*nu4+2*g**4*nu5)*m0-2*g**4*nu4*m1-(m0*m3-m1*m2))
    D1=red(h4*D0-2*g**4*h3*nu4*m0)
    # Audit the two scalar cuts independently against exact signed polynomial columns.
    def WD(T):
        return [red(sum(T[j]*(hr/(j-i)-B*r**(j-i-1))
                        for j in range(i+1,len(T)))) for i in range(len(T)-1)]
    WH=WD(H)
    ee=[E,[0*E[0]]+E]
    vals=[[red(cof(H,WD(T),j)-cof(T,WH,j)) for j in (1,2,3)] for T in ee]
    (p1,p2,p3),(q1,q2,q3)=vals
    assert red(p3*q2-p2*q3-h4*h4*C)==0
    assert red(p3*q1-p1*q3+h4*(D1-h3*C))==0
    c0,ce=remove(C,gs)
    d0,de=remove(D1,gs)
    assert ce==de==[6,0,0,0,1,0,0,0]
    assert (c0.degrees(),d0.degrees())==((13,2,37,1),(16,2,43,1))
    print('signed centered six-known pegs',C.degrees(),c0.degrees(),ce,D1.degrees(),d0.degrees(),de,flush=True)
    return c0,d0,F,(m0,m1,m2,m3,nu4,nu5,E[-2],E[-1])
