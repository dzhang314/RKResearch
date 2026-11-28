"""Exact six-known-nonhole-peg projection, actual silent sixth or seventh."""
from functools import lru_cache
from h5_star_branches import L,SC,specialize,main_front
from h5_star_projection import edges
from h5_regular_projection import model,gpoly
from h54_arithmetic_projection import remove_in_cubic,Yrem
from aq_rear import u as Y,s as S,g,red,ev,divide
from regular_star_projection import Co,remove,nodal,mul,cof
from hole4_projection import crt
from aq5_projection import flip

def sig_mom(poly,k,hr,beta,r):
    return red(hr*sum(q/(j+k+1) for j,q in enumerate(poly))-beta*r**k*ev(poly,r))

@lru_cache(None)
def signed_model():
    H,D,A,B,J,Z,gs,dat=model(True)
    a,b,r,x=dat[-4:]
    F,_,_=edges(True,2)  # The symmetric F has no dependence on the silent clock.
    assert F==edges(True,3)[0]
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
    # Independent exact coefficient-column audit of the two scalar formulas.
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
    assert c0.degrees()==(13,2,37,1) and d0.degrees()==(16,2,43,0)
    print('signed centered six-known pegs',C.degrees(),c0.degrees(),ce,D1.degrees(),d0.degrees(),de,flush=True)
    return c0,d0,F,(m0,m1,m2,m3,nu4,nu5,E[-2],E[-1])

@lru_cache(None)
def project(cubic,second=False):
    H,D,A,B,J,Z,gs,dat=model(True)
    C0,D1,F,_=signed_model()
    T=D1 if second else C0
    if cubic:
        J0,T=Yrem(J),Yrem(T)
        Q=flip(crt(flip(J0),flip(T),'cubic Y true signed six-peg front'))
        Q=Yrem(Q)
        Q0,qe=remove(Q,gs)
        Q0,power=remove_in_cubic(Q0,A)
        Q0,mass_power=remove_in_cubic(Q0,gs[4])
        P=SC
        assert qe==[4,0,0,0,0,0,0,0] and mass_power==1
        assert Q.degrees()==((2,0,106,0) if second else (2,0,94,0))
        assert power==int(second)
        assert Q0.degrees()==((2,0,87,0) if second else (2,0,81,1))
        print('cubic Y signed elimination',second,J0.degrees(),T.degrees(),Q.degrees(),Q0.degrees(),qe,power,mass_power,flush=True)
    else:
        P=main_front()
        Q=red(ev(Co(T,1),(2*Y+1)/3))
        Q0,qe=remove(Q,gs)
        print('affine s signed projection',second,Q.degrees(),Q0.degrees(),qe,flush=True)
    R=crt(P,Q0,'corrected hole5 centered six-peg direction')
    R0,e=remove(R,tuple(v for v in gs if v.degrees()[0]==0))
    U,de=remove(R0,(L,))
    print('center six-peg gamma',cubic,second,'exact',R.degrees(),'guarded',R0.degrees(),e,'non L',U.degrees(),de,flush=True)
    if cubic:
        assert R.degrees()[2]==R0.degrees()[2]==(261 if second else 243)
        assert e==[0,0,0,0] and de==[0]
        return ((gpoly(R0).monic(),P,Q0,'usual'),)
    assert qe==[0,0,0,0,0,0,0,0] and de==[2]
    assert e==([68,12,0,0] if second else [56,9,0,0])
    assert (R.degrees()[2],R0.degrees()[2],U.degrees()[2])==((323,207,201) if second else (278,186,180))
    PL,QL=specialize(P),specialize(Q0)
    assert PL.degrees()==(4,0,2,1) and QL.degrees()==((16,0,2,0) if second else (13,0,2,1))
    print('center six-peg specialized degrees',PL.degrees(),QL.degrees(),flush=True)
    return ((gpoly(U).monic(),P,Q0,'usual'),(gpoly(L).monic(),PL,QL,'degenerate'))
