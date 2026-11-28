"""Exact coupled front/rear projection with literal extra reverse-live fourth."""
from functools import lru_cache
from h5_star_branches import L,SC,specialize,main_front
from h5_star_projection import even
from h5_regular_projection import model,gpoly
from aq_rear import u as Y,s as S,g,red,ev,divide
from regular_star_projection import Co,remove
from hole4_projection import crt
from aq5_projection import flip

@lru_cache(None)
def zero_one():
    H,D,A,B,J,Z,gs,dat=model(True)
    a,b,r,x=dat[-4:]
    k=2-S*S;X=x-g;c=X-g*S;d=X+g*S
    hc,hd,hx=[ev(H,p) for p in (c,d,x)]
    v=S
    F=even(divide(red((1-v)*hc-(1+v)*hd+2*v*k*hx),v*(1-v*v)))
    terms=[]
    for z in (0,1):
        E=even(red((x-z)*(hc+hd)/2-k*(X-z)*hx))
        O=even(red((x-z)*divide(hc-hd,2*v)+g*k*hx))
        terms.append((E,O))
    return F,*terms

@lru_cache(None)
def exact_U():
    H,D,A,B,J,Z,gs,dat=model(True)
    F,(_,O0),(_,O1)=zero_one()
    f0,f1=Co(F,1);o00,o01=Co(O0,1);o10,o11=Co(O1,1)
    assert f1==140*A*g**4
    U=divide(red(f1*(o00+g*S*(o10-o00))-f0*(o01+g*S*(o11-o01))),g)
    assert U.degrees()[1]==1
    return U

@lru_cache(None)
def project(cubic):
    H,D,A,B,J,Z,gs,dat=model(True)
    U=exact_U()
    if cubic:
        U0,E=remove(flip(crt(flip(J),flip(U),'silent4 cubic front fourth and centered odd')),gs)
        print('cubic Y front+tail coupled',U0.degrees(),E,flush=True)
        assert U0.degrees()==(15,0,46,1) and E==[4,0,0,0,0,0,0,0]
        P=SC;Q=U0
    else:
        P=main_front();Q=red(ev(Co(U,1),(2*Y+1)/3))
    R=crt(P,Q,'silent4 exact centered')
    R0,e=remove(R,tuple(v for v in gs if v.degrees()[0]==0))
    F,d=remove(R0,(L,))
    print('silent4 split centered',cubic,'Y Q',Q.degrees(),'exact',R.degrees(),'guarded',R0.degrees(),e,'leading-outside',F.degrees(),d,flush=True)
    if cubic:
        assert R0.degrees()==R.degrees()==(0,0,138,1) and e==[0,0,0,0]
        return ((gpoly(R0).monic(),P,Q,'usual'),)
    assert Q.degrees()==(7,0,20,0)
    assert (R.degrees()[2],R0.degrees()[2],F.degrees()[2])==(139,85,82)
    assert e==[30,6,0,0] and d==[1]
    PL,QL=specialize(P),specialize(Q)
    assert PL.degrees()==(4,0,2,1) and QL.degrees()==(6,0,2,0)
    print('silent4 specialized leading target',PL.degrees(),QL.degrees(),flush=True)
    return ((gpoly(F).monic(),P,Q,'usual'),(gpoly(L).monic(),PL,QL,'degenerate'))
