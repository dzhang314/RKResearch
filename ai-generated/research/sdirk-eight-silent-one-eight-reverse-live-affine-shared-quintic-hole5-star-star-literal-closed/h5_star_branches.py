"""Exact star Ψ split and centered tail diagonal, retaining actual leading-zero locus."""
from functools import lru_cache
from h5_star_projection import edges
from h5_regular_projection import model,gpoly
from aq_rear import t,u as Y,s as S,g,red,ev
from regular_star_projection import Co,remove
from hole4_projection import crt
SC=Y**3-9*Y**2+18*Y-6
L=120*g**3-60*g**2+12*g-1

@lru_cache(None)
def main_front():
    H,D,A,B,J,Z,gs,dat=model(True)
    assert Z==red(SC*(3*S-2*Y-1)/32)
    q=red(ev(Co(J,1),(2*Y+1)/3))
    q0,e=remove(q,gs)
    assert q0.degrees()==(5,0,9,1) and e==[1,0,0,0,0,0,0,0]
    print('noncubic star Ψ front',q0.degrees(),e,flush=True)
    return q0

@lru_cache(None)
def mini_rear(slot):
    H,D,A,B,J,Z,gs,dat=model(True)
    F,E,O=edges(True,slot)
    F0,F1=Co(F,1);O0,O1=Co(O,1)
    assert F1==140*A*g**4
    Q=red(F1*O0-F0*O1)
    q0,e=remove(Q,gs)
    assert q0.degrees()==(6,0,20,1) and e==[1,0,0,0,0,0,0,0]
    print('centered star rear exact',slot,q0.degrees(),flush=True)
    return q0

def specialize(P):
    """Exact coefficient specialization, with no generic branch degree assumptions."""
    return red(divmod(P,L)[1])

@lru_cache(None)
def branches(slot,cubic):
    P=SC if cubic else main_front()
    Q=mini_rear(slot)
    gs=model(True)[6]
    if not cubic:
        assert Co(P)[-1]==(-1881600*g**9*t + 940800*g**8*t -188160*g**7*t+15680*g**6*t)/3 or (Co(P)[-1].degrees()[2], P.degrees())
    R=crt(P,Q,'centered actual hole5 star Ψ split')
    R0,e=remove(R,tuple(v for v in gs if v.degrees()[0]==0))
    F,d=remove(R0,(L,))
    print('split star Ψ full',slot,cubic,'exact',R.degrees(),'guarded',R0.degrees(),e,'leading-outside',F.degrees(),d,flush=True)
    if cubic:
        assert R.degrees()[2]==R0.degrees()[2]==60 and e==[0,0,0,0]
        assert Co(P)[-1]==1
        print('cubic actual leading is monic; leave L complete',flush=True)
        return ((gpoly(R0).monic(),P,Q,'usual'),)
    PL,QL=specialize(P),specialize(Q)
    print('specialized leading target', PL.degrees(),QL.degrees(),flush=True)
    assert (R.degrees()[2],R0.degrees()[2],F.degrees()[2])==(130,82,79)
    assert e==[24,6,0,0] and d==[1]
    assert PL.degrees()==(4,0,2,1) and QL.degrees()==(5,0,2,1)
    return ((gpoly(F).monic(),P,Q,'usual'),(gpoly(L).monic(),PL,QL,'degenerate'))
