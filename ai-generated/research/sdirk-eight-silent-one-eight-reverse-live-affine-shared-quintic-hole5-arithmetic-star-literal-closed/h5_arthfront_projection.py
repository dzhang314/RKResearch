"""Regular corrected hole 5: actual arithmetic front, centrally reflected star rear."""
from functools import lru_cache
from h5_star_projection import edges
from h5_regular_projection import model,gpoly
from aq_rear import g,red
from regular_star_projection import Co,remove
from hole4_projection import crt
from aq5_projection import flip

@lru_cache(None)
def early():
    H,D,A,B,J,Z,gs,dat=model(False)
    P=flip(crt(flip(J),flip(Z),'actual arithmetic zero fifth and fourth'))
    P0,e=remove(P,gs)
    assert J.degrees()==(3,2,10,1) and Z.degrees()==(4,3,0,1)
    assert P.degrees()==(17,0,30,1) and P0.degrees()==(17,0,27,1)
    assert e==[3,0,0,0,0,0,0,0]
    print('actual arithmetic front cut',J.degrees(),Z.degrees(),P.degrees(),P0.degrees(),e,flush=True)
    return P0

@lru_cache(None)
def tail(slot):
    H,D,A,B,J,Z,gs,dat=model(False)
    F,E,O=edges(False,slot)
    F0,F1=Co(F,1);O0,O1=Co(O,1)
    assert F1==140*A*g**4
    raw=red(F1*O0-F0*O1)
    Q0,e=remove(raw,gs)
    assert raw.degrees()==(6,0,21,1) and Q0.degrees()==(6,0,20,1)
    assert e==[1,0,0,0,0,0,0,0]
    print('literal arithmetic-front star-rear exact',slot,F.degrees(),O.degrees(),'raw',raw.degrees(),'legal guards',Q0.degrees(),e,flush=True)
    return Q0

@lru_cache(None)
def diagonal(slot):
    H,D,A,B,J,Z,gs,dat=model(False)
    P,Q=early(),tail(slot)
    M=crt(P,Q,'arithmetic front true star rear')
    Qg,e=remove(M,tuple(g0 for g0 in gs if g0.degrees()[0]==0))
    assert M.degrees()==(0,0,430,1) and Qg.degrees()==(0,0,298,1)
    assert e==[60,18,0,0]
    norm=lambda E:E.a*E.a-E.b*E.b/2
    Hlead=norm(gpoly(Co(P)[-1])).gcd(norm(gpoly(Co(Q)[-1])))
    assert Hlead.gcd(norm(gpoly(Qg))).degree()==0
    print('literal arithmetic front star rear diagonal',slot,M.degrees(),Qg.degrees(),e,flush=True)
    return gpoly(Qg).monic(),P,Q
