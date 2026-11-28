"""Arithmetic-front actual silent eighth, exact ordinary fifth projection."""
from small_resultants_crt import arith_silent8_system
from small_crt import small_resultant
from arith_star_model import quartic_model,literal_fifth_poly
from regular_star_projection import C,Z,O,g,s,t,v,red,con,Co,remove,profile,ev
from functools import lru_cache
from time import perf_counter

@lru_cache(None)
def model():
    D,F,N=arith_silent8_system()
    R,AB,H,delta,dat,guards=quartic_model()
    a,b,q,La,Lb,A0,B0,M0,x,m=dat
    G=literal_fifth_poly()
    NC=Co(N,0);assert len(NC)==5
    N5=red(sum(w*g**(4-i)*(x-g*v)**i for i,w in enumerate(NC)))
    YY,counts=remove(N5,[g,La,Lb])
    assert YY.degrees()==(4,8,23,1) and counts==[5,0,0]
    print('arith silent8 ordinary fifth quartic',N5.degrees(),YY.degrees(),counts,flush=True)
    tm=perf_counter()
    Q=small_resultant(YY,G);assert Q
    J,cs=remove(Q,[*guards,delta,NC[-1]])
    assert Q.degrees()==(0,42,105,1) and J.degrees()==(0,32,69,1)
    assert cs==[6,0,0,2,0,0,0,0,0,2,0,0,0]
    print('arith silent8 ordinary fifth projection',Q.degrees(),J.degrees(),cs,round(perf_counter()-tm,2),flush=True)
    return D,J,F,N,G,H,delta,dat
