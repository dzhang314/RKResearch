"""Signed ordinary hole8 and nonliteral ordinarily silent placements 5/6/7."""
from functools import lru_cache
from h8l_projection import model,arithmetic_gap
from hm_projection import signed_columns
from aq_rear import g,s,ev
from hole4_projection import crt
from regular_star_projection import remove,det
from aq5_projection import flip
from aq_gamma import gpoly

@lru_cache(None)
def projection_data(front):
    H,den,Alp,Bet,J,dat=model(front)
    A,B,m,ha,hb,H4,a,b,x,c,r=dat
    F=arithmetic_gap()
    pegs=(a,b,g*s,x,c)
    Hr=ev(H,r)
    Cs=signed_columns(H,Bet,r,pegs,2)
    P=det(Cs)
    Del,e=remove(den,(g,));assert e==[1]
    gs=(g,Alp,Hr,Del)
    N,ex=remove(P,gs[1:])
    assert ex==[1,2,1]
    assert P.degrees()[:3]==(33,3,63) and N.degrees()[:3]==(13,3,28)
    print('ordinary hole8 middle signed determinant',front,F.degrees(),J.degrees(),P.degrees(),N.degrees(),ex,flush=True)
    return F,N,J,gs,pegs,Cs

@lru_cache(None)
def diagonal(front):
    F,N,J,gs,pegs,cols=projection_data(front)
    N0=flip(crt(flip(J),flip(N),'ordinary hole8 middle fourth'))
    N1,e=remove(N0,(gs[0],gs[1],gs[3]))
    assert e==[6,1,2] and N0.degrees()[:3]==(35,0,86) and N1.degrees()[:3]==(26,0,56)
    print('ordinary hole8 middle exact gap',front,N0.degrees(),N1.degrees(),e,flush=True)
    A=crt(F,N1,'ordinary hole8 middle diagonal')
    assert A.degrees()[:3]==(0,0,168)
    print('ordinary hole8 middle exact diagonal',front,A.degrees(),flush=True)
    return gpoly(A).monic(),N1
