"""Exact (literal fifth, ordinary fourth, actual silent-eighth tail) projections."""
from aq8_shape import (cf,rd,down,literal_fifth_exact,prospective_six,tail,front_data,ev)
from aq5_projection import flip
from aq_gamma import gpoly
from regular_star_projection import Co,remove
from small_crt import small_resultant, image, int_input
from functools import lru_cache

def res23(c,b,a,h,f,e,d):
    # Res_Y(aY²+bY+c, dY³+eY²+fY+h), padded even at a=d=0.
    return (a**3*h*h-a*a*b*f*h-2*a*a*c*e*h+a*a*c*f*f+a*b*b*e*h
       +3*a*b*c*d*h-a*b*c*e*f-2*a*c*c*d*f+a*c*c*e*e-b**3*d*h
       +b*b*c*d*f-b*c*c*d*e+c**3*d*d)

@lru_cache(None)
def fifth_project(front):
    H,J,z,gs,pegs=tail(front)
    P,Q=literal_fifth_exact(front),prospective_six(front)
    A=down(rd(res23(*cf(P,2),*cf(Q,3))))
    assert A.degrees()[:3]==(6,24 if front else 27,52)
    print('literal fifth exact resultant',front,A.degrees(),flush=True)
    return A


def crt(A,B,j):
    D,E=A.degrees()[0],B.degrees()[0]
    cap=tuple(D*B.degrees()[k]+E*A.degrees()[k] for k in [2,1])
    q=image(int_input(A)[:2],int_input(B)[:2],1129,406,cap,(D,E))
    assert q and any(a for c in q for a in c), (j,cap)
    return small_resultant(A,B)

@lru_cache(None)
def fourth_project(front):
    F,J,z,gs,pegs=tail(front)
    P=fifth_project(front)
    R=flip(crt(flip(J),flip(P),'fourth'))
    M,e=remove(R,(gs[7],))
    assert e==[3] and R.degrees()[:3]==(12,0,200 if front else 212)
    assert M.degrees()[:3]==(12,0,164 if front else 176)
    print('proj fourth exact raw/guard',front,R.degrees(),M.degrees(),e,flush=True)
    return M

@lru_cache(None)
def diagonal(front):
    F,J,z,gs,pegs=tail(front)
    G=fourth_project(front)
    R=crt(F,G,'outer')
    M,e=remove(R,(gs[0],gs[2],gs[3],gs[5],gs[7]))
    assert e==[24,4,4,12,4] and R.degrees()[:3]==(0,0,764 if front else 812)
    assert M.degrees()[:3]==(0,0,612 if front else 660)
    print('proj diagonal exact raw/guard',front,R.degrees(),M.degrees(),e,flush=True)
    X,e=remove(M,exceptional_sources(front))
    print('separate true fourth exceptional products',front,M.degrees()[2],X.degrees()[2],e,flush=True)
    assert e==[24 if front else 12,24,24] and X.degrees()[2]==(324 if front else 420)
    return gpoly(X).monic()


@lru_cache(None)
def exceptional_sources(front):
    F,J,_,gs,_=tail(front)
    A,B=front_data(front)[0][:2]
    j=Co(J,1)
    H=(j[2],ev(j,A),ev(j,B))
    assert all(a.degrees()[:3]==(0,0,4) for a in H)
    return H
