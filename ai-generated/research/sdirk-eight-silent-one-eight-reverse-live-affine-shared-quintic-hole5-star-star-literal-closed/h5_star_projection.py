"""Corrected fifth hole, true star rear: centered and homogeneous exact restrictions."""
from functools import lru_cache
from h5_regular_projection import model
from aq_rear import s as S,g,red,ev,divide
from regular_star_projection import Co

def even(V):
    A=Co(V,1)
    assert not any(A[1::2])
    return red(ev(A[::2],S))

@lru_cache(None)
def edges(front,slot):
    H,D,A,B,J,Z,gs,dat=model(front)
    a,b,r,x=dat[-4:]
    z={2:a,3:b}[slot]
    k=2-S*S;X=x-g;c=X-g*S;d=X+g*S
    hc,hd,hx=[ev(H,p) for p in (c,d,x)]
    v=S
    F=even(divide(red((1-v)*hc-(1+v)*hd+2*v*k*hx),v*(1-v*v)))
    E=even(red((x-z)*(hc+hd)/2-k*(X-z)*hx))
    O=even(red((x-z)*divide(hc-hd,2*v)+g*k*hx))
    return F,E,O
