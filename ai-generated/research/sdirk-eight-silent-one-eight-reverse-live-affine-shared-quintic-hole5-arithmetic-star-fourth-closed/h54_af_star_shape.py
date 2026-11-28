"""True arithmetic-front ordinarily silent fourth, centered star rear."""
from h5_arthfront_projection import model
from h5_star_projection import edges,even
from regular_star_projection import remove,Co
from aq_rear import s as S,g,red,ev,divide
from functools import lru_cache

@lru_cache(None)
def U():
    H,den,alp,bet,J,Z,gs,dat=model(False)
    a,b,r,x=dat[-4:]
    F,E,O=edges(False,2)
    F0,F1=Co(F,1)
    assert F1==140*alp*g**4
    X=x-g
    L=even(divide(red(ev(H,X-g*S)-ev(H,X+g*S)),2*S))
    l0,l1=Co(L,1)
    a0=red(F1*l0-F0*l1)
    b0=red(g*ev(H,x)*(2*F1+F0))
    V=divide(red((x-g*S)*a0+b0),g)
    assert V.degrees()==(6,1,20,1)
    return V,F,a0

@lru_cache(None)
def trial():
    H,D,A,B,J,Z,gs,dat=model(False)
    V,F,a0=U()
    v0,v1=Co(V,1)
    assert v1==-a0
    j0,j1,j2=Co(J,1)
    z0,z1,z2,z3=Co(Z,1)
    C=red(j2*v0**2-j1*v0*v1+j0*v1**2)
    N=red(-z3*v0**3+z2*v0**2*v1-z1*v0*v1**2+z0*v1**3)
    C1,e=remove(C,gs)
    N1,f=remove(N,gs)
    assert C.degrees()==(15,0,50,1) and C1.degrees()==(15,0,46,1)
    assert e==[4,0,0,0,0,0,0,0]
    assert N1.degrees()==N.degrees()==(22,0,60,1) and f==[0]*8
    print('true arithmetic front, silent fourth, exact star affine cuts',
           'U',V.degrees(),'C',C.degrees(),C1.degrees(),e,'N',N.degrees(),N1.degrees(),f,
           flush=True)
    return C1,N1
