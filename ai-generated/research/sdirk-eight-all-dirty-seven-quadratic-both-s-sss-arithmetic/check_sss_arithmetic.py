"""Fixed exact certificates for both-S SSS arithmetic against true SDD."""
from pathlib import Path
import sys
BASE=Path(__file__).resolve().parent.parent
for name in ('last-rear-terminal-overlap','last-rear-extra-overlap','last-rear-disjoint-two-star'):
    sys.path.insert(0,str(BASE/('sdirk-eight-all-dirty-seven-quadratic-'+name)))
from sssa_projection import project,CZ
from check_terminal_overlap import K_h,spec_H
from check_extra_overlap import sp,gcd
from flint import nmod_poly as NP
from sympy import isprime
from sympy.polys.rings import ring

def sw(p):return CZ.from_dict({(j,i):v for (i,j),v in p.to_dict().items()})
def exact_small(q,rows,gs):
    K,u=K_h(sw(q));D,_=ring('H',K)
    f=lambda a:spec_H(sw(a),D,u)
    e,z=map(f,rows)
    assert e
    d=gcd(e,z%e.monic())
    assert d.degree()==1
    delta=f(gs['pivots'][2])
    assert delta and gcd(d,delta)==d.monic()
    print('degree',q.total_degree(),'exact linear H gcd lies on inverse determinant zero',flush=True)

def geom(mode,p,u,h):
    inv=lambda x:pow(x%p,-1,p)
    z=lambda x:NP([x%p],p)
    y=NP([0,1],p)
    c=(h+2)*inv(2)%p
    D=lambda v:-v**3+4*v*v+v-2
    K=lambda v:1+2*v-v*v
    N=lambda v:(1+4*v-4*v*v)*D(v)+4*v*v*(3*v-2)
    assert (c*u*(u-2)*D(u)*N(u)*K(u)*(3*u-2)*h*(h-u)*(h-2*u))%p
    beta=((3*u-2)*inv(D(u))-inv(2))%p
    assert beta
    a=(1-(3*u-2)*inv(D(u))*u)%p
    R=z(inv(2))+a*y+beta*y*y
    mu=int(R(h))
    assert mu
    W=R*inv(beta)
    S4=y*(y-u)*(y-2*u)*(y-h)
    t=y-h*inv(2)
    L3=t**3-3*inv(5)*c*c*t
    L4=t**4-6*inv(7)*c*c*t*t+3*inv(35)*c**4
    M=L4%W
    d,j,f=M.xgcd(W)
    assert d==z(1) and M*j%W==z(1)
    F=L3*j%W
    P,r=divmod(L3-F*L4,W)
    assert not r and P.degree()==3
    S0=S4%W
    assert S0
    i=0 if S0[0] else 1
    xi=int(M[i])*inv(int(S0[i]))%p
    C,r=divmod(L4-xi*S4,R)
    assert not r and C.degree()<=2
    T=2*y-h if mode=='A' else 2*h-2-y
    Q,r=divmod(P.compose(T)-P,T-y)
    assert not r
    G=P.gcd(Q)
    v=h-y
    g2=mu*K(v)
    e3,n3=(z(1),g2) if mode=='S' else (D(v),mu*N(v))
    X2=L4-g2*C
    U2=g2*(g2-R)
    X3=e3**2*L4.compose(T)-e3*n3*C.compose(T)
    U3=n3*(n3-e3*R.compose(T))
    assert G.degree()>0 and G.gcd(X2*U3-X3*U2).degree()==0
    print('literal D-pair residual gcd',G.degree(),'-> 0',flush=True)

def good_place(mode,q,rows):
    p,u,h={'S':(13,9,2),'A':(23,10,4)}[mode]
    assert isprime(p)
    F=sp(sw(q),p,0,0)
    assert F.degree()==q.total_degree() and not F(u) and F.derivative()(u)
    E,Z=[sp(sw(x),p,u) for x in rows]
    assert E.degree()==rows[0].degrees()[0]==5
    G=E.gcd(Z)
    assert G.degree()==1 and G.roots()==[(h,1)]
    geom(mode,p,u,h)
    print('large gap factor',q.total_degree(),'simple place',p,u,h,'excluded',flush=True)
def run():
    factors={'S':[(6,2),(12,2),(70,1)],'A':[(6,4),(12,4),(144,1)]}
    for mode in ('S','A'):
        ff,E,Q,gs=project(mode)
        assert sorted((q.total_degree(),n) for q,n in ff)==factors[mode]
        for q,n in ff:
            if q.total_degree()<=12:exact_small(q,[E,Q],gs)
            else:
                K,u=K_h(sw(q))
                assert K.ext is not None
                good_place(mode,q,[E,Q])
    print('both true opposite SDD arithmetic/star phases excluded',flush=True)
if __name__=='__main__':run()
