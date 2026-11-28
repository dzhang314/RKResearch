"""Arithmetic rear of the eight active coprime reverse-silent fourth chart."""
from functools import lru_cache
from extra_active import invpoly
from no_extra import *
from quadratic_poly import E as EE
from off8_fibers import det,add,sc,mul,qr,ev,nodal,cramer
from time import perf_counter

MON=[Q(v,70) for v in Lco]
W=[sum(MON[j]/(j-i) for j in range(i+1,5)) for i in range(4)]
WL0=invpoly(EE,list(map(EE,W)),list(map(EE,MON)))
assert all(not w.b and w.degree()==0 for w in WL0)
WL=[w.a[0] for w in WL0]

def conj(A):
    return can(sum((v*(-t)**l*y**i*u**j*g**k for (i,j,k,l),v in A.to_dict().items()),cx.constant(0)))

def divX(A,G):
    c=conj(G)
    d=can(c*G)
    assert not d.degrees()[-1]
    return divmod(can(c*A),d)

def stripX(F,guards):
    done=[]
    for G in guards:
        j=0
        while F and G and sum(G.degrees())>0:
            T,R=divX(F,G)
            if R:break
            F=can(T);j+=1
        done.append(j)
    return F,done

def polymod(F,G):
    return [can(v) for v in qr(mul(F,G),MON)[1]]

def dpoly(p):
    return [sum(c*p**(j-i-1) for j,c in enumerate(MON) if i<j) for i in range(4)]

removed_common={}

@lru_cache(None)
def acdata(front):
    A,B,m,ha,hb,H4,qA,qB,q0,q1,sh,e,QT,QA,DT,DA=phases(front)
    a,b=expr(A),expr(B)
    q,bq=term(q0,g),term(q1,g)
    Qp=lambda r:g*q+bq*r
    Lp=lambda r:sum(v*r**j for j,v in enumerate(Lco))
    x=1-g; c=x-g*u; d=x-2*g*u
    k=1+2*u-u*u
    H=-2+u+4*u*u-u**3
    J=4*u**3-12*u*u+3*u+2
    Qx,Qc,Qd=map(lambda p:can(Qp(p)),(x,c,d))
    Lx,Lc,Ld=map(lambda p:can(Lp(p)),(x,c,d))
    F=can(H*Ld*Qc*Qx+2*J*Lc*Qd*Qx-k*J*Lx*Qc*Qd)
    F=exdiv(F,u*u)
    M0=can(k*Lx*Qc);M1=can(Lc*Qx)
    rho=[can(-c*M0+x*M1),can(M0-M1)]
    V=polymod(polymod(rho,mul([g*q,bq],[g*q,bq])),WL)
    pegs=[g*a,g*b,x,c,d]
    for r in pegs:
        V=polymod(V,dpoly(r))
    assert len(V)==4 and V[-1]
    Y=[can(v*g**j) for j,v in enumerate(V)]
    EE0=first5(F2,A,B,m,ha,hb,[],H4)
    EE1=first5(F2,A,B,m,ha,hb,[F2(1)],H4)
    Ell=[expr(v) for v in add(EE1,sc(EE0,-1))]
    E5=can(term(EE0,y)*(q+bq*y)+Lp(g*y)*sum(w*y**i for i,w in enumerate(Ell)))
    E5=exdiv(E5,(y-a)*(y-b))
    assert E5.degrees()[0]==3
    qres=can(sum(v*(-g*q)**j*bq**(4-j) for j,v in enumerate(Lco)))
    geom=[g,u,k,bq,qres,Qx,Qc,Qd]+[pegs[i]-pegs[j] for i in range(5) for j in range(i)]
    guards=geom+[Lp(r) for r in pegs]
    Z=[]
    for v in Y:
        T,nn=stripX(v,guards)
        Z.append(nn)
    print('arithmetic raw data',front,'F',F.degrees(),'Y',[v.degrees() for v in Y], 'E5',E5.degrees(),flush=True)
    geoexact=[]
    for G,i in zip(guards,[min(v[j] for v in Z) for j in range(len(guards))]):
        if i:geoexact.append((G,i))
    removed_common[front]=tuple(geoexact)
    print('common powers before reconstruction',front,[(guards.index(G),j) for G,j in geoexact],flush=True)
    # Divide the common product only through exact individual quotients in the fixed order.
    for G,i in geoexact:
        for e0 in range(i):
            R=[]
            for v in Y:
                w,r=divX(v,G)
                assert not r
                R.append(can(w))
            Y=R
    Q34=can(sum(v*y**j for j,v in enumerate(Y)))
    ex=perf_counter()
    N=can(Q34.resultant(E5,0))
    print('arithmetic first exact resultant',front,N.degrees(),'seconds',perf_counter()-ex,flush=True)
    N,f=stripX(N,guards)
    assert not any(f)
    print('arithmetic primitive resultant',front,N.degrees(),f,flush=True)
    return F,N,Y,E5,guards,geom,(a,b,q,bq,pegs,Lx,Lc,Ld)
