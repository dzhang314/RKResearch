"""Exact coprime eight-active fifth gate, both fronts, three live rear star rows."""
from itertools import product
from functools import lru_cache
from extra_active import invpoly
from seven_k0_anchors import *
from both_front_silent8 import context,front5
from quadratic_poly import E as EE
from off8_fibers import det,cramer,add,sc,mul,qr,ev,nodal

zero,one,g=EE(0),EE(1),EE(P([0,1]))
def ce(x):return Epoly(JJ(x)) if x else zero
L=mon(list(map(EE,Lco)))
W=[sum(L[j]/(j-i) for j in range(i+1,5)) for i in range(4)]
WL=invpoly(EE,W,L)
assert qr(mul(W,WL),L)[1]==[one]

def eres(F,G):
    f,n=len(F)-1,len(G)-1
    assert f>=0 and n>=0
    rows=[]
    for i in range(n):rows.append([zero]*i+F+[zero]*(n-1-i))
    for i in range(f):rows.append([zero]*i+G+[zero]*(f-1-i))
    return det(rows)

def guardf(T,guards):
    i=0
    for q in guards:
        assert q
        r=T.gcd(q)
        n=0
        while r.degree()>0:
            T=T.exact(r)
            n+=r.degree()
            r=T.gcd(q)
        i+=n
        if n:print("stripped",q.degree(),n,flush=True)
    return T.monic(),i

@lru_cache(None)
def data(front):
    A,B,m=map(ce,ends(front,1));ha,hb=(A-1)/2,(B-1-m)/2
    LP=list(map(EE,Lco))
    H4=[ce(q) for q in pol(h4(front),lambda x:x)]
    qa,qb=ev(LP,g*A)/ha,ev(LP,g*B)/hb
    q1=(qb-qa)/(B-A);q0=qa-q1*A
    phys=[g*q0,q1]
    x=1-g; mid=1-2*g
    c=[mid,-g];d=[mid,g]
    Qc,Qd=subst(phys,c),subst(phys,d); Qx=ev(phys,x)
    pc,pd,px=subst(L,c),subst(L,d),ev(L,x)
    h=sum_poly([sc(mul(mul([one,-one],pc),Qd),Qx),
               sc(mul(mul([-one,-one],pd),Qc),Qx),
               sc(mul([zero,EE(4),zero,EE(-2)],mul(Qc,Qd)),px)])
    AB,rem=qr(h,[zero,-one,zero,one])
    assert not rem and len(AB)==3 and not AB[1]
    a,b=AB[0],AB[2]
    assert a.gcd(b).degree()==0
    print("star gap coefficients",front,a.degree(),b.degree(),flush=True)
    # Missing cubic via congruence on four fixed Legendre basis coordinates.
    # Use beta=b*(u-1), beta^2=-a*b, and no division by b.
    Qb=[a*b,zero,one]
    cB=[b*mid,-g];dB=[b*mid,g]
    qcb=[b*Qd[0],-g*q1];qdb=[b*Qd[0],g*q1]
    def lb(z):
        return sum_poly([sc(power(z,j),v*b**(4-j)) for j,v in enumerate(L)])
    pcb,pdb=lb(cB),lb(dB)
    qcd=qr(mul(qcb,qdb),Qb)[1]
    pcd=qr(mul(pcb,pdb),Qb)[1]
    pqs=qr(add(mul(pcb,qdb),mul(pdb,qcb)),Qb)[1]
    assert all(len(s)==1 for s in (qcd,pcd,pqs))
    t0=b*b*(2*b+a)*px*qcd[0]
    t1=pqs[0]*Qx/2
    rho=[-mid*t0+x*t1,t0-t1]
    V=sc(qr(mul(mul(rho,power(phys,2)),WL),L)[1],-1)
    P5=mul(nodal([g*A,g*B,x]),[b*mid*mid+a*g*g,-2*b*mid,b])
    assert P5[-1]==b and len(P5)==6
    M=[qr([zero]*j+P5,L)[1] for j in range(4)]
    M=[[M[j][i] if i<len(M[j]) else zero for j in range(4)] for i in range(4)]
    vdet=det(M)
    U=cramer(M,V+[zero]*(4-len(V)))
    assert len(U)==4 and U[-1]
    assert all(sum(M[i][j]*U[j] for j in range(4))==vdet*s
               for i,s in enumerate(V+[zero]*(4-len(V))))
    F0=first5(EE,A,B,m,ha,hb,[],H4)
    F1=first5(EE,A,B,m,ha,hb,[one],H4)
    E5=add(mul(F0,[q0,q1]),mul(add(F1,sc(F0,-1)),[q*g**i for i,q in enumerate(LP)]))
    E5,rem=qr(E5,nodal([A,B]))
    assert not rem and len(E5)==4
    # Normalized missing clocks Y=c/g; no division by g in the resultant.
    T=[u*g**j for j,u in enumerate(U)]
    qres=sum(L[j]*(-g*q0)**j*q1**(4-j) for j in range(5))
    guards=[g,b,q1,qres,qa,qb,Qx,qcd[0]]
    # Other structural collision guards expressed in beta^2, not lost modulo p.
    guards += [a,a+b,a+2*b,1-g*(1+A),1-g*(1+B)]
    guards += [b*(z-mid)**2+a*g*g for z in (g*A,g*B,x)]
    base_guards=guards[:]
    guards += [px,pcd[0],vdet]
    print("degrees",front,[u.degree() for u in T],[u.degree() for u in E5],flush=True)
    GU=T[0]
    for v in T[1:]:GU=GU.gcd(v)
    GE=E5[0]
    for v in E5[1:]:GE=GE.gcd(v)
    print("content",front,GU.degree(),GE.degree(),flush=True)
    # Do not lose a lowered leading or content-zero branch; removed factors always need an exact guard.
    Gu,_=guardf(GU,guards);Ge,_=guardf(GE,guards)
    Uc=GU.exact(Gu);Ec=GE.exact(Ge)
    T=[v.exact(Uc) for v in T]
    E5=[v.exact(Ec) for v in E5]
    G=eres(T,E5)
    assert G
    print('star exact full fifth resultant',front,G.degree(),flush=True)
    G,_=guardf(G,guards)
    G=G.exact(G.gcd(G.der())).monic()
    assert G.degree()==27
    print('star retained fifth resultant',front,G.degree(),flush=True)
    H,_=guardf(px*pcd[0],base_guards)
    H=H.exact(H.gcd(H.der())).monic()
    assert H.degree()==40 and H.gcd(E5[-1]).degree()==0
    print('star Gauss peg locus',front,H.degree(),'fifth leading gcd',H.gcd(E5[-1]).degree(),flush=True)
    return G,(a,b,q0,q1,A,B,m,ha,hb,H4),T,E5,guards,H,base_guards
