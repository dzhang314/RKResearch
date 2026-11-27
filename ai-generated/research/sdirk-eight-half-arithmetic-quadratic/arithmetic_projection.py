"""Exact degree-four Bézout projection for the remaining arithmetic signs."""
import sys
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parent.parent / "sdirk-eight-half-star-quadratic"))
from star_projection import *
import literal_front as F
from itertools import combinations

def arith_pencil(sign):
    A,b,hA,hb,hs,d,W,AA,BB,CC,DD,M=F.front_data(False)
    c,e,k,l,_=F.end(sign,False);c=1-c;e=1-e
    a,b,ha,hb,c,e,k,l=map(Rat.k,(A,b,hA,hb,c,e,k,l))
    def value(poly,s,Y):
        return sum(Rat.k(v)*s**i*Y**j for (i,j,z),v in poly.items() if not z)
    uu=W.exquo(d.exquo((F.s-A)*(F.s-F.end(1,False)[1])))
    coeffs=[sum(Rat.k(v)*s**i for (i,j0,z),v in uu.items() if j0==j and not z) for j in range(3)]
    y_lead=coeffs[2]
    RY=Ring2(coeffs[0]/y_lead,coeffs[1]/y_lead)
    y=RY.gen()
    legs=[[-1,12,-30,20],[1,-20,90,-140,70],[-1,30,-210,560,-630,252]]
    V=lambda x:[ev(v,x) for v in legs]
    V3=[V(x) for x in (a,b,s)]
    dv=det(V3)
    ah=value(AA,s,y);bh=value(BB,s,y);hy=-ah/bh
    hstar=value(hs,s,0)
    coeffs=[cramer(V3,[h*x**j for h,x in zip((ha,hb,hstar),(a,b,s))]) for j in range(3)]
    pp=[[sum(U[i]*(legs[i][j] if j<len(legs[i]) else 0) for i in range(3))/dv for j in range(6)]
        for U in coeffs]
    lv=[ev(u,y)-hy*y**j for j,u in enumerate(pp)]
    aff=(-lv[2]/lv[1],-lv[0]/lv[1])
    qs=[[zero,aff[0],one],[one,aff[1],zero]]
    ps=[[u*aff[0]+v for u,v in zip(pp[1],pp[2])],
        [u+v*aff[1] for u,v in zip(pp[0],pp[1])]]
    evpc=[ev(u,c) for u in ps];evpd=[ev(u,e) for u in ps]
    evqc=[ev(u,c) for u in qs];evqd=[ev(u,e) for u in qs]
    rearEq=[l*a-k*b for a,b in zip(mul(evqd,evpc),mul(evqc,evpd))]
    assert len(rearEq)==3

    R=Ring2(rearEq[0]/rearEq[2],rearEq[1]/rearEq[2]);beta=R.gen()
    q=[R(u)+beta*v for u,v in zip(*qs)];p=[R(u)+beta*v for u,v in zip(*ps)]



    pegs=(a,b,s,y,c,e)
    generic=(pegs,q,p,R,RY)
    raw=(pegs,qs,ps,rearEq,RY)
    C=[[v/dv for v in A] for A in coeffs]
    L=[R(C[2][j]+C[1][j]*aff[0])+beta*(C[0][j]+C[1][j]*aff[1]) for j in range(3)]
    pivots=[y_lead,s-a,s-b,y-a,y-b,y-s,value(d,s,y),bh,dv,lv[1],rearEq[2]]
    return generic,raw,pivots,L,legs

def beam(i,j,l):
    if i>j and j<=l<i:return Q(1,i+j-l)
    if j>i and i<=l<j:return -Q(1,i+j-l)
    return Q(0)

def projection(sign):
    generic,raw,guards,L,legs=arith_pencil(sign)
    pegs,q,p,R,RY=generic
    P6=[1]
    for w in pegs:P6=mul(P6,[-w,1])
    def B(k,Lj,d):
        return sum(r*sum(u*beam(i+k,j,d) for j,u in enumerate(Lj)) for i,r in enumerate(P6))
    for k in range(3):
        for Lj in legs:
            for d0 in range(5,8):
                assert B(k,Lj,d0)==0
    columns=[[sum(L[j]*B(k,legs[j],d) for j in range(3)) for d in range(5)] for k in range(3)]
    columns.append(mul(q,q))
    mat=list(map(list,zip(*columns)))
    minor3={ix:det([mat[i][:3] for i in ix]) for ix in combinations(range(5),3)}
    minors=[]
    for ix in combinations(range(5),4):
        minors.append(sum((-1)**(3+j)*mat[i][3]*minor3[ix[:j]+ix[j+1:]]
                          for j,i in enumerate(ix)))
    D=gcds([normP(x) for x in minors])
    base=sf(reduce(lambda a,b:a*b,[normP(g)*denomP(g) for g in guards]))
    assert D and sf(D).degree()==46
    # Norms and profile coefficients are regular outside the actual pivot support.
    for u in tuple(guards)+pegs+tuple(q)+tuple(p)+tuple(minors)+(R.c0,R.c1,RY.c0,RY.c1):
        assert stripq(denomP(u),base).degree()==0
    for u in minors:
        assert stripq(denomP(evalnorm(u)),base).degree()==0
    assert stripq(sf(D),base).degree()==0
    unit,fac=base.factor()
    check=P(unit)
    factors=[]
    for mod,e in fac:
        check*=mod**e
        factors.append(mod/mod.leading_coefficient())
    assert check==base and base.degree()==108
    print("arithmetic guarded degrees",sign,D.degree(),[m.degree() for m in factors],flush=True)
    return factors,generic,raw
