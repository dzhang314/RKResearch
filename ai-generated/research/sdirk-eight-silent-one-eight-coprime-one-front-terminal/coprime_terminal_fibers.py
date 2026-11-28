"""Six-peg rational moment Bézout mask at an actual Gaussian terminal."""
from coprime_terminal_projection import *
from shared_one_front_fibers import ev_poly,root_consts
from unequal_finite import Bfield,Tower,moment
from equal_undetected_front import Nested
from extra_active import invpoly
from gauss_separate import span_unit
from flint import nmod_poly
from itertools import combinations

def mask(K,rr,q,pegs):
    m0,m1,m2,m3=moment(K,pegs,q,4)
    U=[m1*m3-m2*m2,m1*m2-m0*m3,m0*m2-m1*m1]
    L=mon(list(map(K,Lco)))
    W=[sum(L[j]/(j-i) for j in range(i+1,5)) for i in range(4)]
    WL=invpoly(K,W,L)
    D=nodal(pegs)
    X=qr(mul(D,U),L)[1]
    Y=qr(mul(mul([-rr,K(1)],mul(q,q)),WL),L)[1]
    X += [K(0)]*(4-len(X));Y += [K(0)]*(4-len(Y))
    return U,[X[i]*Y[j]-X[j]*Y[i] for i,j in combinations(range(4),2)]

def padded_res(A,B,K):
    assert len(A)<=3 and len(B)<=6
    z=K(0)
    A=A+[z]*(3-len(A));B=B+[z]*(6-len(B))
    rows=[[z]*i+A+[z]*(4-i) for i in range(5)]
    rows += [[z]*i+B+[z]*(1-i) for i in range(2)]
    return det(rows)

def physical_sixth(K,ga,A,B,m,ha,hb,a,Hact,H4,s,y,Q):
    S0,AA,e,QT,QA=context(K,A,B,m,ha,hb,None,H4)
    hs=ev(H4,s);delta=hs*(s-a)
    m0=s-1-2*hs;m1=s*s/2-s-2*hs
    xa=(B*m0-m1)/(B-A);xb=m0-xa
    tv=s**3-s**4/4+2*hs+xa*A**3+xb*B**3
    av=hs+xa*ha+xb*hb
    qT,qA=ev(QT,a),ev(QA,a)
    uu,vv=tv-qT*hs,av-qA*hs
    MT=[delta*qT-a*uu,uu];MA=[delta*qA-a*vv,vv]
    C=[K(w)*ga**j*delta*Hact for j,w in enumerate(Lco)]
    M0=sc(add(mul(Q,[K(-1),K(1)]),sc(C,-2)),delta)
    M1=sc(add(mul(Q,[K(0),K(-1),K(1)/2]),sc(C,-2)),delta)
    M2=sc(add(mul(Q,[K(0),K(0),K(-1),K(1)/3]),sc(C,-K(4)/3)),delta)
    M3=add(sc(mul(Q,[K(0),K(0),K(0),K(-1),K(1)/4]),delta),mul(add(MT,[-2*delta]),C))
    HH=add(S0,sc(AA,ev(e,s)));F3=nodal([A,B,s])
    M=(M0,M1,M2,M3)
    DA=add(mul(add(MA,[-delta]),C),sc(sum_poly([sc(x,w) for x,w in zip(M,HH)]),-1))
    VR=sum_poly([sc(x,w) for x,w in zip(M,F3)])
    qy,cy=ev(Q,y),ev(C,y)
    return add(sc(DA,ev(F3,y)*qy),sc(VR,ev(HH,y)*qy-cy))

def keep_leading_unit(Pa,Pb,K,d):
    cand=[P for P in (Pa,Pb) if len(P)==d+1]
    if len(Pa)==len(Pb)==d+1:
        cand += [add(Pa,sc(Pb,K(i))) for i in range(1,8)]
    for P in cand:
        if len(P)!=d+1:continue
        try:P[-1].inv()
        except ArithmeticError:continue
        return P
    raise ArithmeticError(('fifth leading',len(Pa)-1,len(Pb)-1,d))

def test(front,slot,rear,p,t,verbose=False):
    G,Et,Ea,F1,F2a,Q=setup(front,slot)
    q0,q1,La,Ls,cond,A,B,m,active,H,H4=Q
    c0,c1=coF(q0,1),coF(q1,1)
    C0=coF(La,1)[0]
    roots=root_consts(p);assert roots is not None
    counts=[0]*3
    Fpoly=F1 if rear else F2a
    for rr in roots:
        Rbase=Bfield(nmod_poly([-rr,1],p),p,t)
        s0=nmod_poly([int(Rbase(q).x[0]) for q in G],p)
        assert s0.degree()==len(G)-1 and s0.leading_coefficient()==1
        for Mf,e in s0.factor()[1]:
            K=Bfield(Mf,p,t);ss=K(nmod_poly([0,1],p));ga=K(1-rr)
            rc=lambda a:K(int(Rbase(a).x[0]))
            rc(C0).inv()
            Ld=ev_poly(Fpoly,0,K,p,rr,t,ga,ss)
            assert len(Ld)==(3 if rear else 6)
            Ld[-1].inv()
            A0,B0=ev_poly(Et,0,K,p,rr,t,ga,ss),ev_poly(Ea,0,K,p,rr,t,ga,ss)
            T=keep_leading_unit(A0,B0,K,3)
            S=gcdp(gcdp(T,A0),B0)
            counts[0]+=1
            if len(S)<=1:continue
            counts[1]+=1
            Y=Tower(S);y0=Y.gen()
            U=Nested(mon(list(map(Y,Ld))));uu=U.gen()
            Hg=U(Y(ga));hh=U(Y(ss));yy=U(y0);Rr=U(Y(K(rr)))
            a0=U(Y(K(active)))
            c=Rr-Hg*uu
            d=Rr-Hg*(2-uu if rear else 2*uu)
            rf=[Hg*U(Y(ev(list(map(rc,c0)),ss))),U(Y(ev(list(map(rc,c1)),ss)))]
            pegs=[Hg*a0,Hg*hh,Hg*yy,Rr,c,d]
            if verbose:print('coprime terminal candidate',front,slot,rear,p,t,rr,Mf.degree(),len(S)-1,flush=True)
            poly,res=mask(U,Rr,rf,pegs)
            try:span_unit(U,*res)
            except ArithmeticError:
                cv0=lambda x:U(Y(K(x)))
                ha,hb=(A-1)/2,(B-1-m)/2
                qn=[U(Y(ev(list(map(rc,c0)),ss))),rf[1]]
                G6=physical_sixth(U,Hg,*map(cv0,(A,B,m,ha,hb,active,H)),
                                  list(map(cv0,H4)),hh,yy,qn)
                Y6=[w*Hg**i for i,w in enumerate(poly)]
                span_unit(U,*res,padded_res(Y6,G6,U))
                if verbose:print('literal sixth needed',front,slot,rear,rr,Mf.degree(),flush=True)
            counts[2]+=1
    return tuple(counts)
