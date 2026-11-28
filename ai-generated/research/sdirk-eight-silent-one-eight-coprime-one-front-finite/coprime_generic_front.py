"""Literal profile of one-active-front coprime branch, with actual Gaussian terminal."""
from shared_one_front_projection import *
from time import perf_counter

def L(X):return can(sum(x*X**j for j,x in enumerate(LM)))

@lru_cache(None)
def setup_front(front,slot):
    A,B,m=map(lambda w:cv(F2,w),ends(front,1))
    ha,hb=(A-1)/2,(B-1-m)/2
    active,quiet,H=(A,B,ha) if slot==0 else (B,A,hb)
    al,bl,af=map(expr,(A,B,active))
    H4=[cv(F2,v) for v in pol(h4(front),lambda z:z)]
    S0,_,S1,QT,QA=context(F2,A,B,m,ha,hb,None,H4)
    hs=term(H4,s)
    diag=g
    La,Ls=L(diag*af),L(diag*s)
    q0=can(s*hs*La-af*expr(H)*Ls)
    q1=can(expr(H)*Ls-hs*La)
    Q=can(q0+q1*y)
    N0=can(expr(H)*(s-af)*L(diag*y))  # common H4 canceled from E_T, E_A
    m0=s-1-2*hs;m1=s*s/2-s-2*hs
    aa=(bl*m0-m1)*expr((B-A).inv());bb=m0-aa
    rowT=can(s**3-s**4/4+2*hs+aa*al**3+bb*bl**3)
    rowA=can(hs+aa*expr(ha)+bb*expr(hb))
    def cfield(poly):
        z=[]
        for f in co(poly,1):
            pairs={}
            for (iy,is0,ig,ir,it),w in f.to_dict().items():
                assert iy==is0==ig==ir==0
                pairs[it]=w
            from check_star_family import E as QqE
            z.append(F2(QqE(FlP([pairs.get(0,0)]),FlP([pairs.get(1,0)]))))
        return z
    assert len(gcdp(H4,cfield(rowA)))==1
    qt,qa=ev(QT,active),ev(QA,active)
    Xt,rem=exdiv(can(rowT-expr(qt)*hs),s-af);assert not rem
    Xa,rem=exdiv(can(rowA-expr(qa)*hs),s-af);assert not rem
    M0=y-1;M1=y*y/2-y;M2=y**3/3-y*y
    J0=M2-(al+bl)*M1+al*bl*M0
    T0=can(y**3-y**4/4+(al+bl)*M2-al*bl*M1+s*J0)
    A0=can(expr(S0[0])*M0+expr(S0[1])*M1+term(S1,s)*J0)
    j=-F2(4)/3+2*(A+B)-2*A*B
    DT=term([2-F2(4)/3*(A+B)+2*A*B,j],s)
    DA=expr(1-2*S0[0]-2*S0[1])+term(S1,s)*expr(j)
    T1=can(hs*(DT-expr(qt))-Xt*(y-af))
    A1=can(hs*(DA-expr(qa))-Xa*(y-af))
    Et=can(T0*Q+T1*N0);Ea=can(A0*Q+A1*N0)
    Et,b=exdiv(Et,(y-af)*(y-s));assert not b
    Ea,b=exdiv(Ea,(y-af)*(y-s));assert not b
    assert Et.degrees()[0]==Ea.degrees()[0]==3
    dres=can(sum(c*(-diag*q0)**i*q1**(4-i) for i,c in enumerate(LM)))
    cond=[g,hs,s-al,s-bl,La,Ls,q1,dres]
    W=can(Et.resultant(Ea,0))
    exact=[can(a0) for a0 in cond]
    # The coprimality guard is normalized by already nonzero factors;
    # its roots are unchanged at actual candidates.
    coprime,powers=strip_known(exact[-1],exact[:-2])
    R,pw=strip_known(W,exact[:-1]+[coprime])
    assert (W.degrees()[1:3],R.degrees()[1:3])==((21,24),(7,12))
    print('coprime generic fifth s/g',front,slot,W.degrees(),R.degrees(),pw,flush=True)
    return Et,Ea,R,q0,q1,exact+[coprime],(A,B,m,ha,hb,active,quiet,H,H4)


def conj(X):
    return CX.from_dict({(i,j,k,n,l):(-1)**l*a0 for (i,j,k,n,l),a0 in X.to_dict().items()})


def strip_known(X,guards):
    counts=[]
    for A in guards:
        power=0
        if not A or not any(A.degrees()):
            counts.append(power);continue
        B=conj(A);N=can(A*B)
        assert not N.degrees()[-1]
        while True:
            P,e=divmod(can(X*B),N)
            if e:break
            X=can(P);power+=1
        counts.append(power)
    return X,counts
