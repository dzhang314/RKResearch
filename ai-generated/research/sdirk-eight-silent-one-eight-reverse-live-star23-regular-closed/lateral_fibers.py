"""Actual fifth and exact physical guards for the single representative silent-two orientation."""
from star4_actual_fifth import *
from regular_star_projection import raw,profile,red,Co,con,ev
from quadratic_poly import E
from check_star_family import F as ExField
from flint import fmpq_poly,fmpq,nmod_poly
from time import perf_counter
from functools import lru_cache

@lru_cache(None)
def lateral_model():
    P,Q,A,B,_=raw(True,2)
    HH,_,V,D,(a,b,q,La,Lb,A0,B0)=profile(True)
    H,div=common_division([*HH,red(D*V)],[g,La,Lb])
    delta=H.pop()
    (A,B),ds=common_division([A,B],[g,La,Lb])
    assert div==ds==[1,1,1]
    x=1-g
    return P,Q,A,B,H,delta,(a,b,q,A0,B0,x,La,Lb)

def fifth_lateral(K,gs,S,p,t):
    P,Q,AA,BB,H,D0,dat=lateral_model()
    U=Tower(S);ss=U.gen();ga=U(gs)
    get=lambda P:lv(P,U,ga,ss,p,t)
    x,p1,q,a,b,A,B,delta=map(get,(dat[5],dat[1],dat[2],dat[3],dat[4],AA,BB,D0))
    hh=[get(x0) for x0 in H]
    ZZ=[h*ga**i for i,h in enumerate(hh)]
    H4=[cv(U,k) for k in pol(h4(True),lambda x:x)]
    hs=pe(H4,ss);ha,hb=(a-1)/2,(b-1)/2
    E5=with_p_supp(U,a,b,ss,ZZ,delta,ha,hb,hs)
    m=1-2*ga
    # Physical two is silent, physical three and four ordinary.
    E=mul(nodal([p1,q,x]),[B*m*m+ga*ga*A,-2*m*B,B])
    M=ccols(E,hh,U)
    W=S
    for I in combinations(range(4),3):
        zz=padded([w*ga**j for j,w in enumerate(cofactors(M,I,U))],E5,U)
        W=gcdp(W,zz.x)
        if len(W)<=1:break
    return W

def gpoly(P):
    cf={}
    for (iv,is0,ig,it),a in P.to_dict().items():
        assert iv==is0==0 and it<=1
        cf[ig,it]=a
    m=max((i for i,_ in cf),default=-1)
    return E(fmpq_poly([cf.get((i,0),0) for i in range(m+1)]),
             fmpq_poly([cf.get((i,1),0) for i in range(m+1)]))

@lru_cache(None)
def attributes():
    P,Q,A,B,H,D,(a,b,q,A0,B0,x,La,Lb)=lateral_model()
    m=1-2*g
    cc=lambda z:red(B*(z-m)**2+g*g*A)
    J=[
      ('scale',D),
      ('earlier_clocks',red((s-A0)*(s-B0))),
      ('terminal_q',x-q),
      ('quintic',H[-1]),
      ('terminal_h',ev(H,x)),
      ('B',B),
      ('w0',A),('w1',red(A+B)),('w2',red(A+2*B)),
      ('rear_a',cc(a)),('rear_b',cc(b)),('rear_q',cc(q)),
    ]
    gg=[('gamma',g),('early_gauss_a',La),('early_gauss_b',Lb),('terminal_a',x-a),('terminal_b',x-b)]
    F0,F1=[tuple(gpoly(e) for e in Co(Z1,1)) for Z1 in (P,Q)]
    return F0,F1,[(nm,gpoly(v)) for nm,v in gg],[(name,tuple(gpoly(e) for e in Co(v,1))) for name,v in J]

def norm(a,p):return int(a.p)*pow(int(a.q),-1,p)%p

def modcoef(v,K,gg,p,t):
    w=K(0);r=v.v
    for i in range(r.degree(),-1,-1):
        w=w*gg+(norm(r.a[i],p)+t*norm(r.b[i],p))%p
    return w

def modgamma(M,p,t):
    D=Bfield(nmod_poly([0,1],p),p,t)
    F=D.cast(M)
    assert F.degree()==M.degree() and F.leading_coefficient()==1
    return F

def direct(M,p,t,guarded=None,verbose=False):
    P,Q,*_=lateral_model()
    FF=modgamma(M,p,t);counts=0;remaining=[]
    for T,e in FF.factor()[1]:
        K=Bfield(T,p,t);gg=K(nmod_poly([0,1],p))
        if guarded is None:
            PP=sv(P,K,gg,p,t);QQ=sv(Q,K,gg,p,t)
            if len(PP)!=10 and len(QQ)!=27:
                remaining.append((T.degree(),-1,-1))
                continue
        else:
            PP=[modcoef(v,K,gg,p,t) for v in guarded]
            assert PP and PP[-1]==1
            QQ=sv(Q,K,gg,p,t)
        W=gcdp(PP,QQ)
        if len(W)<=1:counts+=1;continue
        D=fifth_lateral(K,gg,W,p,t)
        if len(D)>1:remaining.append((T.degree(),len(W)-1,len(D)-1))
        else:counts+=1
    if verbose or not remaining:print('lateral exact candidate reduction',M.degree(),p,t,counts,remaining,flush=True)
    return not remaining,counts


PLAN={
    (326,1):(326,None,0,9),
    (24,3):(12,'scale',3,3),
    (2,6):(1,'terminal_a',0,0),
    (18,6):(9,'rear_a',3,3),
    (27,12):(27,'terminal_h',3,4),
    (4,14):(4,'scale',3,2),
    (2,15):(2,'scale',3,2),
    (1,20):(1,'rear_a',3,1),
    (21,48):(21,'quintic',3,2),
    (1,48):(1,'B',6,1),
    (4,54):(4,'identical_w2',0,0),
    (3,60):(3,'B',2,1),
}

def one_factor(J,M,e,p,t):
    d=M.degree()
    dm,guard,n0,ncomp=PLAN[d,e]
    if dm<d:
        assert not M.b
        G=M.gcd(E(J.a%M.a,J.b%M.a))
        assert G.degree()==dm and G.lc()==E(1)
        print('exact orientation support',d,e,dm,flush=True)
        M=G
    if guard is None:
        ok,n=direct(M,p,t)
        assert ok and n==ncomp
        return
    P0,Q0,G0,S0=attributes();K=ExField(M)
    if guard=='terminal_a':
        assert not K(dict(G0)[guard])
        print('exact orientation forces terminal/literal collision',d,e,flush=True)
        return
    if guard=='identical_w2':
        assert not trim(list(map(K,dict(S0)['w2'])))
        print('exact orientation forces forbidden square gap two',d,e,flush=True)
        return
    P=trim(list(map(K,P0)))
    assert P
    G=trim(list(map(K,dict(S0)[guard])))
    assert G
    n=0
    while len(P)>1:
        H=gcdp(P,G)
        if len(H)<=1:break
        A,R=qr(P,H);assert not R and A
        n+=len(H)-1;P=A
    assert n==n0
    print('exact physical fourth guard',d,e,guard,n,len(P)-1,flush=True)
    W=sc(P,P[-1].inv())
    ok,n=direct(M,p,t,W)
    assert ok and n==ncomp
