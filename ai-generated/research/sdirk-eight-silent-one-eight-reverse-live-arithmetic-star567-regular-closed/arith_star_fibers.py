"""Complete local fifth gates for actual arithmetic-front/star-rear placements."""
from arith_star_model import quartic_model,two_remainders,literal_fifth_poly
from arith_star_diagonal import reconstruct
from regular_star_projection import Co,red,ev,g,s,con
from star4_actual_fifth import Bfield,Tower,pe,lv,sv,sc,qr,trim,add,mul,nodal,det,gcdp,nmod_poly
from quadratic_poly import E
from check_star_family import F as ExField
from flint import fmpq_poly
from math import comb
from functools import lru_cache

def gpoly(P):
    cf={}
    for (iv,is0,ig,it),a in P.to_dict().items():
        assert iv==is0==0 and it<=1
        cf[ig,it]=a
    m=max((i for i,_ in cf),default=-1)
    return E(fmpq_poly([cf.get((i,0),0) for i in range(m+1)]),
             fmpq_poly([cf.get((i,1),0) for i in range(m+1)]))

def norm(a,p):return int(a.p)*pow(int(a.q),-1,p)%p

def modgamma(M,p,t):
    D=Bfield(nmod_poly([0,1],p),p,t)
    F=D.cast(M)
    assert F.degree()==M.degree() and F.leading_coefficient()==1
    return F

@lru_cache(None)
def orient():
    A,B=reconstruct()
    return E(fmpq_poly(A),2*fmpq_poly(B))

@lru_cache(None)
def guards():
    P,Q=two_remainders()
    R,(A,B),H,D,dat,base=quartic_model()
    a,b,q,La,Lb,a0,b0,m0,x,m=dat
    GG={name:tuple(gpoly(e) for e in Co(v,1)) for name,v in (
        ('nodal_lead',R[-1]),('quintic',H[-1]),('B',B),
    )}
    P0=tuple(gpoly(e) for e in Co(P,1))
    return P0,GG

def ress(P,Q,K):
    n,m=2,3;z=K(0)
    assert len(P)<=n+1 and len(Q)<=m+1
    P=P+[z]*(n+1-len(P));Q=Q+[z]*(m+1-len(Q))
    A=[[z]*i+P+[z]*(m-1-i) for i in range(m)]
    A += [[z]*i+Q+[z]*(n-1-i) for i in range(n)]
    return det(A)

def gates_in_s(K,gs,S,p,t):
    R,(A0,B0),H,D,dat,GG=quartic_model()
    F=literal_fifth_poly()
    U=Tower(S);ss=U.gen();ga=U(gs)
    get=lambda v:lv(v,U,ga,ss,p,t)
    R=list(map(get,R));A=get(A0);B=get(B0)
    h=list(map(get,H));F=[get(v) for v in Co(F,0)]
    x=1-ga;m=1-2*ga
    V=[-m,ga]
    Q=add(sc(mul(V,V),B*R[4]),sc(V,B*R[3]))
    Q=add(Q,[B*R[2]-ga**2*A*R[4]])
    ordinary_gate=ress(Q,F,U)
    read=[sum((h[i]*comb(i,j)*m**(i-j)*ga**j for i in range(j,6)),U(0)) for j in (0,2,4)]
    E0=B**2*read[0]-A*B*read[1]+A**2*read[2]
    K0=B*(2*B+A)*pe(h,x);N=m*K0-x*E0;Den=ga*(K0-E0)
    silent_gate=sum((f*N**i*Den**(3-i) for i,f in enumerate(F)),U(0))
    return gcdp(S,silent_gate.x),gcdp(S,ordinary_gate.x)

def modco(v,K,gg,p,t):
    return K(v.v)

def all_mod(M,p,t,guarded=None):
    P,Q=two_remainders()
    FF=modgamma(M,p,t)
    ans=[];bad=[]
    Or=orient()
    for T,e in FF.factor()[1]:
        K=Bfield(T,p,t);gg=K(nmod_poly([0,1],p))
        if K(Or):
            ans.append('orientation');continue
        PP=sv(P,K,gg,p,t);QQ=sv(Q,K,gg,p,t)
        if guarded is None:
            if len(PP)!=9 and len(QQ)!=15:
                bad.append((T.degree(),'s_leading',len(PP)-1,len(QQ)-1));continue
            W=PP if len(PP)==9 else QQ
        else:
            W=[K(v.v) for v in guarded]
            assert W and W[-1]==1
        W=gcdp(gcdp(W,PP),QQ)
        assert W
        if len(W)<=1:
            ans.append('no_s');continue
        C,D=gates_in_s(K,gg,W,p,t)
        if len(C)==len(D)==1:
            ans.append('both_fifths');continue
        bad.append((T.degree(),len(W)-1,len(C)-1,len(D)-1))
    from collections import Counter
    print('actual complete local fibres',M.degree(),p,t,dict(Counter(ans)),'not done',bad,flush=True)
    return not bad,Counter(ans),bad
