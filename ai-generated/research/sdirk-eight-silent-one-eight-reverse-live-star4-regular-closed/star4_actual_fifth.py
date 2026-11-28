"""Actual fifth cofactor family without a divided gap slope or actual pivot."""
from regular_star_projection import raw,profile,red,ev,g,s,Z,C,con,Co
from unequal_finite import Bfield,Tower,gcdp,trim
from off8_fibers import ev as pe,add,mul,sc,qr,nodal,det
from seven_k0_anchors import pol,h4,F2,cv
from flint import nmod_poly
from itertools import combinations
from functools import lru_cache

def data(p,t):
    P,Q,A,B,guards=raw(True,4)
    H,PP,V,delta,(a,b,q,La,Lb,A0,B0)=profile(True)
    x=1-g
    return P,Q,A,B,H,delta,V,(a,b,q,A0,B0,La,Lb,x)

def ncoeff(expr,p,t):
    rows={}
    for (i,j,k,l),w in expr.to_dict().items():
        assert i==0
        z=int(w.p)*pow(int(w.q),-1,p)%p
        rows[k,j]=(rows.get((k,j),0)+z*pow(t,l,p))%p
    return rows

def sv(P,K,x,p,t):
    S={}
    xp=[]
    for (k,j),a in ncoeff(P,p,t).items():
        while len(xp)<=k:xp.append(x**len(xp))
        S[j]=S.get(j,K(0))+K(a)*xp[k]
    return trim([S.get(j,K(0)) for j in range(max(S,default=-1)+1)])

def lv(P,K,x,s0,p,t):
    return sum((a*s0**j for j,a in enumerate(sv(P,K,x,p,t))),K(0))

def moment(P,K):
    return [sum(P[j]/(j-i) for j in range(i+1,len(P))) for i in range(len(P)-1)]
def bcol(A,H,K):
    W=moment(A,K);V=moment(H,K)
    S=add(mul(H,W),sc(mul(A,V),-1))
    assert len(S)<=5
    return (S+[K(0)]*5)[1:5]
def ccols(E,H,K):
    return [bcol([K(0)]*i+E,H,K) for i in range(4)]
def cofactors(J,I,K):
    return [(-1)**(3+j)*det([[J[k][i] for k in range(4) if k!=j] for i in I]) for j in range(4)]
def padded(P,Q,K):
    n,m=3,6
    z=K(0)
    assert len(P)<=n+1 and len(Q)<=m+1
    P=P+[z]*(n+1-len(P));Q=Q+[z]*(m+1-len(Q))
    A=[[z]*i+P+[z]*(m-1-i) for i in range(m)]
    A += [[z]*i+Q+[z]*(n-1-i) for i in range(n)]
    @lru_cache(None)
    def f(i,M):
        if not M:return K(1)
        v=z;sg=1
        for j,c in enumerate(A[i]):
            if M>>j&1:
                if c:v+=sg*c*f(i+1,M^(1<<j))
                sg=-sg
        return v
    return f(0,(1<<(n+m))-1)

def common_division(H,guess):
    L=list(H);out=[]
    for v in guess:
        d=red(v*con(v));w=con(v);k=0
        assert d
        while True:
            Q=[]
            for p in L:
                a,b=divmod(red(p*w),d)
                if b:break
                Q.append(red(a))
            else:L=Q;k+=1;continue
            break
        out.append(k)
    return L,out

@lru_cache(None)
def exact_model():
    P,Q,A,B,H,delta,V,(a,b,q,A0,B0,La,Lb,x)=data(None,None)
    H,guards=common_division([*H,red(delta*V)],[g,La,Lb])
    delta=H.pop()
    (A,B),guards0=common_division([A,B],[g,La,Lb])
    assert H and delta and A and B and guards==guards0==[1,1,1]
    print('exact common gauge removed before independent cofactors',guards,guards0,flush=True)
    return P,Q,A,B,H,delta,(a,b,q,A0,B0,x)

def with_p_supp(K,a,b,s,H,delta,h_a,h_b,h_s):
    # Actual fourth; its predecessor Vandermonde uses only literal (b-a).
    z0=s-1-2*h_s;z1=s*s/2-s-2*h_s
    wt_a=(b*z0-z1)/(b-a);wt_b=z0-wt_a
    As=h_s+wt_a*h_a+wt_b*h_b
    Ts=s**3-s**4/4+2*h_s+wt_a*a**3+wt_b*b**3
    Ta=a**3-a**4/4+a-1;Tb=b**3-b**4/4+b-1
    J=[[h_a,a*h_a,h_a,Ta],[h_b,b*h_b,h_b,Tb],[h_s,s*h_s,As,Ts]]
    C0=[(-1)**(i+3)*det([[v for j,v in enumerate(row) if i!=j] for row in J]) for i in range(4)]
    # No inverse of the candidate fourth collision nor the profile scale.
    DD=(b-a)*(s-a)*(s-b)
    M0=add([K(-1)*delta,delta],sc(H,-2))
    M1=add([K(0),-delta,delta/2],sc(H,-2))
    M2=add([K(0),K(0),-delta,delta/3],sc(H,-K(4)/3))
    MMM=(M0,M1,M2)
    basis=[sc(nodal([b,s]),s-b),sc(nodal([a,s]),a-s),sc(nodal([a,b]),b-a)]
    def tsum(T):
        K0=[]
        for z in T:K0=add(K0,z)
        return K0
    taps=[tsum(sc(M,w) for M,w in zip(MMM,tt)) for tt in basis]
    CH=sc(H,DD)
    Ah=tsum([CH]+[sc(v,hv) for v,hv in zip(taps,(h_a,h_b,h_s))])
    TT=tsum([[K(0),K(0),K(0),DD*delta,-DD*delta/4],sc(CH,2)]+[sc(v,vv**3) for v,vv in zip(taps,(a,b,s))])
    return tsum(sc(f,c) for f,c in zip((CH,[K(0)]+CH,Ah,TT),C0))

def tests_in_s(K,gs,S,p,t):
    P,Q,AA,BB,H,D0,dat=exact_model()
    U=Tower(S);ss=U.gen();ga=U(gs)
    get=lambda P:lv(P,U,ga,ss,p,t)
    x,p0,p1,a,b,A,B,delta=map(get,(dat[-1],dat[0],dat[1],dat[3],dat[4],AA,BB,D0))
    hh=[get(x0) for x0 in H]
    ZZ=[h*ga**i for i,h in enumerate(hh)]
    H4=[cv(U,k) for k in pol(h4(True),lambda x:x)]
    hs=pe(H4,ss);ha,hb=(a-1)/2,(b-1)/2
    E5=with_p_supp(U,a,b,ss,ZZ,delta,ha,hb,hs)
    m=1-2*ga
    # Star pegs are never ordered in this nodal identity.
    E=mul(nodal([p0,p1,x]),[B*m*m+ga*ga*A,-2*m*B,B])
    M=ccols(E,hh,U)
    vals=[padded([w*ga**j for j,w in enumerate(cofactors(M,II,U))],E5,U)
          for II in combinations(range(4),3)]
    W=S
    for r in vals:
        W=gcdp(W,r.x)
    return W
