"""Whole exact oriented fibres and actual ordinary fifth polynomial."""
from arith_literal_diagonal import reconstruct
from arith_star_model import quartic_model,literal_fifth_poly
from arith_star_fibers import gpoly,modgamma,norm
from paired_proposals import recover,mod_poly,fast_guard,prime_series,reduced_support
from regular_star_projection import raw,red,Co,ev,det as mdet,W,nodal as mN,mul as mm,cof,Z,g,s
from star4_actual_fifth import Bfield,Tower,sc,qr,pe,trim,nodal,mul,ccols,cofactors,sv,lv,nmod_poly,gcdp,combinations,det
from quadratic_poly import E
from check_star_family import F as ExField,Split
from functools import lru_cache
from flint import fmpq_poly
from collections import Counter

@lru_cache(None)
def orient(slot):
    A,B=reconstruct(slot)
    return E(fmpq_poly(A),2*fmpq_poly(B))

def fast_orientation(M,n,slot,place=(1129,203)):
    J=orient(slot)
    assert not M.b and n<=M.degree()
    J=E(J.a%M.a,J.b%M.a)
    def trial(p,t):
        A=modgamma(M,p,t)
        U=mod_poly(J,p,t)
        G=A.gcd(U)
        if G.degree()!=n:return []
        return [int(G[i]) for i in range(n)]
    def verify(A,B):
        S=E(fmpq_poly([*A,1]),fmpq_poly(B))
        if M%S or J%S:return None
        Q=M.exact(S)
        p,t=place
        R=modgamma(Q,p,t)
        U=mod_poly(J,p,t)
        if R.gcd(U).degree()!=0:return None
        return S
    return recover(n,trial,verify,('orientation',slot,M.degree(),n))

@lru_cache(None)
def model(slot):
    Q,R,_,_,_=raw(False,slot)
    _,AB,H,delta,dat,_=quartic_model()
    a,b,q,La,Lb,a0,b0,m0,x,m=dat
    p=[a,b,q]
    z=p.pop(slot-2)
    return Q,R,AB,H,delta,dat,p,z

@lru_cache(None)
def nodal_lead(slot):
    P,Q,(A,B),H,D,dat,p,z=model(slot)
    x,m=dat[-2:]
    E=mm(mN([*p,x]),[B*m*m+g*g*A,-2*m*B,B]);HH=W(H)
    M=[]
    for j in range(3):
       F=[Z]*j+E;U=W(F)
       M.append([red(cof(H,U,i)-cof(F,HH,i)) for i in range(2,5)])
    return mdet(M)

@lru_cache(None)
def guards(slot):
    P,Q,(A,B),H,D,dat,pp,z=model(slot)
    a,b,q,La,Lb,a0,b0,m0,x,m=dat
    cv=lambda v:red(B*(v-m)**2+g*g*A)
    S=[
        ('scale',D),('earlier',red((s-a0)*(s-b0))),('terminal_q',x-q),
        ('quintic',H[-1]),('terminal_h',ev(H,x)),('nodal_lead',nodal_lead(slot)),
        ('B',B),('w0',A),('w1',red(A+B)),('w2',red(A+2*B)),
        ('rear_a',cv(a)),('rear_b',cv(b)),('rear_q',cv(q)),
    ]
    GG=[('gamma',g),('early_gauss_a',La),('early_gauss_b',Lb),('terminal_a',x-a),('terminal_b',x-b)]
    F0=[tuple(gpoly(e) for e in Co(v,1)) for v in (P,Q)]
    return F0,[(name,gpoly(v)) for name,v in GG],[(name,tuple(gpoly(e) for e in Co(v,1)),v) for name,v in S]

def padded(P,Q,K):
    n,m=3,3;z=K(0)
    assert len(P)<=n+1 and len(Q)<=m+1
    P=P+[z]*(n+1-len(P));Q=Q+[z]*(m+1-len(Q))
    A=[[z]*i+P+[z]*(m-1-i) for i in range(m)]
    A += [[z]*i+Q+[z]*(n-1-i) for i in range(n)]
    @lru_cache(None)
    def f(i,M):
        if not M:return K(1)
        a=z;sg=1
        for j,c in enumerate(A[i]):
            if M>>j&1:
                if c:a+=sg*c*f(i+1,M^(1<<j))
                sg=-sg
        return a
    return f(0,(1<<(n+m))-1)

def fifth_tests(slot,K,gs,S,p,t):
    P,Q,(As,Bs),H,D,dat,pegs,z=model(slot)
    U=Tower(S);ss=U.gen();ga=U(gs)
    get=lambda v:lv(v,U,ga,ss,p,t)
    A,B,x,m=map(get,(As,Bs,*dat[-2:]))
    hs=list(map(get,H))
    E=mul(nodal([*map(get,pegs),x]),[B*m*m+ga*ga*A,-2*m*B,B])
    J=ccols(E,hs,U)
    F=list(map(get,Co(literal_fifth_poly(),0)))
    G=S
    for I in ((1,2,3),(0,1,2),(0,1,3),(0,2,3)):
        T=[w*ga**j for j,w in enumerate(cofactors(J,I,U))]
        N=padded(T,F,U)
        G=gcdp(G,N.x)
        if len(G)==1:break
    return G

def all_mod(slot,M,p,t,guarded=None,verbose=False,probe_guard=False):
    P,Q,*_=raw(False,slot);J=orient(slot)
    F=modgamma(M,p,t); ans=[];bad=[];gu={}
    for T,e in F.factor()[1]:
        K=Bfield(T,p,t);gg=K(nmod_poly([0,1],p))
        if K(J):
            ans.append('orientation');continue
        A=sv(P,K,gg,p,t);B=sv(Q,K,gg,p,t)
        if guarded is None:
            if len(A)!=P.degrees()[1]+1 and len(B)!=Q.degrees()[1]+1:
                bad.append((T.degree(),'s_leading',len(A)-1,len(B)-1));continue
            W=A if len(A)==P.degrees()[1]+1 else B
        else:
            W=[K(v.v) for v in guarded]
            assert W and W[-1]==1
        W=gcdp(gcdp(W,A),B)
        assert W
        if len(W)==1:
            ans.append('no_s');continue
        Y=fifth_tests(slot,K,gg,W,p,t)
        if len(Y)==1:
            ans.append('fifth');continue
        bad.append((T.degree(),len(W)-1,len(Y)-1))
        if probe_guard:
            for nm,_,v in guards(slot)[2]:
                m=len(gcdp(Y,sv(v,K,gg,p,t)))-1
                if m>0:gu[nm]=gu.get(nm,0)+m
    print('literal actual complete components',slot,M.degree(),p,t,dict(Counter(ans)),'open',bad,'suggest',gu,flush=True)
    return not bad,Counter(ans),bad,gu
