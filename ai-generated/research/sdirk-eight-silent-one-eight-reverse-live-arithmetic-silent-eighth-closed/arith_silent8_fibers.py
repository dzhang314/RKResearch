"""Actual arithmetic third and true distinct fifth/penultimate full fibres."""
from arith_silent8_crt import model
from arith_silent8_diagonal import exact_diagonal
from arith_ordinary_reconstruction import divide_root,extend,reject_chronology
from arith_star_fibers import gpoly,modgamma,norm
from paired_proposals import recover,mod_poly,fast_guard,prime_series,reduced_support
from silent8_fibers import sfactors,getpoly,reverse_arg
from regular_star_projection import Co,red,ev,g,s
from star4_actual_fifth import Bfield,sc,qr,pe,trim,sv,lv,nmod_poly,gcdp
from quadratic_poly import E
from check_star_family import F as ExField,Split
from functools import lru_cache
from flint import fmpq_poly
from collections import Counter

@lru_cache(None)
def orient():
    A,B=exact_diagonal()
    return E(fmpq_poly(A),2*fmpq_poly(B))

@lru_cache(None)
def residue_orientation(p,t):
    return mod_poly(orient(),p,t)

def orientation_for(M,d,place=(1129,203)):
    assert not M.b and d<=M.degree()
    def trial(p,t):
        A=modgamma(M,p,t);U=residue_orientation(p,t)
        G=A.gcd(U)
        if G.degree()!=d:return []
        return [int(G[i]) for i in range(d)]
    def verify(A,B):
        S=E(fmpq_poly([*A,1]),fmpq_poly(B))
        # Keep an exact monic factor covering every actual orientation.
        # It need not itself be proved equal to the exact gcd.
        if M%S:return None
        Q=M.exact(S)
        p,t=place
        R=modgamma(Q,p,t)
        U=residue_orientation(p,t)
        if R.gcd(U).degree()!=0:return None
        return S
    return recover(d,trial,verify,('orientation',M.degree(),d))

@lru_cache(None)
def guards():
    D,J,F,N,G,H,delta,dat=model()
    a,b,q,La,Lb,A0,B0,M0,x,m=dat
    gg0=[('gamma',g),('early_a',La),('early_b',Lb),('terminal_a',x-a),('terminal_b',x-b)]
    gg1=[
        ('scale',delta),('quintic',H[-1]),('terminal_h',ev(H,x)),
        ('nodal_lead',Co(N,0)[-1]),('literal_fourth',red((s-A0)*(s-B0))),
        ('terminal_q',x-q),
    ]
    PP=[tuple(gpoly(e) for e in Co(P,1)) for P in (D,J)]
    return PP,[(n,gpoly(v),v) for n,v in gg0],[(n,tuple(gpoly(e) for e in Co(v,1)),v) for n,v in gg1]

def one_s(K,g0,S,p,t):
    D,J,F,N,G,H,delta,dat=model()
    A,B,M=dat[5:8]
    U,s,E0=extend(K,S);g=E0(g0);x=1-g
    g1,s1=g,s
    f,n,h=map(lambda a:getpoly(a,U,g,s,p,t),(F,N,G))
    if len(n)!=5:return 'nodal_leading',None
    n=sc(n,n[-1].inv())
    r=reverse_arg(h,x,g,U)
    q=gcdp(n,f)
    assert q
    if len(q)==1:return 'no_penultimate',None
    V,u,inc0=extend(U,q)
    n=divide_root(list(map(inc0,n)),u,V)
    j=gcdp(n,list(map(inc0,r)))
    assert j
    if len(j)==1:return 'no_distinct_fifth',None
    W,y,inc1=extend(V,j)
    n=divide_root(list(map(inc1,n)),y,W)
    assert len(n)==3
    X,r0,inc2=extend(W,n)
    lift=lambda z:inc2(inc1(inc0(z)))
    g=lift(g);s=lift(s);u=inc2(inc1(u));y=inc2(y)
    g.inv()
    k=1+2*u-u*u
    xx=1/g-1; zz=xx+k*(u-2)/2
    r1=-inc2(n[1])-r0
    a,b,m0,d=[lift(lv(q0,U,g1,s1,p,t)) for q0 in (A,B,M,delta)]
    H=[lift(lv(q0,U,g1,s1,p,t))/d for q0 in H]
    Y=[X(1),a,b,s,xx-y,xx-r0,xx-r1,zz,xx-u,xx]
    HH=[X(0)]+[pe(H,g*z) for z in Y[1:]]
    reject_chronology(X,Y,HH,g,k,m0)
    return 'arith_chronology', (len(q)-1,len(j)-1)

def all_mod(M,p,t,U0=None,verbose=False,probe_guard=False):
    D,J,*_=model();Z=residue_orientation(p,t)
    FF=modgamma(M,p,t);done=Counter();bad=[];guesses={}
    for B,e in FF.factor()[1]:
        K=Bfield(B,p,t);g=K(nmod_poly([0,1],p))
        if K(Z):
            done['orientation']+=1;continue
        PP=sv(D,K,g,p,t);QQ=sv(J,K,g,p,t)
        if U0 is None:
            if len(PP)!=33 and len(QQ)!=33:
                bad.append((B.degree(),'s_leading',len(PP)-1,len(QQ)-1));continue
            W=PP if len(PP)==33 else QQ
        else:
            W=[K(v.v) for v in U0]
            assert W and W[-1]==1
        W=gcdp(gcdp(W,PP),QQ)
        assert W
        if len(W)==1:
            done['no_s']+=1;continue
        for S,j in sfactors(W,K):
            try:X,Y=one_s(K,g,S,p,t)
            except (ArithmeticError,ValueError,ZeroDivisionError) as err:
                X,Y='arithmetic_failure',str(err)
            if X in ('nodal_leading','arithmetic_failure'):
                bad.append((B.degree(),len(S)-1,X,Y))
                if probe_guard:
                    for nm,_,w in guards()[2]:
                        n=len(gcdp(S,sv(w,K,g,p,t)))-1
                        if n:guesses[nm]=guesses.get(nm,0)+n
            else: done[X]+=1
            if verbose:print('full reduced s',B.degree(),len(S)-1,X,Y,flush=True)
    print('whole arithmetic silent8 diagonal',M.degree(),p,t,dict(done),'open',bad,'maybe',guesses,flush=True)
    return not bad,done,bad,guesses
