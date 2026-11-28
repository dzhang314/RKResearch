"""Full local fibers with separate actual fifth-stage equations by placement."""
from regular_star_nonliteral import get_nonliteral
from regular_star_projection import C,Co,red,g,s,ev,profile
from star4_actual_fifth import (
    Bfield,Tower,add,qr,sc,mul,pe,det,trim,common_division,gcdp,
    with_p_supp,bcol,lv,sv,nodal,pol,h4,cv,nmod_poly,lru_cache,combinations,
)
from star4_guarded_fibers import Field,gpoly,norm,modQ,modcoef
from math import comb

@lru_cache(None)
def half_model():
    P,A,B=get_nonliteral(True)
    H,PP,V,delta,(a,b,q,La,Lb,A0,B0)=profile(True)
    H,rs=common_division([*H,red(delta*V)],[g,La,Lb]);D=H.pop()
    (A,B),rs0=common_division([A,B],[g,La,Lb])
    assert rs==rs0==[1,1,1]
    # P has one overall factor of the nonzero orientation unit.
    assert all(all(i[3]==1 for i in p.to_dict()) for p in P)
    P=[C.from_dict({(i,j,k,0):w for (i,j,k,l),w in p.to_dict().items()}) for p in P]
    return P,A,B,H,D,(a,b,q,La,Lb,A0,B0,1-g)

@lru_cache(None)
def bounds():
    P,A,B,H,D,(a,b,q,La,Lb,A0,B0,x)=half_model()
    m=1-2*g
    col=lambda z:red(B*(z-m)**2+g*g*A)
    J=[
      ('regular_scale',D),('early_clock',red((s-A0)*(s-B0))),
      ('x_q',x-q),('quintic',H[-1]),('terminal_h',ev(H,x)),
      ('B',B),('w0',A),('w1',red(A+B)),('w2',red(A+2*B)),
      ('rear_a',red(col(a)*col(b))),('rear_q',col(q)),('rear_x',col(x)),
    ]
    gg=red(g*La*Lb*(x-a)*(x-b))
    assert all(all(k[3]==0 for k in c.to_dict()) for c in [gg,*P,*(e[1] for e in J)])
    return [tuple(gpoly(e) for e in Co(p,1)) for p in P],gpoly(gg),[(name,tuple(gpoly(e) for e in Co(v,1))) for name,v in J]

def cofactors(J,I,K):
    return [(-1)**(2+j)*det([[J[k][i] for k in range(3) if k!=j] for i in I]) for j in range(3)]

def padded(P,Q,K):
    n,m=2,6;z=K(0)
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

def tests_in_s(K,gs,S,p,t):
    P,AA,BB,H,D0,dat=half_model()
    U=Tower(S);ss=U.gen();ga=U(gs)
    get=lambda P:lv(P,U,ga,ss,p,t)
    a,b,q,A0,B0,x,A,B,D=map(get,(*dat[:3],*dat[5:],AA,BB,D0))
    hh=[get(h) for h in H];m=1-2*ga
    E=mul(nodal([a,b,q,x]),[B*m*m+ga*ga*A,-2*m*B,B])
    Z=[h*ga**i for i,h in enumerate(hh)]
    ha,hb=(A0-1)/2,(B0-1)/2
    hs=pe([cv(U,k) for k in pol(h4(True),lambda x:x)],ss)
    J=with_p_supp(U,A0,B0,ss,Z,D,ha,hb,hs)
    assert len(J)<=7
    # Centered H at the two rear clocks, averaged and cleared by B^2.
    Hm=[sum((hh[i]*comb(i,j)*m**(i-j)*ga**j for i in range(j,6)),U(0)) for j in (0,2,4)]
    X=B*B*Hm[0]-A*B*Hm[1]+A*A*Hm[2]
    Y=B*(2*B+A)*pe(hh,x)
    N,Q=m*Y-x*X,ga*(Y-X)
    J5=sum((j*N**i*Q**(6-i) for i,j in enumerate(J)),U(0))
    C=[bcol([U(0)]*j+E,hh,U) for j in range(3)]
    J67=[padded([r*ga**j for j,r in enumerate(cofactors(C,I,U))],J,U) for I in combinations(range(4),2)]
    W0,W1=gcdp(S,J5.x),S
    for r in J67:W1=gcdp(W1,r.x)
    return W0,W1

def all_mod(F,p,t,guarded=None,verbose=False):
    FF=modQ(F,p)
    assert FF.degree()==F.degree() and FF.leading_coefficient()==1
    FFs=FF.factor()[1]
    P,*_=half_model()
    count=0;bad=[]
    for M,e in FFs:
        K=Bfield(M,p,t);g0=K(nmod_poly([0,1],p))
        PPP=[sv(q,K,g0,p,t) for q in P]
        if guarded is None:
            if all(len(L)!=1+d for L,d in zip(PPP,(18,17,16,16))):
                bad.append((M.degree(),tuple(len(L)-1 for L in PPP)))
                continue
            W=PPP[0]
        else:
            W=[modcoef(c,K,g0,p) for c in guarded]
            assert W and W[-1]==1
        Q=W
        for L in PPP:Q=gcdp(Q,L)
        if len(Q)<=1:
            assert len(Q)==1
            count+=1;continue
        A,B=tests_in_s(K,g0,Q,p,t)
        if len(A)>1 or len(B)>1:
            bad.append((M.degree(),len(Q)-1,len(A)-1,len(B)-1))
        else:count+=1
    if verbose or not bad:
        print('local trials',F.degree(),p,t,'pass',count,'bad',bad,flush=True)
    return not bad,count,bad
