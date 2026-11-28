"""Full gamma and fourth fibers at the degree-21 rank loss."""
from mixed_front_projection import front_projection,ext,L3,L4,L5
from reverse_live_quartic import *
from sympy import isprime,sqrt_mod
from flint import nmod_poly
from functools import lru_cache

def fp(x,p):
    return int(x.p)*pow(int(x.q),-1,p)%p

def evaluate(B,p,t,ga,K):
    H={}
    for (j,k,ell),v in B.to_dict().items():
        H[j]=H.get(j,K(0))+ga**k*K(fp(v,p)*pow(t,ell,p)%p)
    return trim([H.get(j,K(0)) for j in range(max(H,default=-1)+1)])

def base(front,p,t,verbose=False):
    PH,VH,GH=front_projection(front)
    rr=mon(ext(GH))
    D=Bfield(nmod_poly([0,1],p),p,t)
    G=nmod_poly([int(D(c).x[0]) for c in rr],p)
    assert G.degree()==21 and G.leading_coefficient()==1
    all_factors=G.factor()[1]
    assert sorted((q.degree(),e) for q,e in all_factors)==([(1,1),(20,1)] if front else [(6,1),(6,1),(9,1)])
    count=0
    for J,n in all_factors:
        K=Bfield(J,p,t);ga=K(nmod_poly([0,1],p))
        P,V=[evaluate(w,p,t,ga,K) for w in (PH,VH)]
        assert max(map(len,(P,V)))==4, ('s leading drop',J.degree(),len(P),len(V))
        S=gcdp(P,V)
        assert len(S)==2
        ga.inv()
        A,B,m=map(lambda q:cv(K,q),ends(front,1))
        ha,hb=(A-1)/2,(B-1-m)/2
        (B-A).inv()
        a,b=ga*A,ga*B
        L0=list(map(K,L4));G0=list(map(K,L3))
        La,Lb=ev(L0,a),ev(L0,b)
        qa,qb=ha/La,hb/Lb
        ya,yb=ev(G0,a)/La,ev(G0,b)/Lb
        line=lambda x,y:[(b*x-a*y)/(b-a),(y-x)/(b-a)]
        H0=mul(L0,line(qa,qb));H1=add(G0,sc(mul(L0,line(ya,yb)),-1))
        U=Tower(S);s=U.gen();g=U(ga);l=lambda w:[U(r) for r in w]
        hp=ev(l(H0),g*s)
        assert not ev(l(H1),g*s)
        assert hp==ev([cv(U,w) for w in pol(h4(front),lambda aa:aa)],s)
        if verbose:print('base fiber',front,p,t,J.degree(),len(S)-1,'profile degrees',len(H0)-1,len(H1)-1,flush=True)
        count+=1
        yield U,g,U(A),U(B),U(m),U(ha),U(hb),s,hp,l(H0),l(H1)
    if verbose:print('total base',front,p,t,[(M.degree(),e) for M,e in all_factors],count,flush=True)
