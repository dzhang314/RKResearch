"""Exact finite gamma splits and a six-peg constant-profile nodal moment gate."""
from one_front_constant_projection import *
from off_literal_active8 import eval_y,eval_s,span_unit
from silent_guard import h4_splits
from constant_q_nonzero import moment_const
from extra_active import invpoly
from itertools import combinations

@lru_cache(None)
def world(f,slot):
    G,Phi,D,Et,Ea=cert(f,slot)
    # Monicity, not square-freeness, is needed for the final finite-unit tests.
    A,B=profile(f,slot)[:2]
    H4=[cv(F2,v) for v in pol(h4(f),lambda h:h)]
    Forbidden=mul(H4,nodal([A,B]))
    W=exact_g(can(Phi.resultant(term(Forbidden,s),1)))
    assert len(gcdp(G,W))-1==12
    print('one-front exact guarded projection',f,slot,len(G)-1,len(gcdp(G,W))-1,flush=True)
    Z=mon(guarded(G,[W]))
    bad=gcdp(G,W)
    spec=h4_splits(bad,Phi,Forbidden) if len(bad)>1 else []
    return [(Z,None)]+spec,Phi,D,Et,Ea

def tail(F,gg,rear):
    l=list(map(F,Lco));x=1-gg
    U=[F(0),F(1)];k=[F(1),F(2),F(-1)]
    c=[x,-gg];d=[x-2*gg,gg] if rear else [x,-2*gg]
    px,pc,pd=ev(l,x),subst(l,c),subst(l,d)
    if rear:
        N=sum_poly([mul([F(2),F(-1)],pc),sc(mul(U,pd),-1),
                    sc(mul(k,[F(-2),F(2)]),px)])
        for a in (0,1,2):
            N,rr=qr(N,[-F(a),F(1)]);assert not rr
        assert len(N)==3
    else:
        H=[F(-2),F(1),F(4),F(-1)];J=[F(2),F(3),F(-12),F(4)]
        N=sum_poly([mul(H,pd),sc(mul(J,pc),2),sc(mul(k,J),-px)])
        N,rr=qr(N,[F(0),F(0),F(1)]);assert not rr
        assert len(N)==6
    return mon(N)

def check(f,slot,rear,p,t):
    defs,Phi,D,Et,Ea=world(f,slot)
    av=profile(f,slot)[5]
    cb=Bfield(nmod_poly([0,1],p),p,t)
    counts=[0]*4
    for Gamma,exact_s in defs:
        if len(Gamma)<=1:continue
        G0=nmod_poly([int(cb(w).x[0]) for w in Gamma],p)
        assert G0.degree()==len(Gamma)-1 and G0.leading_coefficient()==1
        for M,_ in G0.factor()[1]:
            F=Bfield(M,p,t);ga=F(nmod_poly([0,1],p));ga.inv()
            counts[0]+=1
            S0=eval_s(Phi,F,ga,F(0)) if exact_s is None else [ev(list(map(F,w)),ga) for w in exact_s]
            if exact_s is None:assert len(S0)==4
            else:assert len(S0)==len(exact_s)
            if len(S0)<=1:continue
            S0[-1].inv()
            Ss=gcdp(S0,eval_s(D,F,ga,F(0)))
            if len(Ss)<=1:continue
            counts[1]+=1
            U=Tower(Ss);s0=U.gen();g0=U(ga)
            ET=eval_y(Et,U,g0,s0);EA=eval_y(Ea,U,g0,s0)
            # At least one monic degree-three equation is available to
            # lift the actual fifth into a finite local algebra. No leading
            # drop is inferred from the reduced gcd.
            candidates = ([ET] if len(ET)==4 else [])+([EA] if len(EA)==4 else [])
            if len(ET)==len(EA)==4:
                candidates+=[add(ET,sc(EA,U(j))) for j in range(1,7)]
            for C0 in candidates:
                if len(C0)!=4:continue
                try:C0[-1].inv()
                except ArithmeticError:continue
                break
            else:raise ArithmeticError('no degree-three fifth leading unit')
            YY=gcdp(gcdp(C0,ET),EA)
            if len(YY)<=1:continue
            counts[2]+=1
            Y=Nested(YY);y0=Y.gen();g1=Y(g0)
            V=Nested(list(map(Y,tail(F,ga,rear))));u0=V.gen();gamma=V(g1)
            k=1+2*u0-u0*u0;x=1-gamma
            c=x-gamma*u0;d=x-gamma*(2-u0 if rear else 2*u0)
            a=gamma*V(Y(U(F(av))))
            z=gamma*V(Y(s0));l=gamma*V(y0)
            points=[a,z,x,c,d,l]
            J=moment_const(V,points,4)
            a0,b0,c0,d0=J
            D2=a0*c0-b0*b0
            N2=[b0*d0-c0*c0,b0*c0-a0*d0,D2]
            L=mon(list(map(V,Lco)));q=invpoly(V,[sum(L[j]/(j-i) for j in range(i+1,5)) for i in range(4)],L)
            Lx,Lc=ev(L,x),ev(L,c)
            rho=[-c*k*Lx+x*Lc,k*Lx-Lc]
            R0=qr(mul(rho,q),L)[1]
            R1=qr(mul(nodal(points),N2),L)[1]
            R0+=[V(0)]*(4-len(R0));R1+=[V(0)]*(4-len(R1))
            print('one-front constant stage5 support',f,slot,rear,p,t,M.degree(),
                  (len(Ss)-1,len(YY)-1),flush=True)
            span_unit(V,*(R0[i]*R1[j]-R0[j]*R1[i] for i,j in combinations(range(4),2)))
            counts[3]+=1
    return tuple(counts)
