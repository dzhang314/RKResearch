"""Exact star Gauss contact, adding actual fifth before nodal reconstruction."""
from star_fibers import *
from equal_undetected_front import Nested

def fixres(F,G,U,d=2,n=5):
    z=U(0)
    assert len(F)<=d+1 and len(G)<=n+1
    F+= [z]*(d+1-len(F));G+=[z]*(n+1-len(G))
    rows=[]
    for i in range(n):rows.append([z]*i+F+[z]*(n-1-i))
    for i in range(d):rows.append([z]*i+G+[z]*(d-1-i))
    return det(rows)

def verify_gauss(front,p,t,verbose=False):
    _,ds,_,E5,_,G,guards=data(front)
    B0=Bfield(nmod_poly([0,1],p),p,t)
    M=B0.cast(G)
    assert M.degree()==G.degree() and M.leading_coefficient()==1
    counts=[0,0,0]
    for Md,_ in M.factor()[1]:
        F=Bfield(Md,p,t);ga=F(nmod_poly([0,1],p))
        counts[0]+=1
        for h in guards:eval_E(F,ga,h).inv()
        a,b,q0,q1,A,B,m,ha,hb,H4=ds
        aa,bb,qa,qb,AA,BB=map(lambda z:eval_E(F,ga,z),(a,b,q0,q1,A,B))
        vpoly=[aa/bb,F(0),F(1)]
        ll=list(map(F,Lco)); x0=1-ga;xr=1-2*ga
        sites=[[x0],[xr,-ga],[xr,ga]]
        Ls=[subst(ll,s) for s in sites]
        for ir in range(3):
            V0=gcdp(vpoly,Ls[ir])
            if len(V0)<=1:continue
            counts[1]+=1
            Z=Tower(V0);v=Z.gen();gg=Z(ga)
            a,b,x,c,d=Z(AA)*gg,Z(BB)*gg,Z(x0),Z(xr)-gg*v,Z(xr)+gg*v
            pegs=[a,b,x,c,d]
            kk=2-v*v
            r=pegs[2+ir]
            rr=pegs[:2+ir]+pegs[3+ir:]
            Q=[Z(qa),Z(qb)];q=[gg*Q[0],Q[1]]
            for c0 in pegs:ev(q,c0).inv()
            lp=mon(list(map(Z,Lco)))
            for cc in rr:ev(lp,cc).inv()
            assert not ev(lp,r)
            u0,rem=qr(lp,[-r,Z(1)])
            assert not rem and len(u0)==4
            Lp=ev(lp,x)*ev(q,c)*kk
            Lc=ev(lp,c)*ev(q,x)
            rho=[-c*Lp+x*Lc,Lp-Lc]
            assert not ev(rho,r)
            V=qr(mul(mul(rho,power(q,2)),list(map(Z,WL))),lp)[1]
            V,rem=qr(V,[-r,Z(1)])
            assert not rem
            Y0=mon(list(map(Z,all_coeffs(F,ga,E5))))
            assert len(Y0)==4
            if verbose:print('Gauss case',front,p,t,Md.degree(),ir,len(V0)-1,len(Y0)-1,flush=True)
            W=Nested(Y0);y=W.gen()
            gg=W(gg);q=list(map(W,q));Q=list(map(W,Q))
            r=W(r);rr=list(map(W,rr))
            LP=list(map(W,lp))
            u0=list(map(W,u0));V=list(map(W,V))
            P5=nodal(rr+[gg*y])
            S=[qr([W(0)]*j+P5,u0)[1] for j in range(3)]
            mat=[[S[j][i] if i<len(S[j]) else W(0) for j in range(3)] for i in range(3)]
            # No inverse of the reduced node matrix: true non-Gauss sites
            # justify the image up to scale in characteristic zero.
            Z2=cramer(mat,V+[W(0)]*(3-len(V)))
            Z2=[u*gg**j for j,u in enumerate(Z2)]
            cg=lambda z:W(Z(eval_E(F,ga,z)))
            A,B,m,ha,hb=map(cg,ds[4:9])
            H4=list(map(cg,ds[-1]))
            C=[W(v)*gg**j for j,v in enumerate(Lco)]
            sixth=sixth_gate(W,A,B,m,ha,hb,H4,Q,C,y)
            fixres(Z2,sixth,W).inv()
            counts[2]+=1
    return tuple(counts)
