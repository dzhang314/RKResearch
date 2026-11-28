"""Full local replay for all arrays in the single-contact chart."""
from early_gauss_exact import *
from unequal_finite import Bfield,Tower,gcdp,trim as ptrim
from off8_fibers import ev as pev,multicol,sc as fsc
from reverse_live_quartic import literal_fifth
import exception_final as EF
from flint import nmod_mpoly_ctx

def norm(v,p):
    return int(v.p)*pow(int(v.q),-1,p)%p

def tb(P,p,t0,r0):
    A={}
    for (i,j,k,l),v in P.to_dict().items():
        A[i,j]=(A.get((i,j),0)+norm(v,p)*pow(r0,k,p)*pow(t0,l,p))%p
    return A

def red_s(P,p,t0,r0):
    T={}
    for (i,j),v in tb(P,p,t0,r0).items():
        assert i==0
        T[j]=v
    return nmod_poly([T.get(j,0) for j in range(max(T,default=-1)+1)],p)

def ev_s(P,K,p,t0,r0,ss):
    T={}
    for (i,j),v in tb(P,p,t0,r0).items():
        T[i]=T.get(i,K(0))+K(v)*ss**j
    return ptrim([T.get(i,K(0)) for i in range(max(T,default=-1)+1)])

def eval_scalar(P,K,p,t0,r0,ss):
    a=ev_s(P,K,p,t0,r0,ss)
    assert len(a)<=1
    return a[0] if a else K(0)

def actual_fifth(front,contact,rear,slot,K,ss,uu,p,t0,rr,report):
    H,D,(gg,aa,bb,qq,A0,B0,HA,HB,mm,H4all)=shape(front,contact)
    U=Tower(uu);u=U.gen()
    what=lambda P: U(eval_scalar(P,K,p,t0,rr,ss))
    s0=U(ss)
    g,a,b,q,A,B,ha,hb,m,H4,DD=map(what,(gg,aa,bb,qq,A0,B0,HA,HB,mm,H4all,D))
    inv=DD.inv()
    L=[what(x)*inv for x in H]
    C0=[vt*g**j for j,vt in enumerate(L)]
    assert pev(C0,A)==ha and pev(C0,B)==hb and pev(C0,s0)==H4
    X=1-g
    if rear is True:
        c,d=X-g-g*u,X-g+g*u
        kk=2-u*u
    else:
        c,d=X-g*u,X-2*g*u
        kk=1+2*u-u*u
    P=[a,b,q,X,c]+([] if rear is None else [d])
    if slot<=4:P.pop(slot-2)
    F5=literal_fifth(U,A,B,m,ha,hb,s0,H4,C0)
    if slot==5:
        hX,hc=pev(L,X),pev(L,c)
        z=(kk*c*hX-X*hc)/(kk*hX-hc)
        pev(F5,z/g).inv()
    J=EF.ordinary_cols([[v] for v in L],[[v] for v in P],U)
    J=[[v[0] if v else U(0) for v in row] for row in J]
    n=8-len(P)
    R=EF.solve_minor(J,n,U)+[U(1)]
    assert all(sum(R[j]*J[j][i] for j in range(n+1))==0 for i in range(4))
    Yn=[v*g**j/g**n for j,v in enumerate(R)]
    multicol(Yn,F5).inv()
    if report:print('single Gauss actual fifth unit',front,contact,rear,slot,p,t0,rr,K.M.degree(),len(uu)-1,flush=True)

def roots(p):
    a=[int(r) for r,e in nmod_poly(list(L4),p).roots() if e==1]
    return sorted(a) if len(a)==4 else None

def test(front,contact,rear,slot,p,t0,verbose=False,late=True):
    """One full prime across the four distinct Legendre residue roots."""
    mode,P,F,G,N=chart(front,contact,rear,slot)
    root=roots(p);assert root is not None
    counts=[0,0,0]
    for rr in root:
        if mode=='arith6':
            M2=nmod_mpoly_ctx.get(['u','s'],p)
            f,n=[M2.from_dict(tb(X,p,t0,rr)) for X in (F,N[0])]
            assert f.degrees()[0]==n.degrees()[0]==6
            z=f.resultant(n,0)
            zz={}
            for (i,j),a0 in z.to_dict().items():
                assert i==0
                zz[j]=int(a0)
            S=nmod_poly([zz.get(j,0) for j in range(max(zz,default=-1)+1)],p)
            if S.degree()!=72:raise ArithmeticError(('arith6 s-degree drop',rr,S.degree()))
        else:
            if mode=='star':
                T=[(U,red_s(U,p,t0,rr)) for U in P if U]
            else:
                assert P
                T=[(P,red_s(P,p,t0,rr))]
            for U,S in T:
                if S.degree()==U.degrees()[1]:break
            else:raise ArithmeticError(('no full s leading',rr))
            for V,M in T:S=S.gcd(M)
        # The full s algebra is retained through the other constraints.
        for M,j in S.factor()[1]:
            K=Bfield(M,p,t0);ss=K(nmod_poly([0,1],p))
            counts[0]+=1
            U=ev_s(F,K,p,t0,rr,ss)
            GG=G[:]
            if rear is True and slot<=4:
                _,(g,a,b,q,x,c,d,HC,HD,HX,k)=tail(front,contact,rear)
                z={2:a,3:b,4:q}[slot]
                GG=[red((x-z)*HC-k*(c-z)*HX),red((x-z)*HD-k*(d-z)*HX)]
            need=max(0,F.degrees()[0])
            if len(U)!=need+1:
                # If the true star leading drops in this residue, another
                # full actual comparison may still supply a monic u model.
                for P0 in GG+N:
                    f=ev_s(P0,K,p,t0,rr,ss)
                    if len(f)==P0.degrees()[0]+1:
                        U=f;break
                else:raise ArithmeticError(('no full u leading',rr,M.degree(),need,len(U)-1))
            for V in [F]+GG+N:U=gcdp(U,ev_s(V,K,p,t0,rr,ss))
            if len(U)<=1:continue
            counts[1]+=1
            if verbose:print('single Gauss actual u fiber',front,contact,rear,slot,p,t0,rr,M.degree(),len(U)-1,flush=True)
            if late:actual_fifth(front,contact,rear,slot,K,ss,U,p,t0,rr,verbose)
            counts[2]+=1
    return counts
