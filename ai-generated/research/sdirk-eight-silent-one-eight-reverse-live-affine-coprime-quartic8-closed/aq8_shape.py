"""Actual ordinarily silent eighth, six prospective ordinary pegs."""
from functools import lru_cache
from aq_rear import C,u,s,g,red,ev,divide,front_data,Lco
from regular_star_projection import remove
from flint import fmpq_mpoly_ctx, fmpq

B=fmpq_mpoly_ctx.get(['Y','u','s','g','t'])
Y,U,S,G,T=B.gens()
BB=T*T-fmpq(1,2)
Z=B.constant(0)
def lift(F):
    if not hasattr(F,'to_dict'):return B.constant(F)
    return B.from_dict({(0,*I):c for I,c in F.to_dict().items()})
def down(F):
    R={}
    for (y,*I),c in F.to_dict().items():
        assert not y
        R[tuple(I)]=c
    return C.from_dict(R)
def rd(F):return divmod(F,BB)[1]
def coj(F):return B.from_dict({I:v*(-1)**I[-1] for I,v in F.to_dict().items()})
def dv(F,H):
    if H.degrees()[4]:
        H0=coj(H);F,H=rd(F*H0),rd(H*H0)
    Q,R=divmod(F,H);assert not R,(F.degrees(),H.degrees())
    return Q
def cf(F,j):
    D={}
    for (y,*I),a in F.to_dict().items():
        D.setdefault(y,{})[(0,*I)]=a
    return [B.from_dict(D.get(i,{})) for i in range(j+1)]
def bf(F,r):return rd(sum(c*r**i for i,c in enumerate(F)))
def subs_y(F,y):return bf(cf(F,F.degrees()[0]),y)
def mulp(a,b):
    T=[Z]*(len(a)+len(b)-1)
    for i,r in enumerate(a):
        for j,s in enumerate(b):
            T[i+j]+=r*s
    return list(map(rd,T))
def nodal(aa):
    P=[B.constant(1)]
    for a in aa:P=mulp(P,[-a,B.constant(1)])
    return P
def W(P):return [rd(sum(P[j]/(j-i) for j in range(i+1,len(P)))) for i in range(len(P)-1)]
def cof(a,b,k):return rd(sum(c*b[k-i] for i,c in enumerate(a) if 0<=k-i<len(b)))
def det(M):
    if len(M)==1:return M[0][0]
    R=Z
    for k,v in enumerate(M[0]):
        if v: R+=(-1)**k*rd(v*det([r[:k]+r[k+1:] for r in M[1:]]))
    return rd(R)

@lru_cache(None)
def tail(front):
    fd,J,gs=front_data(front)
    A,B0,m,ha,hb,H,H4,Q=fd
    a,b=red(g*A),red(g*B0)
    x=1-g;c=x-g*u;k=1+2*u-u*u
    Px,Pc=ev(Lco,x),ev(Lco,c)
    Qx,Qc=ev(Q,x),ev(Q,c)
    F0=red((u-2)*Pc*Qx-(2*u+k*(u-2))*Px*Qc)
    F=divide(F0,u)
    L,st=remove(gs[4],gs[:4]);assert L.degrees()[2]==12 and st==[0,0,1,1]
    gs=gs+(Px,Qx,L)
    z=red(x+g*k*(u-2)/2)
    assert F.degrees()[:3]==(4,0,9)
    print('actual silent eighth shape',front,F.degrees(),flush=True)
    return F,J,z,gs,(a,b,red(g*s),x,c)

@lru_cache(None)
def literal_fifth_exact(front):
    A,B0,m,ha,hb,Δ,H4,Q=front_data(front)[0]
    A,B0,m,ha,hb,Δ=map(lift,(A,B0,m,ha,hb,Δ))
    H4=list(map(lift,H4));Q=list(map(lift,Q))
    h=bf(H4,S)
    BA=B0-A
    # 1/(B-A) is an exact scalar in Q(t), never an unknown pivot.
    delta=coj(BA);unit=rd(BA*delta)
    assert unit.is_constant() and unit
    inv=rd(delta/unit)
    wa,wb=S-1-2*h,S*S/2-S-2*h
    ca=rd((B0*wa-wb)*inv);cb=wa-ca
    Ah=rd(h+ca*ha+cb*hb)
    Th=rd(S**3-S**4/4+2*h+ca*A**3+cb*B0**3)
    Ta=rd(A**3+A-1-A**4/4)
    Tb=rd(B0**3+B0-1-m+m*A**3-B0**4/4)
    # h(Y)=N/D in normalized stages; use the homogeneous row itself.
    N=rd(G*Δ*bf(list(map(lift,Lco)),G*Y))
    D=bf(Q,G*Y)
    μ0=rd((Y-1)*D-2*N)
    μ1=rd((Y**2/2-Y)*D-2*N)
    μ2=rd((Y**3/3-Y**2)*D-fmpq(4,3)*N)
    pA=rd((S-B0)*(μ2-(S+B0)*μ1+S*B0*μ0))
    pB=rd(-(S-A)*(μ2-(S+A)*μ1+S*A*μ0))
    pS=rd(BA*(μ2-(A+B0)*μ1+A*B0*μ0))
    d0=rd(BA*(S-A)*(S-B0))
    AH=rd(d0*N+pA*ha+pB*hb+pS*h)
    TH=rd(d0*((Y**3-Y**4/4)*D+2*N)+pA*A**3+pB*B0**3+pS*S**3)
    P=det([[ha,rd(A*ha),ha,Ta],[hb,rd(B0*hb),rd(hb+m*ha),Tb],
           [h,rd(S*h),Ah,Th],[rd(N*d0),rd(Y*N*d0),AH,TH]])
    P0=dv(P,rd((Y-A)*(Y-B0)))
    # Work modulo true fourth J only to remove the third literal pad.
    Ps=subs_y(P0,S)
    _,J,_,_,_=tail(front)
    if Ps:dv(Ps,lift(J))
    H=dv(rd(P0-Ps),Y-S)
    H=dv(H,G)   # genuine nonzero diagonal, from profile scale
    assert P.degrees()[:4]==(5,0,5 if front else 7,5)
    assert H.degrees()[:4]==(2,0,6 if front else 7,4)
    print('ordinary fifth raw / padded exact',front,P.degrees(),H.degrees(),flush=True)
    return H

@lru_cache(None)
def prospective_six(front):
    F,J,z,gs,pegs=tail(front)
    E=nodal(list(map(lift,pegs))+[G*Y])
    L=list(map(lift,Lco));WL=W(L)
    cols=[]
    for j in range(3):
        D=[Z]*j+E;WD=W(D)
        V=[cof(L,WD,i)-cof(D,WL,i) for i in range(12)]
        assert all(not x for x in V[4:])
        cols.append(V[:4])
    Q=front_data(front)[0][-1]
    cols.append(mulp(list(map(lift,Q)),list(map(lift,Q)))+[Z])
    P=det(cols)
    P0=dv(P,rd(lift(gs[2]*gs[3])))
    assert P.degrees()[:4]==(3,3,3,28) and P0.degrees()[:4]==(3,3,3,20)
    print('prospective six ordinary pegs',front,P.degrees(),P0.degrees(),flush=True)
    return P0
