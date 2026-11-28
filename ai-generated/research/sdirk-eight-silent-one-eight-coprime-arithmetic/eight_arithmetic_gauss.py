"""Arithmetic Gauss tail modes, using the physical Gauss root as base parameter."""
from eight_arithmetic_fibers import *
from eight_star_projection import WL as WLstar
from itertools import combinations

def pad(v,d,z):
    assert len(v)<=d+1
    return v+[z]*(d+1-len(v))

MM=EE(P([Q(v,70) for v in Lco]))
GP=ExField(MM)
r0=GP(EE(P([0,1])))

@lru_cache(None)
def gamma_mode(front,mode):
    assert mode in (0,1,2)
    F0,_,_,E5,guards,geom,de=acdata(front)
    _,_,q,bq,pegs0,Lx,Lc,Ld=de
    E=[ea(a)[0] for a in ycoeffs(E5)]
    gg=[GP(0),GP(1)]
    if mode==0:
        ga=[1-r0];u0=gg;den=[GP(1)]
    else:
        ga=gg;u0=[1-r0,GP(-1)];den=sc(ga,mode)
    rr=[r0]
    x=add([GP(1)],sc(ga,-1))
    if mode==0:c=add(x,sc(mul(ga,u0),-1));d=add(x,sc(mul(ga,u0),-2))
    elif mode==1:c=rr;d=add(sc(rr,2),sc(x,-1))
    else:c=sc(add(x,rr),GP(1)/2);d=rr
    # D1 in physical clock units; q_physical(x) = gamma*q0 + q1*x.
    q0=[GP(ea(q)[0].coeff(j)) for j in range(ea(q)[0].degree()+1)]
    # Evaluation at constant gamma, keeping the same polynomial-list type.
    if mode==0:q0=[ev(q0,ga[0])]
    bb=ea(bq)[0]
    q1=[GP(bb.coeff(j)) for j in range(bb.degree()+1)]
    if mode==0:q1=[ev(q1,ga[0])]
    Qclk=lambda y:add(mul(ga,q0),mul(q1,y))
    L=[GP(x) for x in Lco]
    a,b,*_=phases(front)
    pts=[sc(ga,GP(a.v)),sc(ga,GP(b.v)),x,c,d]
    geom=[ga,u0,add(add(power(den,2),sc(mul(den,u0),2)),sc(power(u0,2),-1)),
          q1, sum_poly([sc(mul(power(sc(mul(ga,q0),-1),j),power(q1,4-j)),v) for j,v in enumerate(L)])]
    geom += [add(pts[i],sc(pts[j],-1)) for i,j in combinations(range(5),2)]
    geom += [Qclk(z) for z in pts]
    geom += [subst(L,z) for j,z in enumerate(pts) if j!=mode+2]
    H=[GP(-2),GP(1),GP(4),GP(-1)];J=[GP(2),GP(3),GP(-12),GP(4)]
    def at_hom(v):return sum_poly([sc(mul(power(u0,j),power(den,len(v)-1-j)),c) for j,c in enumerate(v)])
    assert len(gcdp(H,J))==1
    geom.extend([at_hom(H),at_hom(J)])
    assert len(geom)==len([w for w in geom if w])
    # Use the necessary arithmetic tail profile at x or c, and the
    # stronger affine midpoint relation when the physical eighth d is Gauss.
    if mode==2:
        kq=geom[2]
        raw=add(sc(mul(mul(subst(L,c),Qclk(x)),power(den,2)),2),
                sc(mul(mul(kq,subst(L,x)),Qclk(c)),-1))
    else:
        ff=ea(F0)
        if mode==0:
            raw=[ev([GP(a.coeff(j)) for j in range(a.degree()+1)],ga[0]) for a in ff]
            raw=trim(raw)
        else:
            raw=sum_poly([mul(mul(power(u0,j),power(den,len(ff)-1-j)),
                              [GP(a.coeff(k)) for k in range(a.degree()+1)])
                         for j,a in enumerate(ff)])
    assert raw
    R=mon(guarded(raw,geom))
    print('Gauss root parameter mode',front,mode,'raw',len(raw)-1,'retained',len(R)-1,flush=True)
    return R,E,(ga,u0,den,x,c,d,pts,geom)

def verify_r(front,mode,p,t):
    P0,EE5,dat=gamma_mode(front,mode)
    if len(P0)<=1:return (0,0)
    B0=Bfield(nmod_poly([0,1],p),p,t)
    M=B0.cast(MM)
    assert M.degree()==4 and M.leading_coefficient()==1
    result=[]
    for G,_ in M.factor()[1]:
        F=Bfield(G,p,t);rr=F(nmod_poly([0,1],p))
        R0=list(map(F,P0));assert len(R0)==len(P0) and R0[-1]==F(1)
        U=Tower(R0);param=U.gen();r=U(rr)
        bc=lambda v:ev(list(map(U,v)),param)
        ga0,u00,den,x0,c0,d0,pts,guards=dat
        gamma=bc(ga0)
        for w in guards:bc(w).inv()
        u=bc(u00)/bc(den)
        k=1+2*u-u*u
        pegs=list(map(bc,pts));x,c,d=pegs[-3:]
        others=pegs[:mode+2]+pegs[mode+3:]
        LL=mon(list(map(U,Lco)))
        assert r==pegs[mode+2] and not ev(LL,r)
        l3,rem=qr(LL,[-r,U(1)]);assert not rem
        A,B,m,ha,hb,H4,qA,qB,qa,qb,*_=phases(front)
        Q=[ev(list(map(U,a)),gamma) for a in (qa,qb)]
        q=[gamma*Q[0],Q[1]]
        Lp,Lc=ev(LL,x)*ev(q,c)*k,ev(LL,c)*ev(q,x)
        rho=[-c*Lp+x*Lc,Lp-Lc];assert not ev(rho,r)
        W=qr(mul(mul(rho,power(q,2)),list(map(U,WLstar))),LL)[1]
        W,rem=qr(W,[-r,U(1)]);assert not rem
        e5=mon([ev([U(a.coeff(j)) for j in range(a.degree()+1)],gamma) for a in EE5])
        assert len(e5)==4
        Y=Nested(e5);y=Y.gen();yg=Y(gamma)
        l3=list(map(Y,l3));W=list(map(Y,W))
        P5=nodal(list(map(Y,others))+[yg*y])
        cols=[qr([Y(0)]*j+P5,l3)[1] for j in range(3)]
        slopes=[[cols[j][i] if i<len(cols[j]) else Y(0) for j in range(3)] for i in range(3)]
        R2=[z*yg**j for j,z in enumerate(cramer(slopes,pad(W,2,Y(0))))]
        abc=lambda c:Y(U(c))
        gate=sixth_gate(Y,*map(abc,(A,B,m,ha,hb)),list(map(abc,H4)),list(map(Y,Q)),
                       [Y(v)*yg**j for j,v in enumerate(Lco)],y)
        fixres(R2,gate,Y).inv()
        print('Gauss root arithmetic unit',front,mode,p,t,G.degree(),len(R0)-1,flush=True)
        result.append(G.degree())
    return tuple(result)
