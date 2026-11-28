"""Complete actual fifth and both remaining ordinary root assignments."""
from aq8_shape import tail, literal_fifth_exact, cf,down
from aq8_projection import fifth_project,fourth_project,diagonal
from aq_rear import front_data,Lco
from aq_gamma import gpoly
from regular_star_projection import Co
from aq_modular import lcmo,mon,horner,Bfield,nmod_poly,gcdp
from aq_modular import ev,qr,mul,sc,add,nodal,det,invpoly,cramer
from arith_ordinary_reconstruction import extend,divide_root,reverse_core,residual,factor_deriv
from collections import Counter

def cas(B,F):
    return B(gpoly(F))

def evu(B,F,u,i0):
    return horner([i0(cas(B,c)) for c in Co(F)],u)

def evs(B,F,u,s,i0,i1):
    return horner([i1(evu(B,c,u,i0)) for c in Co(F,1)],s)

def weights(V,Y,g,Q):
    cc=[g*y for y in Y]
    iii=(1,2,3,4,5,6,8,9)
    D=nodal([cc[i] for i in iii]);W=nodal(cc[1:])
    DD=factor_deriv(D,V);WW=factor_deriv(W,V)
    b=[V(0)]*10;w=[V(0)]*10
    for i in iii:
        T,rr=qr(D,[-cc[i],V(1)])
        assert not rr
        b[i]=sum((V(a)/(j+1) for j,a in enumerate(T)),V(0))/ev(DD,cc[i])
        b[i].inv()
    L=-b[-1]*ev(WW,cc[-1])/ev(Q,cc[-1])
    L.inv()
    for i in range(1,10):
        w[i]=L*ev(Q,cc[i])/ev(WW,cc[i])
    return b,w

def chrono(V,Y,hh,g,k,Q,m):
    b,w=weights(V,Y,g,Q)
    A=reverse_core(V,Y,hh,g,k,b,w,m)
    S0=residual(V,Y,hh,g,b,A([V(0)]*3));T=[]
    for j in range(3):
        v=[V(int(i==j)) for i in range(3)]
        T.append([a-d for a,d in zip(residual(V,Y,hh,g,b,A(v)),S0)])
    det([*T,S0]).inv()

def one_s(front,B,g0,U,u,i0,S):
    F,J,zpoly,gs,raw=tail(front)
    V,s,i1=extend(U,S)
    lift=lambda q:i1(i0(q))
    poly=lambda q:evs(B,q,u,s,i0,i1)
    g=lift(g0)
    pegs=list(map(poly,raw))
    A,B0,m,ha,hb,H,H4,Q=front_data(front)[0]
    Q0=list(map(poly,Q));L0=list(map(V,Lco))
    WL=[sum(L0[j]/(j-i) for j in range(i+1,5)) for i in range(4)]
    Z=qr(mul(invpoly(V,WL,mon(L0)),mul(Q0,Q0)),mon(L0))[1]
    rows=[];rhs=[]
    for a in pegs:
        L=ev(L0,a)
        rows.append([L,L*a,L*a**2,L*a**3,ev(Z,a)])
        rhs.append(-L*a**4)
    d0=det(rows).inv()
    *coef,lam=[a*d0 for a in cramer(rows,rhs)]
    P=mon(add(mul(L0,coef+[V(1)]),sc(Z,lam)))
    R,rem=qr(P,nodal(pegs));assert not rem and len(R)==4
    R=mon([a*g**j for j,a in enumerate(R)])
    L=[poly(down(a)) for a in cf(literal_fifth_exact(front),2)]
    L=gcdp(R,L)
    assert L and L[-1]==1
    if len(L)==1:return 'no_y',[]
    K,y,i2=extend(V,L)
    R=divide_root(list(map(i2,R)),y,K)
    assert len(R)==3
    W,r6,i3=extend(K,R)
    r7=-i3(R[1])-r6
    L2=lambda z:i3(i2(z))
    L3=lambda z:L2(i1(z))
    q0=list(map(L2,Q0))
    a,b,mm,dd,lz=map(lambda z:L2(poly(z)),(A,B0,m,H,zpoly))
    g=L2(g);u=L3(u);s=L2(s);y=i3(y)
    x=1/g-1;c=x-u;k=1+2*u-u*u
    zz=lz/g
    Y=[W(1),a,b,s,y,r6,r7,zz,c,x]
    Hs=[W(0)]+[g*dd*ev(list(map(W,Lco)),g*v)/ev(q0,g*v) for v in Y[1:]]
    chrono(W,Y,Hs,g,k,q0,mm)
    return 'chrono',(len(L)-1,)

def all_mod(front,p,t):
    F,J,_,_,_=tail(front);RY=fifth_project(front);N=fourth_project(front);M=diagonal(front)
    D=Bfield(nmod_poly([0,1],p),p,t).cast(M)
    assert D.degree()==M.degree() and D.leading_coefficient()==1
    parts=D.factor()[1];rr=nmod_poly([1],p)
    for d,e in parts:rr*=d**e
    assert rr==D
    cnt=Counter();covered=0
    for MM,e in parts:
        B=Bfield(MM,p,t);gg=B(nmod_poly([0,1],p))
        fn,nn,jn=[lcmo(B,Co(h,i)) for h,i in ((F,0),(N,0),(J,1))]
        assert len(fn)==5 and len(jn)==3
        covered+=MM.degree()*e
        fn,jn=mon(fn),mon(jn)
        E=gcdp(fn,nn)
        assert E
        if len(E)==1:cnt['no_u']+=1;continue
        U,u,i0=extend(B,E)
        sy=[evu(B,q,u,i0) for q in Co(RY,1)]
        S=gcdp(list(map(i0,jn)),sy)
        assert S and S[-1]==1
        if len(S)==1:cnt['no_s']+=1;continue
        key,msg=one_s(front,B,gg,U,u,i0,S)
        assert key in ('chrono','no_y')
        cnt[key]+=1
        print('full reduced regular case',front,MM.degree(),e,len(E)-1,len(S)-1,key,msg,flush=True)
    assert covered==M.degree()
    assert dict(cnt)=={'chrono':11 if front else 5}
    print('full regular affine quartic silent eighth',front,p,t,M.degree(),dict(cnt),flush=True)
    return dict(cnt)
