"""Quartic profile replay within actual constant reverse-live nine-site numerator."""
from reverse_live_quintic import *
from equal_undetected_front import lagrange
L4=(1,-20,90,-140,70)

def literal_fifth(V,a,b,m,ha,hb,s,h,L):
    # Scale clocks and cubic defects by gamma and gamma^3 respectively.
    # This determinant uses actual rows 2...5, even an invisible one.
    w0=s-1-2*h;w1=s*s/2-s-2*h
    ca=(b*w0-w1)/(b-a);cb=w0-ca
    AH=h+ca*ha+cb*hb
    TH=s**3-s**4/4+2*h+ca*a**3+cb*b**3
    TA=a**3+a-1-a**4/4
    TB=b**3+b-1-m+m*a**3-b**4/4
    U=[[ha,a*ha,ha,TA],[hb,b*hb,hb+m*ha,TB],[h,s*h,AH,TH]]
    M0=add([V(-1),V(1)],sc(L,-2))
    M1=add([V(0),V(-1),V(1)/2],sc(L,-2))
    M2=add([V(0),V(0),V(-1),V(1)/3],sc(L,-V(4)/3))
    Md=[M0,M1,M2]
    tap=[sum_poly([sc(t,c) for t,c in zip(Md,l)]) for l in lagrange([a,b,s])]
    P=sum_poly([L]+[sc(w,z) for w,z in zip(tap,[ha,hb,h])])
    T=sum_poly([[V(0),V(0),V(0),V(1),-V(1)/4],sc(L,2)]+[sc(w,z**3) for w,z in zip(tap,[a,b,s])])
    W=[L,[V(0)]+L,P,T]
    Z=[(-1)**(i+3)*det([[z for j,z in enumerate(row) if j!=i] for row in U]) for i in range(4)]
    return sum_poly([sc(w,z) for w,z in zip(W,Z)])

def mode4(front,rear,slot,p,t,verbose=False):
    assert slot in (2,3,4,5,8) and (rear is None)==(slot==8)
    D,data=profile_gamma(front,L4)
    F=Bfield(nmod_poly([0,1],p),p,t)
    M=nmod_poly([int(F(q).x[0]) for q in D],p)
    assert M.degree()==4 and M.leading_coefficient()==1
    cnt=0
    for M0,e in M.factor()[1]:
        K=Bfield(M0,p,t);g=K(nmod_poly([0,1],p));x=1-g
        A,B,m,ha,hb,H4=data
        A,B,m,ha,hb=map(K,(A,B,m,ha,hb));H4=list(map(K,H4))
        LP=[K(v)*g**j for j,v in enumerate(L4)]
        R=add(sc(LP,ha),sc(H4,-ev(LP,A)))
        S,Err=qr(R,nodal([A,B]));assert not Err and len(S)==3
        S=mon(S);K0=Tower(S);s=K0.gen();g0=K0(g);x0=K0(x)
        U0=gap(K,g,x,rear,L4)
        nd=4 if rear is None else (2 if rear else 5)
        assert len(U0)==nd+1,(slot,front,rear,M0.degree(),len(U0)-1)
        W=Nested(list(map(K0,mon(U0))));u=W.gen();X=W(x0);G=W(g0)
        a,b,q=G*W(K0(A)),G*W(K0(B)),G*W(s)
        c=X-G*u;d=X-G*(2-u if rear else 2*u)
        pegs=[a,b,q,X,c]+([] if rear is None else [d])
        if slot<=4: pegs.pop(slot-2)
        L=mon(list(map(W,L4)))
        V=invpoly(W,[sum(L[j]/(j-i) for j in range(i+1,5)) for i in range(4)],L)
        rows=[];rhs=[]
        for a0 in pegs:
            l=ev(L,a0)
            rows.append([l,l*a0,l*a0**2,l*a0**3,ev(V,a0)])
            rhs.append(-l*a0**4)
        if slot==5:
            det([a+[v] for a,v in zip(rows,rhs)]).inv()
            cnt+=1;continue
        C0=det(rows).inv()
        *U,lam=[v*C0 for v in cramer(rows,rhs)]
        H=add(mul(L,U+[W(1)]),sc(V,lam))
        Y,rem=qr(H,nodal(pegs));assert not rem and len(Y)==4
        Y0=[v*G**j/(G**3) for j,v in enumerate(Y)]
        Hm=[W(K0(v)) for v in LP]
        scale=W(K0(ha))/ev(Hm,W(K0(A)))
        nc=lambda v:W(K0(v))
        p5=literal_fifth(W,nc(A),nc(B),nc(m),nc(ha),nc(hb),W(s),ev(sc(Hm,scale),W(s)),sc(Hm,scale))
        gts=[multicol(Y0,p5)]
        if slot<=4:
            z={2:a,3:b,4:q}[slot];k=1+2*u-u*u
            gts.append((X-z)*ev(L,c)-k*(c-z)*ev(L,X))
        span_unit(W,*gts)
        cnt+=1
    if verbose:print('quartic pass',front,rear,slot,p,t,cnt,flush=True)
    return cnt
