"""Exact late constraints with a sole literal early quartic Legendre contact."""
from flint import fmpq_mpoly_ctx, fmpq_poly, fmpq, nmod_poly
from quadratic_poly import E
from check_star_family import F as ExField
from seven_k0_anchors import F2,cv,ends,h4,pol
from functools import lru_cache
from itertools import combinations
from time import perf_counter

L3=(-1,12,-30,20)
L4=(1,-20,90,-140,70)
L5=(-1,30,-210,560,-630,252)
C=fmpq_mpoly_ctx.get(['u','s','r','t'])
u,s,r,t=C.gens();O=C.constant(1);Z=C.constant(0)
TT=t*t-fmpq(1,2)
RR=sum(fmpq(w,70)*r**j for j,w in enumerate(L4))
Q4=ExField(E(fmpq_poly([fmpq(w,70) for w in L4])))
r0=Q4(E(fmpq_poly([0,1])))

def red(P):
    if not hasattr(P,'to_dict'):return C.constant(P)
    return divmod(divmod(P,TT)[1],RR)[1]

def expr(y):
    y=Q4(y).v
    return sum((y.a[j]+y.b[j]*t)*r**j for j in range(y.degree()+1)) if y else Z

def number(v):
    d={}
    for (i,j,k,l),w in v.to_dict().items():
        assert i==j==0 and l in (0,1)
        d[k,l]=w
    return Q4(E(fmpq_poly([d.get((i,0),0) for i in range(4)]),
                fmpq_poly([d.get((i,1),0) for i in range(4)])))

def ev(P,a):return red(sum(v*a**i for i,v in enumerate(P)))
def evnum(P,a):return sum(v*a**i for i,v in enumerate(P))

def coeffs(P,axis=0):
    cells={}
    for I,v in P.to_dict().items():
        ij=list(I);n=ij[axis];ij[axis]=0
        cells.setdefault(n,{})[tuple(ij)]=v
    return [C.from_dict(cells.get(i,{})) for i in range(max(cells,default=-1)+1)]

def exactS(P,D):
    R=coeffs(P,1);K=coeffs(D,1);m=len(K)-1
    assert K and all(not v.degrees()[0] for v in K if v)
    inv=expr(number(K[-1]).inv())
    Q=[Z]*max(0,len(R)-m)
    while R and len(R)>m:
        d=len(R)-1-m
        v=red(R[-1]*inv)
        Q[d]=v
        for j,k in enumerate(K):R[d+j]=red(R[d+j]-v*k)
        while R and not R[-1]:R.pop()
    return red(sum(v*s**j for j,v in enumerate(Q))),red(sum(v*s**j for j,v in enumerate(R)))

def drop(P,gs):
    powers=[]
    for V in gs:
        j=0
        if V and V.degrees()[1]>0:
            while True:
                Q,R=exactS(P,V)
                if R:break
                P=Q;j+=1
                assert P
        powers.append(j)
    return P,powers

def trim(P):
    while P and not P[-1]:P=P[:-1]
    return P

def mul(A,B):
    Y=[Z]*(len(A)+len(B)-1)
    for i,v in enumerate(A):
        for j,w in enumerate(B):Y[i+j]+=v*w
    return trim([red(y) for y in Y])

def nodal(V):
    S=[O]
    for x in V:S=mul(S,[-x,O])
    return S

def W(F):return [red(sum(F[j]/(j-i) for j in range(i+1,len(F)))) for i in range(len(F)-1)]
def con(A,B,k):return red(sum(v*B[k-i] for i,v in enumerate(A) if 0<=k-i<len(B)))

def det(M):
    n=len(M)
    @lru_cache(None)
    def go(i,J):
        if i==n:return O
        S=Z;sg=1
        for j in range(n):
            if J>>j&1:
                if M[i][j]:S+=sg*M[i][j]*go(i+1,J^(1<<j))
                sg=-sg
        return red(S)
    return go(0,(1<<n)-1)

def res(F,G):
    a,b=coeffs(F,0),coeffs(G,0)
    m,n=len(a)-1,len(b)-1
    assert m>=1 and n>=1
    rows=[[Z]*i+a+[Z]*(n-1-i) for i in range(n)]
    rows += [[Z]*i+b+[Z]*(m-1-i) for i in range(m)]
    return det(rows)

@lru_cache(None)
def shape(front,contact):
    A,B,m=[Q4(cv(F2,v).v) for v in ends(front,1)]
    ha,hb=(A-1)/2,(B-1-m)/2
    A0,B0,HA,HB=map(expr,(A,B,ha,hb))
    a,other,hh,bb=(A,B,ha,hb) if contact==2 else (B,A,hb,ha)
    gamma=r0/a
    bo=gamma*other
    gr=evnum(L3,r0);lb=evnum(L4,bo)
    eta=hh/gr
    theta=(bb-eta*evnum(L3,bo))/lb
    hn=[eta*(L3[j] if j<4 else 0)+theta*L4[j] for j in range(5)]+[Q4(0)]
    h1=[((L4[j-1] if j else 0)-bo*(L4[j] if j<5 else 0)) for j in range(6)]
    g=expr(gamma);q=red(g*s)
    AH4=list(map(lambda v:Q4(cv(F2,v).v),pol(h4(front),lambda x:x)))
    H4all=red(sum(expr(v)*s**i for i,v in enumerate(AH4)))
    C0,C1=[list(map(expr,L)) for L in (hn,h1)]
    Draw=ev(C1,q)
    E=red(H4all-ev(C0,q))
    Pad=red((s-A0)*(s-B0))
    delta,rr=exactS(Draw,Pad);assert not rr and delta.degrees()[1]==3
    H=[]
    for y0,y1 in zip(C0,C1):
        z,w=exactS(red(Draw*y0+E*y1),Pad);assert not w
        H.append(z)
    ax,bx=red(g*A0),red(g*B0)
    for X,Y in [(ax,HA),(bx,HB),(q,H4all)]:
        assert not red(ev(H,X)-delta*Y)
    assert max(v.degrees()[1] for v in H if v)==3 and H[-1].degrees()[1]==2
    return H,delta,(g,ax,bx,q,A0,B0,HA,HB,expr(m),H4all)

@lru_cache(None)
def tail(front,contact,rear):
    h,delta,data=shape(front,contact)
    g,a,b,q,*_=data
    x=red(1-g);k=red(1+2*u-u*u)
    if rear is True:
        c,d=red(x-g-g*u),red(x-g+g*u) # centered u = original gap minus one
        C0,D0,X=map(lambda v:ev(h,v),(c,d,x))
        raw=red((1-u)*C0-(1+u)*D0+2*u*(2-u*u)*X)
        F,R=divmod(raw,u*(u*u-1))
        k=2-u*u
    else:
        c,d=red(x-g*u),red(x-2*g*u)
        C0,D0,X=map(lambda v:ev(h,v),(c,d,x))
        H=-2+u+4*u*u-u**3;J=2+3*u-12*u*u+4*u**3
        if rear is False:F,R=divmod(red(H*D0+2*J*C0-k*J*X),u*u)
        else:F,R=divmod(red((u-2)*C0-(2*u+k*(u-2))*X),u)
    assert not R
    F=red(F)
    assert F.degrees()[0]==(2 if rear is True else (6 if rear is False else 5))
    return F,(g,a,b,q,x,c,d,C0,D0,X,k)

def nd_gate(h,pegs):
    E=nodal(pegs);X=W(h);r0=8-len(pegs)
    M=[]
    for j in range(r0+1):
        Y=[Z]*j+E;U=W(Y)
        M.append([red(con(h,U,i)-con(Y,X,i)) for i in range(1,5)])
    return [det([[M[j][i] for i in II] for j in range(r0+1)])
            for II in combinations(range(4),r0+1)]

def center(P):
    f=coeffs(P);assert all(not v for v in f[1::2]);return f[::2]

@lru_cache(None)
def chart(front,contact,rear,slot):
    H,delta,data=shape(front,contact)
    _,_,_,_,A,B,*_=data
    F,(g,a,b,q,x,c,d,HC,HD,HX,k)=tail(front,contact,rear)
    pegs=[a,b,q,x,c]+([] if rear is None else [d])
    z=None
    if slot<=4:
        z=pegs[slot-2]
        pegs.pop(slot-2)
    N=nd_gate(H,pegs)
    guards=[delta,s-A,s-B,x-q,H[-1],HX]
    now=perf_counter()
    if rear is True:
        F0,F1=center(F)
        O0=N[:]
        if z is not None:O0=[red((x-z)*(HC+HD)/2-k*(x-g-z)*HX)]+O0
        GD=[]
        for P in O0:
            P0=center(P);J=red(sum(q*(-F0)**i*F1**(len(P0)-1-i) for i,q in enumerate(P0)))
            if J:
                T0,m=drop(J,guards)
                GD.append(T0)
                print('single Gauss centered elimination',front,contact,rear,slot,J.degrees()[1],T0.degrees()[1],m,flush=True)
            else:GD.append(J)
        deg=[d.degrees()[1] for d in GD]
        assert deg==([9,23 if slot==contact else 20] if slot<4 else ([10,21] if slot==4 else [18,17,16,16]))
        return 'star',GD,F,[],N
    G=[]
    if z is not None:
        G0,R=divmod(red((x-z)*HC-k*(c-z)*HX),u);assert not R
        G=[red(G0)]
    if rear is False and slot==5:
        hit=[]
        for n0 in N:
            P,m=drop(n0,guards)
            assert m[0]>=1
            hit.append(P)
        assert F.degrees()[:2]==(6,3) and hit[0].degrees()[:2]==(6,9)
        return 'arith6',None,F,[],hit
    D=res(F,G[0] if G else N[0])
    if D:
        S,m=drop(D,guards)
        assert S.degrees()[1]==(32 if rear is None else (27 if slot<4 else 33))
        assert m==([10,0,0,0,3,4] if rear is None else [0,0,0,0,1,0])
        print('single Gauss exact resultant',front,contact,rear,slot,D.degrees()[1],S.degrees()[1],m,round(perf_counter()-now,2),flush=True)
    else:
        S=D
        print('zero exact s resultant',front,contact,rear,slot,flush=True)
    return 'u',S,F,G,N
