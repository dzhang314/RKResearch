
"""Fixed exact certificates: third early mate over full degree-six residue quotients."""
from itertools import permutations
from check_first_two import (
    S, nmod_poly, argv, kind, G, rr, ev, w_z, v_z, u_w, b_w,
)

def third(p,u,b,v,slot):
    a=(1+2*u)%p
    if not a or not b or a==b or (kind!='star' and not v):return
    k=(1+2*v-v*v)%p
    h=(v**3-4*v*v-v+2)%p; q=(4*v**3-12*v*v+3*v+2)%p
    if kind!='star' and (not k or (kind=='arith' and (not h or not q))):return
    scalar=lambda x:nmod_poly([x%p],p)
    zero,one=scalar(0),scalar(1)
    D=nmod_poly([0,1],p)
    c=D-(1+slot*v)
    zj=(D-1,D-1-v,D-1-2*v)
    keep=[zj[j] for j in range(3) if j!=slot]
    Js=lambda f:nmod_poly([0]+[int(f[i])*pow(i+1,-1,p)%p for i in range(f.degree()+1)],p)
    Z=(D-a)*(D-b);TZ=D*Z
    J2,J3=Js(Z),Js(TZ)
    dj=(int(J2(a))*int(J3(b))-int(J2(b))*int(J3(a)))%p
    assert dj==a*a*b*b*(a-b)**3*pow(24,-1,p)%p and dj
    dl=lambda t:70*t**4-140*D*t**3+90*D**2*t**2-20*D**3*t+D**4
    al=(-dl(a)*int(J3(b))+dl(b)*int(J3(a)))*pow(dj,-1,p)
    be=(-dl(b)*int(J2(a))+dl(a)*int(J2(b)))*pow(dj,-1,p)
    Zc=(c-a)*(c-b)
    nc=al*(Zc-J2(c))+be*(c*Zc-J3(c))-dl(c)
    F,rem=divmod(nc,Zc)
    assert not rem
    if F.degree()!=6:return
    guards=[D,c-a,c-b]
    if kind!='star':guards += [x-y for x in keep for y in (a,b)]
    if any(g.gcd(F).degree() for g in guards):
        return
    # All loops that can invert in R use a proved unit in the whole residue algebra.
    F=F*pow(int(F[F.degree()]),-1,p)
    def unit(g):
        dd,aa,_=g.xgcd(F)
        if dd.degree()!=0:return
        return aa*pow(int(dd[0]),-1,p)%F

    def plus(A,B):
        m=max(len(A),len(B))
        return [((A[i] if i<len(A) else zero)+(B[i] if i<len(B) else zero))%F for i in range(m)]
    def sc(A,x):
        return [a*x%F for a in A]
    def minus(A,B):
        return plus(A,sc(B,-1))
    def mul(A,B):
        C=[zero]*(len(A)+len(B)-1)
        for i,x in enumerate(A):
            for j,y in enumerate(B): C[i+j]=(C[i+j]+x*y)%F
        return C
    def pp(*rs):
        A=[one]
        for z in rs: A=mul(A,[-z,one])
        return A
    def evR(A,t):
        y=zero
        for a in A[::-1]:y=(y*t+a)%F
        return y
    def J(A):
        return [zero]+[a*pow(i+1,-1,p)%F for i,a in enumerate(A)]
    def I(A,i=0):
        return sum((z*pow(j+i+1,-1,p)*D.pow_mod(j+i,F) for j,z in enumerate(A)),zero)%F
    def div(A,B):
        assert B[-1]==one
        R=A[:]
        Q=[zero]*(len(A)-len(B)+1)
        for j in range(len(Q)-1,-1,-1):
            Q[j]=R[j+len(B)-1]
            for i,x in enumerate(B):
                R[j+i]=(R[j+i]-Q[j]*x)%F
        assert not any(R)
        return Q
    def det(A):
        n=len(A)
        d=zero
        for sig in permutations(range(n)):
            sgn=(-1)**sum(sig[i]>sig[j] for i in range(n) for j in range(i+1,n))
            z=one
            for j in range(n):z=z*A[j][sig[j]]%F
            d=(d+sgn*z)%F
        return d
    def solve(A,B):
        d=det(A)
        inv=unit(d)
        if inv is None:return
        M=[];n=len(A)
        for k in range(n):M.append(det([[B[i] if j==k else A[i][j] for j in range(n)] for i in range(n)])*inv%F)
        assert all(sum((x*y for x,y in zip(row,M)),zero)%F==b%F for row,b in zip(A,B))
        return d,M

    L3=[-D**3,12*D**2,-30*D,scalar(20)]
    L4=[D**4,-20*D**3,90*D**2,-140*D,scalar(70)]
    L5=[-D**5,30*D**4,-210*D**3,560*D**2,-630*D,scalar(252)]
    Sig=pp(scalar(a),scalar(b),c)
    JS=J(Sig)
    xs=[scalar(a),scalar(b),c]
    s3=solve([[evR(L,x) for L in (L3,L4,L5)] for x in xs],
             [-(x-c)*evR(JS,x)%F for x in xs])
    if s3 is None:return
    p3,lam=s3
    U=plus(plus(sc(L3,lam[0]),sc(L4,lam[1])),sc(L5,lam[2]))
    C4=div(minus(mul([-c,one],minus(Sig,JS)),U),Sig)
    if kind=='star':
        P5,R=Sig,mul(Sig,pp(D-2,D-2))
    else:
        P5=mul(Sig,pp(*keep))
        s,t,r=zj
        qt=lambda x:div(P5,[-x,one])
        if slot==2: R=minus(sc(qt(t),k),qt(s))
        elif kind=='ghost': R=qt(r)
        elif slot==0: R=plus(sc(qt(r),q),sc(qt(t),h))
        else: R=plus(sc(qt(r),k*q),sc(qt(s),h))
    s2=solve([[I(M),I(M,1)] for M in (P5,R)],[-I(M,2) for M in (P5,R)])
    if s2 is None:return
    p2,(v0,v1)=s2
    r0=(C4[0]-C4[2]*v0)%F; r1=(C4[1]-C4[2]*v1)%F
    N=(r0*r0-v1*r0*r1+v0*r1*r1)%F
    if N.gcd(F).degree():return
    return list(map(int,F.coeffs())),list(map(int,N.coeffs())),list(map(int,p3.coeffs())),list(map(int,p2.coeffs()))

def on_third(p,z0,slot):
    gp=nmod_poly([rr(c,p) for c in reversed(G.all_coeffs())],p)
    if gp(z0)!=0 or gp.derivative()(z0)==0:return
    try:
        ww,vv=(z0,0) if kind=='star' else [ev(x,z0,p) for x in (w_z,v_z)]
        uu,bb=[ev(x,ww,p) for x in (u_w,b_w)]
    except ValueError:return
    assert (uu+bb+2*vv-z0)%p==0
    rej=third(p,uu,bb,vv,slot)
    if rej:return (p,z0,uu,bb,vv,rej)

if __name__=='__main__':
    rows={
        'ghost': ((0,17,6),(1,17,1),(2,17,6)),
        'arith': ((0,59,28),(1,59,28),(2,59,28)),
        'star': ((0,13,9),),
    }
    for slot,p,z in rows[kind]:
        assert S.isprime(p) and p>7
        ans=on_third(p,z,slot)
        assert ans is not None
        print(kind,slot,ans)
