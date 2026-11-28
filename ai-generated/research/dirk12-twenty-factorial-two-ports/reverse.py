"""Paid raw reverse actions and exact integral null directions."""
from fractions import Fraction as Q
from math import lcm, prod
from arith import cardinals, ev, lin, vecmul, strip, matrix_paid, xgcd

def syzygies(v):
    d=lcm(*(Q(e).denominator for e in v))
    a=[int(z*d) for z in v]
    n=len(a)
    I=[[int(i==j) for j in range(n)] for i in range(n)]
    if not any(a):
        return I
    k=n-1
    for j in range(k):
        if not a[j]:continue
        u,v,d=xgcd(a[k],a[j])
        c=-a[j]//d
        e=a[k]//d
        for row in I:
            m,z=row[k],row[j]
            row[k]=u*m+v*z
            row[j]=c*m+e*z
        a[k]=d;a[j]=0
    assert a[-1] and not any(a[:-1])
    return [[row[j] for row in I] for j in range(n-1)]


def reduce_ranktwo(x,w,F):
    n=len(x)
    P=[Q(1)-q for q in x]
    y=lambda k:[v**k for v in P]
    W=[vecmul(w,y(k)) for k in range(6)]
    k=[Q(0)]+[Q(1)/(x[i]*prod(x[i]-x[j] for j in range(1,n) if i!=j)) for i in range(1,n)]
    cp=cardinals(x[1:4])
    vals=[w[i]*P[i]**3/(6*k[i]) for i in (1,2,3)]
    G=[cof*sum(q*ev(p,u) for q,p in zip(vals,cp,strict=True)) for u,cof in zip(x,k,strict=True)]
    D=[z-w/6 for z,w in zip(G,W[3],strict=True)]
    assert D[:4]==[0]*4
    Q1=[a/2 for a in W[2]]
    Q2=[a/3+g for a,g in zip(W[3],G,strict=True)]
    Q3=[a/4+Q(3,2)*t*g for a,t,g in zip(W[4],P,G,strict=True)]
    TG=[t*g/2 for t,g in zip(P,G,strict=True)]
    cols=(W[1],Q1,Q2,Q3)
    fit=[[Q(0)]*n for _ in range(n)]
    for i in range(1,4):
        fit[i][0]=w[i]*P[i]/(2*w[0])
        fit[i][i]=P[i]/2
    assert all(strip(t.numerator)==1 for t in w[:4])
    pol=cardinals(tuple(P[:4]))
    for i in range(4,n):
        fit[i][i]=P[i]/4
        v=[o[i]-fit[i][i]*inp[i] for inp,o in zip(W,cols)]
        for j,p in enumerate(pol):
            fit[i][j]=sum(c*t for c,t in zip(p,v,strict=True))/w[j]
    for V,O in zip([*W[:4],G],[*cols,TG],strict=True):
        assert lin(fit,V)==O
    cofs=[]
    for i in range(4,n):
        for q in syzygies(D[4:i+1]):
            v=[Q(0)]*4+list(q)+[Q(0)]*(n-i-1)
            assert sum(a*b for a,b in zip(v,D,strict=True))==0
            for j,p in enumerate(pol):
                v[j]=-sum(v[l]*w[l]*ev(p,P[l]) for l in range(4,i+1))/w[j]
            assert all(sum(a*b for a,b in zip(v,T,strict=True))==0 for T in (*W[:4],G))
            cofs.append((i,v))
    U=vecmul(x,G)
    targets=(W[4],U)
    gam=([v/5 for v in W[5]], [0]*n)
    R=[];rhs=[]
    for f in F:
        d=[ev(f,z) for z in x]
        for T,tm in zip(targets,gam,strict=True):
            img=lin(fit,T)
            rhs.append(sum(q*(t-w) for q,t,w in zip(d,tm,img,strict=True)))
            R.append([d[i]*sum(a*b for a,b in zip(v,T,strict=True)) for i,v in cofs])
    assert matrix_paid(R,rhs)
    assert all(strip(Q(a).denominator)==1 for row in fit for a in row)
    assert all(strip(Q(a).denominator)==1 for i,v in cofs for a in v)

    def reconstruct(vals):
        A=[r[:] for r in fit]
        for (i,v),s in zip(cofs,vals,strict=True):
            for j,a in enumerate(v):
                A[i][j]+=a*s
        for V,O in zip([*W[:4],G],[*cols,TG],strict=True):
            assert lin(A,V)==O
        for f in F:
            d=[ev(f,z) for z in x]
            for T,tm in zip(targets,gam,strict=True):
                img=lin(A,T)
                assert not sum(q*(t-w) for q,t,w in zip(d,tm,img,strict=True))
        return A

    return R,rhs,reconstruct,G,fit,cofs
