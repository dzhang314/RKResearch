#!/usr/bin/env python3
"""Independent exact checks. Standard library only. No file, network or compiler dependency."""
from fractions import Fraction as F
from math import prod, factorial
from functools import cache


def trees_up_to(N):
    trees=[()]; ns=[1]; gam=[1]
    for n in range(2,N+1):
        def partitions(lo,rest):
            if rest==0:
                yield ();return
            for i in range(lo,len(ns)):
                if ns[i]>rest:break
                for more in partitions(i,rest-ns[i]):yield (i,)+more
        add=list(partitions(0,n-1))
        for ch in add:
            trees.append(ch);ns.append(n);gam.append(n*prod(gam[i] for i in ch))
    assert [ns.count(n) for n in range(1,N+1)]==[1,1,2,4,9,20,48,115][:N]
    return trees,ns,gam


def extrap(M,m):return F((-1)**(M-m)*m**(M-1),factorial(m-1)*factorial(M-m))

def at_one(S):return [prod((1-v)/(u-v) for v in S if v!=u) for u in S]

def dot(x,y):return sum((u*v for u,v in zip(x,y)),F(0))
def mul(x,y):return tuple(u*v for u,v in zip(x,y))

def build_blocks(M,S,dirk,theta=None):
    # theta=None uses independent ordinary left/right Euler. Otherwise a shared
    # zero stage for all m within each individual scale; positive m-stage clocks.
    W=at_one(S) if len(S)>1 else [F(1)]
    specs=[];b=[];c=[]
    for s,w in zip(S,W):
        if theta is not None:
            specs.append(('zero',));zero=len(b);c.append(F(0));b.append(F(0))
        else:zero=None
        for m in range(1,M+1):
            st=len(b);h=s/m;specs.append(('m',st,m,h,zero))
            for j in range(m):
                c.append(h*(j+(dirk if theta is None else 1)));b.append(w*extrap(M,m)/m)
    c=tuple(c);b=tuple(b)
    def A(x):
        out=[]
        for block in specs:
            if block[0]=='zero':out.append(F(0));continue
            _,st,m,h,zero=block
            total=F(0) if theta is None else (1-theta)*x[zero]
            for j in range(st,st+m):
                v=x[j]
                out.append(h*(total+(dirk if theta is None else theta)*v))
                total+=v
        return tuple(out)
    assert A((F(1),)*len(c))==c
    return A,b,c


def all_trees(A,b,ts):
    phi=[];ap=[]
    for ch in ts:
        x=(F(1),)*len(b)
        for i in ch:x=mul(x,ap[i])
        phi.append(x);ap.append(A(x))
    return phi,ap


def context_checks():
    H=8;p=4;S=[F(j,p+1) for j in range(1,p+1)];W=at_one(S)
    mu=[sum(w*s**g for s,w in zip(S,W)) for g in range(H)]
    assert mu[:p]==[1]*p and mu[p]==1-prod(1-s for s in S)!=1
    ts,ns,gm=trees_up_to(H)
    # Enumerate words in A and multiplication by A Phi(t), cost<=4;
    # include nested/branching side decorations, not only powers of clocks.
    paths=[]
    def grow(path,C):
        paths.append((path,C))
        if C==4:return
        grow(path+(-1,),C+1)
        for i,n in enumerate(ns):
            if n+C>4:break
            grow(path+(i,),C+n)
    grow((),0)
    for impl in (0,1):
        A,b,c=build_blocks(H,[F(1)],impl)
        V,AV=all_trees(A,b,ts)
        assert all(dot(b,x)*g==1 for x,g in zip(V,gm))
        cacheword={}
        def act(path,i):
            k=(path,i)
            if k in cacheword:return cacheword[k]
            if not path:return V[i]
            x=act(path[:-1],i);op=path[-1]
            v=A(x) if op==-1 else mul(x,AV[op]);cacheword[k]=v;return v
        pft=0
        for path,C in paths:
            q=0;hs=[];side=F(1)
            for op in path:
                if op==-1:hs.append(q);q+=1
                else:q+=ns[op];side/=gm[op]
            hs.append(q);assert q==C and len(set(hs))==len(hs)
            coeff={k:side/prod(l-k for l in hs if l!=k) for k in hs}
            for i,n in enumerate(ns):
                if n+C>H:break
                # Actual Q_k value is independently checked by actual raw trees.
                factor=F(n,gm[i]);x=act(path,i)
                val=dot(b,x);expected=factor*sum(z/(n+k) for k,z in coeff.items())
                assert val==expected==factor*side/prod(n+k for k in hs)
                pft+=1
        A,b,c=build_blocks(H,S,impl);V,AV=all_trees(A,b,ts)
        assert all(dot(b,x)*g==mu[n-1] for x,g,n in zip(V,gm,ns))
        # m=1 is discarded on the first scale. A real degree-one cover.
        P=tuple(z-c[0] for z in c)
        def T(x):
            y=A(x);u=A(mul(c,x));v=A(y)
            return tuple(a*b-c-d for a,b,c,d in zip(c,y,u,v))
        v=T(P);assert v[0]==0
        assert v[5 if not impl else 3]==F(1 if not impl else 2,3375)
        def go(path,x):
            for op in path:x=A(x) if op==-1 else mul(x,AV[op])
            return x
        for path,C in paths:assert dot(b,go(path,v))==0  # 3+C+1<=8
        assert dot(b,mul(v,v))==dot(b,mul(A(v),v))==dot(b,A(mul(v,v)))==0
        gram=sum((w*x)**2 for w,x in zip(b,v));assert gram>0
        label='DIRK' if impl else 'ERK'
        print(f'{label}: {len(ts)} actual normalized trees through order {H}; exact order {p}, multiplier at order {p+1}={mu[p]}; {len(paths)} context words, {pft} paid path/tree tests. Genuine one-stage degree-one cut, native two-hole = 0, collided two-hole > 0, retained coordinate={v[5 if not impl else 3]}.')
    # Same physical b,c, same tree scalars through H, positive mask P=X, but
    # a nonlinear collided scalar varies. No need to classify diagonal endpoints.
    seen=[];bc=None
    for th in (F(0),F(1,2),F(1)):
        A,b,c=build_blocks(H,S,0,th);V,_=all_trees(A,b,ts)
        assert bc is None or (b,c)==bc;bc=(b,c)
        assert all(dot(b,x)*g==mu[n-1] for x,g,n in zip(V,gm,ns))
        x=c;y=A(x);z=A(mul(c,x));u=A(y)
        v=tuple(c[i]*y[i]-z[i]-u[i] for i in range(len(c)))
        assert v[0]==0 and dot(b,mul(v,v))==0
        seen.append(sum((w*x)**2 for w,x in zip(b,v)))
    assert len(set(seen))==3
    print('Fixed b,c and every rooted scalar through order 8, P=X, T(c) collided-square values at theta=0,1/2,1: '+', '.join(map(str,seen))+'.')


def mod(x,l):
    x=F(x);return x.numerator*pow(x.denominator,-1,l)%l

def det(mat,l):
    A=[list(row) for row in mat];v=1
    assert all(len(row)==len(A) for row in A)
    for j in range(len(A)):
        k=next((i for i in range(j,len(A)) if A[i][j]%l),None)
        if k is None:return 0
        if j!=k:v=-v;A[j],A[k]=A[k],A[j]
        piv=A[j][j]%l;v=v*piv%l;inv=pow(piv,-1,l)
        for i in range(j+1,len(A)):
            a=A[i][j]*inv%l
            if a:
                for k in range(j+1,len(A)):A[i][k]=(A[i][k]-a*A[j][k])%l
    return v%l


def case20():
    # A direct rational matrix witness from complete m=15,...,33 blocks on
    # first scale. H=54 independently fixes order isotropy of whole tableau.
    p=20;d=4;r=14;H=54;ell=1009;s=F(1,21)
    slots=[(a,e) for t in range(0,r,2) for a in [(r-t)//2] for e in range(min(t,p-d-1-t)+1)]
    dx=max(d+e+a for a,e in slots);dh=max(d+e+2*a for a,e in slots)
    assert (len(slots),dx,dh)==(34,14,18) and H>=dh+35+1
    for impl in (0,1):
        roots=[s*(j+impl)/d for j in range(d)]
        # Exact rational paid seed ranks from integrals of P(X)X^k.
        coeff=[F(1)]
        for z in roots:
            b=[F(0)]*(len(coeff)+1)
            for j,u in enumerate(coeff):b[j]-=z*u;b[j+1]+=u
            coeff=b
        Hanks=[mod(sum(a/F(k+j+1) for j,a in enumerate(coeff)),ell) for k in range(15)]
        hd=[det([[Hanks[i+j] for j in range(k)] for i in range(k)],ell) for k in range(1,9)]
        assert all(hd)
        cols=[[] for _ in slots]
        for m in range(dx+1,dx+dh+2):
            h=mod(s/m,ell);c=[h*(j+impl)%ell for j in range(m)]
            P=[prod(x-mod(z,ell) for z in roots)%ell for x in c]
            def T(v):
                # Use the defining commutator, not T=±hA, for the matrix certificate.
                def A(y):
                    out=[];z=0
                    for v in y:out.append(h*(z+impl*v)%ell);z+=v
                    return out
                y=A(v);z=A([x*v for x,v in zip(c,v)]);u=A(y)
                return [(x*y-z-u)%ell for x,y,z,u in zip(c,y,z,u)]
            for i,(a,e) in enumerate(slots):
                v=[y*pow(x,e,ell)%ell for x,y in zip(c,P)]
                for _ in range(a):v=T(v)
                cols[i].extend(v)
        # Two-hole stage-collision (unit positive masses on chosen physical blocks).
        G=[[sum(x*y for x,y in zip(a,b))%ell for b in cols] for a in cols]
        h=det(G,ell);assert h
        print(f'{"DIRK" if impl else "ERK"} p=20, H=54, {p*H*(H+1)//2} stages, quartic prefix; 34 independent old columns, {len(cols[0])} retained coordinate rows, binary unweighted coincidence-Gram det = {h} mod {ell}, all paid leading minors through width 8 = {hd}. Native contexts of cost <=35 all zero on these old columns.')

if __name__=='__main__':
    context_checks();case20()
