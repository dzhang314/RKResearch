"""Explicit maximal minor selecting an exact algebraic diagonal projection."""
from coprime_one_front_finiteness import *

def pivot_columns(columns,p):
    rows=[list(row) for row in zip(*columns)]
    n,m=len(rows),len(columns)
    i=0;j0=[];a=1
    for j in range(m):
        k=next((k for k in range(i,n) if rows[k][j]),None)
        if k is None:continue
        if k!=i:
            rows[k],rows[i]=rows[i],rows[k]
            a=-a
        t=rows[i][j]
        a=a*t%p
        ti=pow(t,-1,p)
        for k in range(i+1,n):
            if rows[k][j]:
                b=rows[k][j]*ti%p
                rows[k][j:]=[(x-b*y)%p for x,y in zip(rows[k][j:],rows[i][j:])]
        j0.append(j);i+=1
        if i==n:break
    assert i==n and a%p
    return j0,a%p

def test_matrix(front,slot,rear,p,t,gg):
    Et,Ea,D,T,q0,q1,ds=tail(front,slot,rear)
    d=choose_poly(D,p,t,gg)
    assert d.degree()==7
    S=Bfield(d,p,t);s0=S(nmod_poly([0,1],p));g0=S(gg)
    a,b,c=[ev_poly(P,0,S,p,0,t,g0,s0) for P in (Et,Ea,T)]
    assert len(a)==4 and len(c)==(3 if rear else 6)
    a[-1].inv();c[-1].inv()
    Y=Tower(mon(a));y0=Y.gen()
    W=Nested(mon(list(map(Y,c))));u0=W.gen()
    Q=[]
    for q in (q0,q1):
        v=ev_poly(q,0,S,p,0,t,g0,s0)
        assert len(v)<=1
        Q.append(W(Y(v[0] if v else S(0))))
    gx,ax,sx,yx=W(Y(g0)),W(Y(S(ds[5]))),W(Y(s0)),W(y0)
    RR=remainders(W,gx,ax,sx,yx,u0,rear,Q)
    EA=W(ev(list(map(Y,b)),y0))
    n1,n2,n3=7,3,len(c)-1
    def coords(x):
        z=[]
        for k in range(n3):
            v=x.x[k] if k<len(x.x) else Y(0)
            for j in range(n2):
                w=v.x[j] if j<len(v.x) else S(0)
                z+=[int(w.x[i])%p for i in range(n1)]
        return z
    base=[(sx**i)*(yx**j)*(u0**k) for k in range(n3) for j in range(n2) for i in range(n1)]
    ans,val=pivot_columns([coords(f*x) for f in (EA,RR) for x in base],p)
    return len(base),ans,val
