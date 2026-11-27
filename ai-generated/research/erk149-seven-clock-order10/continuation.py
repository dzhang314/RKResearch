#!/usr/bin/env python3
from pathlib import Path
from itertools import combinations,product
import sys
HERE=Path(__file__).resolve().parent
WITNESS=Path(sys.argv[1]) if len(sys.argv)>1 else HERE/'../../upper-bounds/real-algebraic/erk14-order9-seven-clock'
sys.path.insert(0,str(WITNESS))
from cert import *
def dot(x,y):return sum(a*b for a,b in zip(x,y))
def pull(weighted,word,source):
    x,weights,L=weighted
    a=[Box(1)]*len(x)
    f=[Box(1)]
    def jstar(p):
        J=[0]+[(u+Box(0))/(k+1)for k,u in enumerate(p)]
        return [sum(J),*[-u for u in J[1:]]]
    def pevals(p):
        return [polval(p,z+Box(0))for z in x]
    def adj(v):return [dot(row,v)for row in L]
    for c in word:
        if c=='C':
            a=[u*v for u,v in zip(a,x)]
            f=[Box(0)]+f
        else:
            a=adj(a)
            f=jstar(f)
    r0=[z-s for z,s in zip(adj(a),pevals(jstar(f)))]
    r1=[z-s for z,s in zip(a,pevals(f))]
    J=[Box(0)]+[(u+Box(0))/(k+1)for k,u in enumerate(source)]
    return sum(w*(u*x-v*y)for w,u,v,x,y in zip(weights,r0,r1,pevals(source),pevals(J)))
def rank(M):
    U=[r[:]for r in M]; d=0;piv=[]
    for k in range(len(U[0])):
        p=next((i for i in range(d,len(U))if U[i][k]),None)
        if p is None:continue
        U[d],U[p]=U[p],U[d]
        U[d]=[u/U[d][k]for u in U[d]]
        for i in range(d+1,len(U)):
            U[i]=[a-U[i][k]*b for a,b in zip(U[i],U[d])]
        d+=1;piv.append(k)
    return d,piv
def main():
    A0,Pi=read_prefix(WITNESS/'prefix.json')
    ph0=prefix(A0,Pi)
    X=verify_geometry()
    x=X[0]
    cs,W,_,L=eval_geometry(X)
    weighted=cs,W,L
    D=prod_poly(([0,1],[-x,1],[-x/2,1]))
    Q=polmul(D,[0,-x,1])
    six=[]
    for word in product('CT',repeat=3):
        word=''.join(word)
        p=[pull(weighted,word,f)for f in (D,Q)]
        six.append((word,p))
        print('size-six',word,[u.print()for u in p])
    c=next((a,b,a[1][0]*b[1][1]-a[1][1]*b[1][0])for a,b in combinations(six,2)
           if (a[1][0]*b[1][1]-a[1][1]*b[1][0]).sign())
    print('independent size-six exterior word functionals:',c[0][0],c[1][0],'det',c[2].print())
    seven=[]
    for t in trees(6):
        Phi=ph0(t)
        h=[-dot(c,Phi) for c in Pi]+[F(0),F(7,fact(t))]
        assert sum(h)==0 and h[0]==0
        f=[v*x**(6-k)for k,v in enumerate(h)]
        p=pull(weighted,'CC',f)
        seven.append((t,h,p))
    rr,dd=rank([h for _,h,_ in seven]),rank([h for t,h,_ in seven if all(sz(u)<=5 for u in t)])
    assert rr[0]==4 and dd[0]==3
    print('size-seven spaces',rr,'direct',dd)
    rows=[seven[i][1] for i in (0,2,5)]
    assert all(all(sz(v)<=5 for v in seven[i][0])for i in (0,2,5))
    shape=prod_poly(([0,1],[-1,1],[F(-1,2),1]))
    assert [dot(list(k),[-9,F(27,2),18])for k in zip(*rows)]==shape+[0]*3
    assert [dot(list(k),[F(9,2),F(27,4),-27])for k in zip(*rows)]==[0]+shape+[0]*2
    def src6(i):
        t=trees(5)[i];P=ph0(t)
        assert all(sz(v)<=5 for v in t)
        return [-dot(c,P)for c in Pi]+[F(6,fact(t)),F(0)]
    pieces=list(zip(src6(0),src6(2)))
    assert [dot(list(k),[-9,27])for k in pieces]==shape+[0]*3
    assert [dot(list(k),[3,-6])for k in pieces]==polmul(shape,[0,-1,1])+[0]
    print('four explicit rational direct-source combinations checked')
    good=next((t,g)for t,h,g in seven if g.sign() and all(sz(u)<=5 for u in t))
    print('isolated actual size-seven source',good[0],'strict CC payment',good[1].print())
    A,b,_=build(X,A0,Pi)
    ph=rk(A)
    t=((),(),good[0])
    e=sum(s*v for s,v in zip(ph(t),b))-F(1,fact(t))
    assert e.sign()==good[1].sign()
    assert e.l<=good[1].h and good[1].l<=e.h
    print('actual tree',t,'factorial',fact(t),'raw defect',e.print())
    tangent(X,A0,Pi,t)
def tangent(X,A0,Pi,t):
    x,*u=X
    def Dmom(k):
        return Box(1)/(k+4)-3*x/(2*(k+3))+x*x/(2*(k+2))
    m=[Dmom(k+1)-Dmom(k)for k in range(5)]
    de=m[0]*m[2]-m[1]*m[1]
    assert de.sign()
    h0=(m[1]*m[3]-m[2]*m[2])/de
    h1=(m[1]*m[2]-m[0]*m[3])/de
    H=[h0,h1,Box(1)]
    h9=m[2]*h0+m[3]*h1+m[4]
    assert h9.sign()
    c=cubic(Dual(x,1))
    dq=[k*Dual(c[k]).x for k in range(1,4)]
    ux=[-polval(c,z).d/polval(dq,z)for z in u]
    ue=[-polval(H,z)/polval(dq,z)for z in u]
    dx=condition(Dual(x,1),*[Dual(z,d)for z,d in zip(u,ux)]).d
    de=condition(Dual(x),*[Dual(z,d)for z,d in zip(u,ue)]).d
    shear=-de/dx
    dz=[a+b*shear for a,b in zip(ue,ux)]
    print('degree-eight precision family dxi/depsilon',shear.print())
    g=(Dual(x,shear),*[Dual(z,d)for z,d in zip(u,dz)])
    A,b,_=build(g,A0,Pi)
    ph=rk(A)
    deriv=lambda t:sum(s*v for s,v in zip(ph(t),b)).d
    bad=deriv(t)
    bush=deriv(((),)*9)
    assert bad.sign() and bush.sign() and bush.sign()==(-h9).sign()
    assert bush.l<=(-h9).h and (-h9).l<=bush.h
    print('derivative of exact B10 clock defect',bush.print())
    print('derivative of the isolated factorial-70 raw defect',bad.print())
if __name__=='__main__':main()
