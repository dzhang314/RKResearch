#!/usr/bin/env python3
"""Literal six-opening/eight-high rational construction, no external modules."""
from fractions import Fraction as F
from itertools import combinations
from pathlib import Path
import argparse
import json

def dot(a,b):return sum(x*y for x,y in zip(a,b))
def poly(roots):
    p=[F(1)]
    for c in roots:
        q=[F(0)]*(len(p)+1)
        for j,x in enumerate(p):q[j]-=c*x;q[j+1]+=x
        p=q
    return p
def ev(p,x):
    v=F(0)
    for q in p[::-1]: v=v*x+q
    return v
def lagrange(xs,j):
    p=poly([x for i,x in enumerate(xs)if i!=j])
    d=ev(p,xs[j])
    return [q/d for q in p]
def linear(m,b):
    n=len(m)
    x=[list(map(F,u))+[F(v)]for u,v in zip(m,b)]
    assert all(len(r)==n+1 for r in x)
    for i in range(n):
        k=next((j for j in range(i,n)if x[j][i]),None)
        if k is None:return
        x[i],x[k]=x[k],x[i]
        x[i]=[q/x[i][i]for q in x[i]]
        for j in range(n):
            if i!=j and x[j][i]:
                x[j]=[u-x[j][i]*v for u,v in zip(x[j],x[i])]
    return [row[-1]for row in x]
def expect(*args):
    z=linear(*args)
    assert z is not None
    return z

def make():
    A,C,D,E,V=map(F,("2/3","1/2","2","4/5","1/6"))
    x=[F(1),A,A,C,A,D,E,V]
    y=[1-z for z in x]
    roots=[F(0),F(1),A,C,D,E,V]
    m=[sum(v/F(i+1)for i,v in enumerate(lagrange(roots,j)))for j in range(7)]
    assert all(dot(m,[t**i for t in roots])==F(1,i+1)for i in range(9))
    w=[m[1],3*m[2],-3*m[2],m[3],m[2],m[4],m[5],m[6]]
    a,t=y[1],y[3]
    assert t==3*a/2
    y2=[z*z for z in y]; y3=[z**3 for z in y]
    L=[[F(0)]*8 for _ in range(8)]
    def row(i,taps):
        for j,z in taps:L[i][j]=z
        L[i][0]=y[i]-sum(L[i])
    row(1,[]);row(2,[(1,a)])
    u=[dot(r,y)-s*s/2 for r,s in zip(L[:3],y)]+[F(0)]*5
    row(3,enumerate(expect([[a,a],u[1:3]],[t*t/2,0]),1))
    g=[dot(r,y2)-s**3/3 for r,s in zip(L[:4],y)]+[F(0)]*4
    h=[dot(r,u)for r in L[:4]]+[F(0)]*4
    u[4],g[4],h[4]=[-sum(w[i]*r[i]for i in (1,2))/w[4]for r in (u,g,h)]
    row(4,enumerate(expect([y[1:4],y2[1:4],u[1:4]],[u[4]+a*a/2,g[4]+a**3/3,h[4]]),1))
    v=[i/2+j for i,j in zip(g,h)]
    defect=lambda z:(a+t)*z**3/3-a*t*z*z/2-z**4/4
    k=[dot(r,y3)-z**4/4 for r,z in zip(L[:5],y)]+[defect(y[5]),F(0),F(0)]
    pr=poly([F(0),E,V])
    at=[w[i]*k[i]*ev(pr,x[i])for i in range(6)]
    tau=dot(at,x[:6])/sum(at)
    pressure=poly([F(0),E,V,tau])
    assert tau==F(17,26)

    # Opening rows and genuine free tap at the third clean donor.
    p,q,r,e=map(F,("3/10","3/4","4/5","1/10"))
    s=2*p/3
    c=[F(0),e,s,p,q,r]
    old=[[],[e],[s-s*s/(2*e),s*s/(2*e)],[p/4,F(0),3*p/4],[],[]]
    def oldrow(i,add):
        u=c[i]
        v1,v2=u*u/2-add*q,u**3/3-add*q*q
        sv=(p*v1-v2)/(s*(p-s));pv=(v2-s*v1)/(p*(p-s))
        old[i]=[u-sv-pv-add,F(0),sv,pv]+([add]if i==5 else [])
    oldrow(4,F(0))
    def ann(f):
        oldrow(5,f)
        Q=[dot(old[i],[z**3 for z in c])-c[i]**4/4 for i in (3,4,5)]
        V0=[old[i][2]for i in (3,4,5)]
        return [Q[(i+1)%3]*V0[(i+2)%3]-Q[(i+2)%3]*V0[(i+1)%3]for i in range(3)]
    vals=[ev(pressure,z)for z in (p,q,r)]
    z0,z1=dot(ann(F(0)),vals),dot(ann(F(1)),vals)
    ft=-z0/(z1-z0)
    ell=ann(ft)
    assert ft==F(6128,131625)
    assert dot(ell,vals)==0 and ell[2]
    ellX=[dot(ell,[z**i for z in (p,q,r)])for i in range(5)]
    j=next(i for i in range(1,5)if ellX[i])
    H=[]
    for i in range(1,5):
        if i==j:continue
        g0=[F(0)]*5
        g0[i]=F(1);g0[j]=-ellX[i]/ellX[j]
        H.append(g0)
    Pi=[[F(0)]*6 for _ in range(4)]
    for i,z in enumerate((0,3,4,5)):
        for l,k0 in enumerate(lagrange([F(0),p,q,r],i)):Pi[l][z]=k0

    # Solve the three V payments and two remaining cubic payments.
    eta=expect([[w[i]*ev(g0,x[i])for i in (5,6,7)]for g0 in H],
               [-sum(w[i]*dot(L[i],v)*ev(g0,x[i])for i in range(5))for g0 in H])
    for gi,gj in combinations(H,2):
        G=[gi,gj]
        res=linear([[w[i]*ev(z,x[i])for i in (6,7)]for z in G],
                   [-sum(w[i]*k[i]*ev(z,x[i])for i in range(6))for z in G])
        if res is not None:
            k[6],k[7]=res
            break
    else:raise ValueError("cubic rank")
    for i in (5,6,7):
        m0=5 if i==5 else 6
        rows=[[F(1)]*m0,y[:m0],y2[:m0],u[:m0],v[:m0]]
        tgt=[y[i],y2[i]/2,y3[i]/3,F(0),eta[i-5]]
        if i>5:rows.append(y3[:m0]);tgt.append(y[i]**4/4+k[i])
        L[i][:m0]=expect(rows,tgt)
    for z in H:
        assert sum(w[i]*k[i]*ev(z,x[i])for i in range(8))==0
        assert sum(w[i]*dot(L[i],v)*ev(z,x[i])for i in range(8))==0

    outA=old[:]
    cx=x[::-1]
    for i,z in enumerate(cx):
        B=[w[7-j]*L[7-j][7-i]/w[7-i] for j in range(i)]
        d=[z**(k+1)/(k+1)-dot(B,[t**k for t in cx])for k in range(4)]
        outA.append([dot(d,[t[j]for t in Pi])for j in range(6)]+B)
    outb=[m[0],F(0),F(0),F(0),F(0),F(0)]+w[::-1]
    return {
       "A":[list(map(str,r))for r in outA],"b":list(map(str,outb)),
       "reverse_x":list(map(str,x)),"reverse_L":[list(map(str,r))for r in L],
       "third_donor_tap":str(ft),"pressure_root":str(tau),
       "donor_annihilator":list(map(str,ell)),
    }

if __name__=="__main__":
    p=argparse.ArgumentParser()
    p.add_argument("--emit",type=Path)
    args=p.parse_args()
    out=json.dumps(make(),indent=2)+"\n"
    if args.emit:args.emit.write_text(out)
    else:assert out==Path(__file__).with_name("tableau.json").read_text()
    print("Literal rational construction reproduced byte for byte.")
