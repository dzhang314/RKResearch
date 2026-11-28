from math import prod
from fractions import Fraction as F
from pathlib import Path
import json

base=[16,2,8,9,4,6] # a,c,d,e,f,g
def poly(r):
    f=[1]
    for z in r:
        s=[0]*(len(f)+1)
        for j,v in enumerate(f):s[j]-=z*v;s[j+1]+=v
        f=s
    return f
def mul(f,g):
    z=[0]*(len(f)+len(g)-1)
    for i,a in enumerate(f):
        for j,b in enumerate(g):z[i+j]+=a*b
    return z
def integ(f,m):
    return sum(v*pow(i+1,-1,m)for i,v in enumerate(f))%m
def primitive(f,m):
    return [0]+[v*pow(i+1,-1,m)%m for i,v in enumerate(f)]
def dot(x,y,m):
    return sum(a*b for a,b in zip(x,y))%m
def system(T,m,metadata=False):
    a,c,d,e,f,g=T;b=2*a%m
    nodes=[0,1,a,b,c,d,e,f,g]
    mu={z:integ(poly([y for i,y in enumerate(nodes)if i!=j]),m)for j,z in enumerate(nodes)}
    sc=integ(poly(nodes),m)
    early=(c*(c-b)*mu[c]+a*a*mu[a])%m
    G4=poly([0,a,b,c]);J=primitive(G4,m)
    Q=[0,0,0,b*b*pow(12,-1,m)%m,-b*pow(8,-1,m)%m,pow(20,-1,m)]
    E=poly([1,e,f,g]);D=[-x for x in poly([1,f,g])]
    A0=integ(mul(E,J),m);B0=integ(mul(E,Q),m)
    A1=integ(mul(D,J),m);B1=integ(mul(D,Q),m)
    def value(F,z):return dot(F,[pow(z,i,m)for i in range(len(F))],m)
    Z4d=(d-b)*(-a*a*mu[a]*d-mu[d]*d*d*(d-b))%m
    last=(Z4d*A1+4*mu[d]*value(G4,d)*B1)%m
    if metadata:
        H={z:-a*a*mu[a]*z*pow(4*mu[z],-1,m)%m for z in nodes[2:]}
        Z=lambda z:(z-b)*(H[z]-z*z*(z-b)*pow(4,-1,m))%m
        det=(value(G4,d)*Z(e)-value(G4,e)*Z(d))%m
        return [sc,early,A0,B0,last],(mu,det,(Z(d),Z(e)),A1,B1)
    return [sc,early,A0,B0,last]
def reduce(M,b,p):
    X=[[z%p for z in r]+[u%p] for r,u in zip(M,b)]
    piv=[]
    N=len(M[0])
    for j in range(N):
        i=len(piv)
        k=next((k for k in range(i,len(X))if X[k][j]),None)
        if k is None:continue
        piv.append(j);X[i],X[k]=X[k],X[i]
        t=pow(X[i][j],-1,p);X[i]=[z*t%p for z in X[i]]
        for k in range(len(X)):
            if k==i or not X[k][j]:continue
            u=X[k][j]; X[k]=[(a-u*b)%p for a,b in zip(X[k],X[i])]
    if any(row[-1] for row in X[len(piv):]):return piv,None
    y=[0]*N
    for j,row in zip(piv,X):y[j]=row[-1]
    return piv,y
def jac(x,p):
    s=system(x,p*p)
    return [[((system([v+(p if i==j else 0)for i,v in enumerate(x)],p*p)[k]-s[k])% (p*p))//p
              for j in range(len(x))]for k in range(len(s))]
if __name__=='__main__':
    assert system(base,17)==[0]*5
    print('initial guards',system(base,17,True))
    M=jac(base,17)
    print('Jacobian',M)
    print('Jacobian pivots',reduce(M,[0]*5,17)[0])
    sol={1:base}
    for k in range(1,9):
        q=17**k;p=17*q
        x=sol[k]; y=system(x,p)
        assert all(v%q==0 for v in y)
        piv,z=reduce(M,[-v//q for v in y],17)
        if z is None:
            print('no first-order lift at exponent',k+1,'defect',y)
            break
        xx=[x+q*y for x,y in zip(x,z)]
        assert system(xx,p)==[0]*5
        sol[k+1]=xx
        print('lift exponent',k+1,xx)
    Path('geometry-lifts.json').write_text(json.dumps(sol,indent=2)+'\n')
