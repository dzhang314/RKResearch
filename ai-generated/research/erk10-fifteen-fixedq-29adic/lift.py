"""Exact Hensel residuals for the origin-root branch of the fixed-q F29 chart.

Pass the original fixed-q spectrum directory as the first argument.
"""
from fractions import Fraction
from pathlib import Path
import sys

if len(sys.argv)>1: sys.path.insert(0,sys.argv[1])
import spectrum as S
import literal

PRIME=29
MOD=29
seed=(2,6,15,26,11,20)  # c,g,R,d,a,b

class Z:
    __slots__=("v",)
    def __init__(self,x=0,y=1):
        if isinstance(x,Z):x=x.v
        if isinstance(y,Z):y=y.v
        if isinstance(x,Fraction):
            x=x.numerator*pow(x.denominator,-1,MOD)
        try: self.v=int(x)*pow(int(y),-1,MOD)%MOD
        except ValueError as e: raise ZeroDivisionError("nonunit") from e
    def __add__(self,o):return Z(self.v+Z(o).v)
    __radd__=__add__
    def __sub__(self,o):return Z(self.v-Z(o).v)
    def __rsub__(self,o):return Z(Z(o).v-self.v)
    def __mul__(self,o):return Z(self.v*Z(o).v)
    __rmul__=__mul__
    def __truediv__(self,o):return Z(self.v,Z(o).v)
    def __rtruediv__(self,o):return Z(Z(o).v,self.v)
    def __pow__(self,n):return Z(pow(self.v,n,MOD))
    def __neg__(self):return Z(-self.v)
    def __eq__(self,o):return self.v==Z(o).v
    def __bool__(self):return bool(self.v)
    def __hash__(self):return hash(self.v)
    def __int__(self):return self.v
    def __str__(self):return str(self.v)
    __repr__=__str__

def residual(xs,mod):
    global MOD
    MOD=mod
    S.F=literal.F=Z
    c,g,R,d,a,b=map(Z,xs)
    e,f,h,M,JM=S.late(c,d,g,R)
    tau,s,p=d*e,a+b,a*b
    T=S.nodes([f,g,h])
    omega=(S.delta(c)-1)/c
    S4=S.mul([Z(1),Z(-1)],S.nodes([g,h,R]))
    k=S.moment(S.mul(S.mul([Z(0),Z(-1),Z(1)],S.nodes([c,c,R])),T))
    J=S.moment(S.mul(S.mul(S4,S.nodes([f,Z(0),c])),[Z(1),omega]))
    ell=J-2*k/c
    B=S.mul(S.mul([Z(0),Z(-1),Z(1)],S.nodes([c,d,e])),T)
    E0,E1=S.moment(B),S.moment(B,1)
    K,L=tau*k,tau*ell
    hd=((E0*R*c*c-2*K*c)*s+
        (-E0*R*c-E0*c*c+E1*c+2*K-L*c)*p-E1*R*c*c+K*c*c)
    V=S.cubic(c)
    Phi=S.mul(S.nodes([Z(1),c,d,e]),S.add(V,S.scale(T,-V[0]/T[0])))
    tl=S.moment(S.mul(Phi,[p,-s,Z(1)]))
    n=lambda z:(1-z)*S.val(V,z)/((1-R)*S.val(V,R))
    ordinary=[a,b,c,d,e,f,g,h,R]
    w=S.cardinal([Z(0),Z(1),a,b,c,d,e,f,g,h])
    uv={z:1/S.product(z-x for x in ordinary if x!=z) for z in ordinary}
    q=S.interp({z:w[z]*n(z)/(uv[z]*(z-R)) for z in [f,g]})
    eta={z:(z-R)*S.val(q,z)*uv[z]/w[z] for z in [a,b,d,e,f,g,h]}
    eta[R]=Z(1)
    true=[sum((z-c)*z**j*eta[z]*uv[z] for z in eta) for j in range(3)]
    return list(map(int,[hd,tl,k+ell]+true))

def jacobian(v):
    J=[[] for _ in v]
    base=residual(v,PRIME**2)
    for j in range(len(v)):
        tmp=tuple(x+(PRIME if h==j else 0) for h,x in enumerate(v))
        x=residual(tmp,PRIME**2)
        for i in range(len(v)):
            diff=(x[i]-base[i])%PRIME**2
            assert diff%PRIME==0
            J[i].append(diff//PRIME)
    return J

def inv_and_det(A):
    n=len(A); t=[list(a)+[int(i==j) for j in range(n)]for i,a in enumerate(A)]
    det=1
    for j in range(n):
        pivot=next((i for i in range(j,n) if t[i][j]),None)
        if pivot is None:return None,0
        if j!=pivot:
            t[j],t[pivot]=t[pivot],t[j];det=-det
        d=t[j][j];det=det*d%PRIME
        t[j]=[a*pow(d,-1,PRIME)%PRIME for a in t[j]]
        for i in range(n):
            if i!=j:
                m=t[i][j];t[i]=[(a-m*b)%PRIME for a,b in zip(t[i],t[j])]
    return [row[n:] for row in t],det%PRIME

def refine(v,k,M):
    r=residual(v,PRIME**(k+1))
    assert all(a%PRIME**k==0 for a in r)
    e=[-a//PRIME**k for a in r]
    corr=[sum(a*b for a,b in zip(row,e))%PRIME for row in M]
    vn=[x+y*PRIME**k for x,y in zip(v,corr)]
    assert residual(vn,PRIME**(k+1))==[0]*len(v)
    return vn


def unit_lin(mat,rhs,k):
    rows=[list(row)+[b] for row,b in zip(mat,rhs)]
    for j in range(k):
        w=next((i for i in range(j,len(rows)) if int(rows[i][j])%29),None)
        if w is None:raise ArithmeticError("no unit pivot")
        rows[j],rows[w]=rows[w],rows[j]
        a=rows[j][j];rows[j]=[x/a for x in rows[j]]
        for i in range(len(rows)):
            if i==j:continue
            a=rows[i][j]
            if a:rows[i]=[x-a*y for x,y in zip(rows[i],rows[j])]
    assert all(not row[-1] for row in rows[k:])
    return [row[-1] for row in rows[:k]]

def make_tableau(xs,mod):
    assert residual(xs,mod)==[0]*6
    c,g,R,d,a,b=map(Z,xs)
    im=S.late(c,d,g,R)
    sd=S.head(c,d,g,R,a,b,im,origin=True)
    z=S.nonlinear(sd)
    literal.lin=unit_lin
    mat,w,x=literal.full(sd,z,Z(1,8))
    return dict(A=[list(map(int,r)) for r in mat],b=list(map(int,w)),
                c=list(map(int,x)),modulus=mod,params=list(map(int,xs)))

def orders(tup):
    mat,b,x,m=[tup[k] for k in ("A","b","c","modulus")]
    assert all(mat[i][j]==0 for i in range(15) for j in range(i,15))
    assert x==[sum(row)%m for row in mat]
    sz=[1]; den=[1]; Ac=[[sum(row)%m for row in mat]]
    assert sum(b)%m==1
    def gen(rem,i,k):
        if not rem:yield ()
        else:
            for j in range(i,k):
                if sz[j]>rem:break
                for tail in gen(rem-sz[j],j,k):yield (j,)+tail
    import math
    count=1
    for j in range(2,11):
        k=len(sz)
        for ch in gen(j-1,0,k):
            ph=[math.prod(Ac[i][s] for i in ch)%m for s in range(15)]
            d=j*math.prod(den[i] for i in ch)
            assert (d*sum(a*b0 for a,b0 in zip(ph,b)))%m==1,(m,j,ch)
            den.append(d);sz.append(j)
            Ac.append([sum(u*v for u,v in zip(row,ph))%m for row in mat])
            count+=1
    assert count==1205
    defect=(11*sum(w*pow(y,10,m) for w,y in zip(b,x))-1)%m
    assert defect%29==10
    return defect

def main():
    import argparse,json
    ap=argparse.ArgumentParser()
    ap.add_argument("spectrum")
    ap.add_argument("--power",type=int,default=11)
    ap.add_argument("--save")
    ar=ap.parse_args()
    print("residual mod29 at seed:",residual(seed,PRIME))
    J=jacobian(seed)
    for row in J:print(row)
    M,d=inv_and_det(J);print("full Jacobian determinant mod29:",d)
    cols=(0,4,5)
    M,d=inv_and_det([[J[i][j] for j in cols] for i in range(3)])
    assert d==14
    print("head+origin 3×3 pivot in c,a,b:",d)
    xs=list(seed)
    tab=make_tableau(xs,29)
    assert orders(tab)==10
    for k in range(1,ar.power):
        res=residual(xs,29**(k+1))
        assert all(a%29**k==0 for a in res)
        err=[-(a//29**k) for a in res[:3]]
        for j,row in zip(cols,M):
            xs[j]+=29**k*(sum(a*b for a,b in zip(row,err))%29)
        assert residual(xs,29**(k+1))==[0]*6
        tab=make_tableau(xs,29**(k+1))
        d=orders(tab)
        print(f"mod29^{k+1}: 1205 all exact; normalized bush {d}; c,a,b",
              [xs[i] for i in cols])
    if ar.save:Path(ar.save).write_text(json.dumps(tab,indent=2)+"\n")

if __name__=="__main__":main()
