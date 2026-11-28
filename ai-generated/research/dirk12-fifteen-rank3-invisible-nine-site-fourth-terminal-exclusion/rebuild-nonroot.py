#!/usr/bin/env python3
"""Exact characteristic-zero nonroot e=1 projection. SymPy and python-flint."""
import sympy as s
import flint as f
import json
from pathlib import Path

a,x,y,T=s.symbols('a x y T')
L=lambda z:5544*z**5-13860*z**4+12600*z**3-5040*z*z+840*z-42
D=2*x*y-x-3*y*y+2*y
P=6*x*x*y**3-18*x*x*y*y+20*x*x*y-10*x*x-4*x*y**4+8*x*y**3-6*x*y*y+5*x*y+2*y**4-3*y**3
G2=s.cancel(((2*x-1)*L(a*x)-x**3*(2*x*x-6*x+5)*L(a))/(x-1))
Yraw=(2*x-1)*D*L(a*y)+y*y*P*L(a)
G3,rem=s.div(Yraw,(y-1)*(y-x),y)
assert s.cancel(rem/G2).as_numer_denom()[1]==1
U=T*(T-1)*(T-x)*(T-y)
def J(m,z):
    return sum(k*z**(j+1)/(j+1) for (j,),k in s.Poly(m,T).terms())
I0,I1=J(U,1),J(T*U,1)
rho=x**4*(2*x*x-6*x+5)/(2*x-1)
D0,D1=J(U,x)-rho*I0,J(T*U,x)-rho*I1
assert s.cancel(I0*D1-I1*D0-x**3*(x-1)**3*D/360)==0
GE=s.cancel(360*a*L(a)*(J(U,1/a)*D1-J(T*U,1/a)*D0)-42*x**3*(x-1)**3*D).as_numer_denom()[0]
fact=s.factor_list(GE)[1]
expected=[(a-1,1),(x,3),(x-1,3)]
assert [(v,m) for v,m in fact if s.degree(v,y)==0]==expected
GE,=[u for u,m in fact if s.degree(u,y)>0 and m==1]
C=f.fmpz_mpoly_ctx.get(('a','x','y'))
def mpoly(p):
    return C.from_dict({l:int(z) for l,z in s.Poly(p,a,x,y).terms()})
G2,G3,GE=map(mpoly,(G2,G3,GE))

def rebuild():
    H0=G3.resultant(GE,2)
    fac=H0.factor()[1]
    assert [(d.degrees(),m) for d,m in fac]==[((1,0,0),1),((49,22,0),1)]
    assert fac[0][0]==C.gens()[0]
    H=fac[1][0];Q=G2.resultant(H,1)
    assert Q.degrees()==(302,0,0)
    forms=Q.factor()[1]
    assert [(d.degrees()[0],m) for d,m in forms]==[(5,1),(30,1),(105,1),
                                                     (6,5),(1,15),(4,15),(1,57)]
    def coeff(P):
        D=P.to_dict();return [int(D.get((i,0,0),0)) for i in range(int(P.degrees()[0])+1)]
    assert [coeff(P) for P,m in forms[4:]]==[[-1,2],[1,-18,84,-132,66],[0,1]]
    A=[coeff(d) for d,m in forms[:4]]
    aset=f.fmpq_poly([0,1]);one=f.fmpq_poly([1])
    read=lambda x:json.loads(x.read_text())
    prev=Path(__file__).parent.parent/'dirk12-fifteen-rank3-invisible-nine-site-early-repeated-endpoint'/'projections.json'
    Csource=read(prev)
    assert A[1]==Csource['base']['c1'] or A[1]==[-c for c in Csource['base']['c1']]
    def rows(p):
        return [[*map(int,i),int(z)] for i,z in p.to_dict().items()]
    data=dict(a=A,G2=rows(G2),G3=rows(G3),GE=rows(GE),H=rows(H),linear=Csource['linear'])
    for j in (0,1,3):
        M=f.fmpq_poly(A[j])
        def inv(u):
            dd,uu,vv=u.xgcd(M);assert dd==one
            return uu%M
        t=inv(aset)
        v,w=map(f.fmpq_poly,data['linear'])
        x0=one if j==0 else t if j==3 else ((-w*inv(v))%M)
        def value(R,y0):
            ap=[(aset**i)%M for i in range(max(i for i,k,l,c in R)+1)]
            xp=[(x0**k)%M for k in range(max(k for i,k,l,c in R)+1)]
            yp=[(y0**l)%M for l in range(max(l for i,k,l,c in R)+1)]
            return sum((c*ap[i]*xp[k]*yp[l])%M for i,k,l,c in R)%M
        assert not value(data['G2'],one)
        if j==1:
            assert not value(data['G3'],t)
    return data

def main():
    data=rebuild()
    p=Path(__file__).with_name('nonroot-projection.json')
    o=json.dumps(data,separators=(',',':'))+'\n'
    if p.exists():assert p.read_text()==o
    else:p.write_text(o)
    print("Nonroot exact double resultants; a factors 5,30,105,6 and exact lifted collision roots")
if __name__=="__main__":main()
