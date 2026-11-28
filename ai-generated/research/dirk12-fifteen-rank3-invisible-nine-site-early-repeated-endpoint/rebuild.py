#!/usr/bin/env python3
"""Exact characteristic-zero first-three endpoint projection (SymPy)."""
import json
from pathlib import Path
import sympy as S
a,x,y=S.symbols('a x y')
def L(t):
    return -42+840*t-5040*t*t+12600*t**3-13860*t**4+5544*t**5
D=2*x*y-x-3*y*y+2*y
P=6*x*x*y**3-18*x*x*y*y+20*x*x*y-10*x*x-4*x*y**4+8*x*y**3-6*x*y*y+5*x*y+2*y**4-3*y**3
G2=(2*x-1)*L(a*x)-x**3*(2*x*x-6*x+5)*L(a)
G3=(2*x-1)*D*L(a*y)+y*y*P*L(a)
G31=x*x*(x-1)**3*D*L(a*y)+y*y*(y-1)**3*(3*x*x-2*x*y-2*x+y)*L(a*x)
H0=264*x**5-530*x**4+406*x**3-139*x*x+21*x-1
H1=660*a**6-1782*a**5+1963*a**4-1099*a**3+321*a*a-44*a+2
H2=66*a**4-132*a**3+84*a*a-18*a+1
def N(g):return S.cancel(g).as_numer_denom()[0]
def coeff(f,z):return [int(c) for c in S.Poly(f,z).all_coeffs()[::-1]]
def main():
    assert S.expand(G2.subs(a,1)-42*(x-1)*H0)==0
    assert S.cancel(G2.subs(x,1/a)+42*(a-1)*H1/a**5)==0
    assert S.expand(L(a)-42*(2*a-1)*H2)==0
    C0=S.cancel(G2/(x-1))
    C1=S.cancel(N(G3.subs(y,1/a))/(a-1))
    C2=S.cancel(N(G31.subs(y,1/a))/(a*x-1))
    assert S.degree(C1,x)==2 and S.degree(C2,x)==6
    K=S.Poly(C2,x).LC()
    assert S.cancel(K/(a**5*(a-1)**3)).is_Integer
    assert S.rem(C2.subs(x,1),L(a),a)==0
    SS=S.subresultants(C0,C1,x)
    R=S.Poly(SS[-2],x)
    assert R.degree()==1
    factors=S.factor_list(SS[-1])[1]
    deg30,=[f for f,m in factors if S.degree(f,a)==30 and m==1]
    assert S.cancel(SS[-1]/(a*(2*a-1)*H1*H2*deg30)).is_Rational
    v,w=R.all_coeffs()
    assert S.gcd(v,H1)==1 and S.rem(v+a*w,H1,a)==0
    bases={"a1":coeff(H0,x),"b1":coeff(H1,a),"c1":coeff(deg30,a),
           "b1root":coeff(L(a),a),"c1root":coeff(L(a),a)}
    data=dict(base=bases, c2=[coeff(c,a) for c in S.Poly(C2,x).all_coeffs()[::-1]],
              linear=[coeff(c,a) for c in R.all_coeffs()])
    p=Path(__file__).with_name('projections.json')
    result=json.dumps(data,separators=(',',':'))+'\n'
    if p.exists():assert p.read_text()==result
    else:p.write_text(result)
    print("Exact scalar base degrees 5,6,5,5,30; first-root c=1 strips x=1 and ax=1")

if __name__=="__main__":
    main()
