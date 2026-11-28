#!/usr/bin/env python3
"""Regenerate the exact characteristic-zero quartic-mask projection.

Only this derivation requires SymPy. verify-quartic.py independently
checks the residue layer with the Python standard library.
"""
import json
from pathlib import Path
import sympy as S

a,x,y,T=S.symbols("a x y T")
D=2*x*y-x-3*y*y+2*y
U=3*x*x-2*x*y-2*x+y
V=(6*x*x*y**3-18*x*x*y*y+20*x*x*y-10*x*x
   -4*x*y**4+8*x*y**3-6*x*y*y+5*x*y+2*y**4-3*y**3)
def L(z):
    return -42+840*z-5040*z*z+12600*z**3-13860*z**4+5544*z**5
def zeros(expr, numdegree, expected):
    factors=S.factor_list(expr)[1]
    keep=[p for p,e in factors if S.degree(p,a)>0]
    guards=[(p,e) for p,e in factors if S.degree(p,a)==0]
    assert len(keep)==1 and S.degree(keep[0],a)==numdegree
    assert guards==expected
    return keep[0]
def encode(p):
    return [[i,j,int(z)] for (i,j),z in S.Poly(p,a,x).terms()]
def projection(typ, H,J, retained, dropped):
    sr=S.subresultants(H,J,a)
    out=S.Poly(sr[-2],a)
    assert out.degree()==1
    sf=S.factor_list(sr[-1])[1]
    bits=[(S.Poly(p,x),e) for p,e in sf if S.degree(p,x)>2]
    skip=[(p,e) for p,e in sf if S.degree(p,x)<=2]
    assert [p.degree() for p,e in bits]==retained
    assert all(e==1 for p,e in bits) and skip==dropped
    return dict(G=[encode(H),encode(J)], linear=[encode(p) for p in out.all_coeffs()],
                factors=[[int(n) for n in f.all_coeffs()[::-1]] for f,e in bits])
def main():
    P=T*(T-1)*(T-x)*(T-y)
    def FJ(f,v): return sum(c*v**(i+1)/(i+1) for (i,),c in S.Poly(f,T).terms())
    I0=FJ(P,1)
    rho=x**3*(2*x*x-6*x+5)/(2*x-1)
    assert S.cancel(I0+(10*x*y-5*x-5*y+3)/60)==0
    mm=S.factor(FJ(P,x)-x*rho*I0)
    assert S.cancel(mm-x**3*(x-1)**3*(2*x*y-x-y)/(6*(2*x-1)))==0
    y0=x/(2*x-1);y1=(5*x-3)/(10*x-5)
    def pn(expr,v): return S.cancel(expr.subs(y,v)).as_numer_denom()[0]
    A=zeros(x**3*(2*x*x-6*x+5)*L(a)-(2*x-1)*L(a*x),5,[(x-1,1)])
    B=zeros(pn((2*x-1)*D*L(a*y)+y*y*V*L(a),y0),5,[(x,1),(x-1,2)])
    C=zeros(pn(x*x*(x-1)**3*D*L(a*y)+y*y*(y-1)**3*U*L(a*x),y1),5,
            [(5*x*x-5*x+1,1),(10*x*x-10*x+3,1)])
    pr=dict(nonroot=projection("nonroot",A,B,[26],[(x-1,5),(x,15),(2*x*x-2*x+1,2)]),
            firstroot=projection("firstroot",L(a),C,[8,32],[(x-1,5),(5*x-2,5)]))
    dst=Path(__file__).with_name("quartic-projection.json")
    out=json.dumps(pr,separators=(",",":"))+"\n"
    if dst.exists():
        assert dst.read_text()==out
    else:
        dst.write_text(out)
    print("characteristic zero: exact Möbius substitutions, retained x degrees 26 | 8,32, linear a subresultants")

if __name__=="__main__":
    main()
