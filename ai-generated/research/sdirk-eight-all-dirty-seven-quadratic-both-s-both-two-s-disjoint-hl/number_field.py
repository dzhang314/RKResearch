from sympy import QQ, Poly, Symbol
from flint import fmpq_poly
U=Symbol('u')
def field(P):
    P0=Poly.from_dict({(int(i),):int(v) for (i,j,k),v in P.to_dict().items()},U,domain=QQ)
    assert P0.is_irreducible and P0.degree()==P.total_degree()
    if P0.degree()==1:return P0,QQ,QQ.convert(-P0.nth(0)/P0.nth(1))
    K=QQ.algebraic_field((P0,U))
    return P0,K,K.unit
def spec(P,R,u):
    K=R.domain
    h=fmpq_poly(list(reversed(K.mod.to_list()))) if hasattr(K,'mod') else fmpq_poly([-u,1])
    cs={}
    for (i,j,k),a in P.to_dict().items():cs.setdefault(int(j),{})[int(i)]=int(a)
    out={}
    for j,q in cs.items():
        coeff=[0]*(1+max(q))
        for i,c in q.items():coeff[i]=c
        rem=fmpq_poly(coeff)%h
        if rem:out[(j,)]=K.new(list(reversed(rem.coeffs()))) if hasattr(K,'mod') else K.convert(rem[0])
    return R.from_dict(out)
def gcd(a,b):
    while b:
        r=a%b
        a,b=b,(r.monic() if r else r)
    return a.monic() if a else a
def trim(a,mask):
    assert mask
    while (g:=gcd(a,mask)).degree()>0:a=a.exquo(g).monic()
    return a
