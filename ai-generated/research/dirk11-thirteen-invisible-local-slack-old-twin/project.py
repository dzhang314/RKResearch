#!/usr/bin/env python3
"""Exact degree-24 old-twin projection and all-branch repeat/fifth unit checks."""
import argparse
from fractions import Fraction
from hashlib import sha256
from pathlib import Path
from runpy import run_path
import sympy as S

X,z,t=S.symbols("X z t")
D24_COEFFS=(1940962832424,-31055405318784,235804110840144,
 -1130049909450000,3834915888814164,-9801701463985200,19593743040411624,
 -31403970051684048,41046670451615094,-44269862603032080,39715904883399948,
 -29791570226650596,18737987585745663,-9889743125578140,4374831636922230,
 -1616813832771000,496494644937750,-125655124770000,25904349346000,
 -4277991825000,552372525000,-53742150000,3708450000,-162000000,3375000)
D=S.Poly.from_list(D24_COEFFS,gens=z,domain=S.QQ)
rat=lambda c:Fraction(int(S.Rational(c).p),int(S.Rational(c).q))
def up(a): return S.Poly(a,z,domain=S.QQ)
def mod(a): return up(a).rem(D)
def div(a,b):
    g=mod(b).invert(D)
    assert (g*mod(b)).rem(D).is_one
    return (mod(a)*g).rem(D)
def prim(poly):
    return [poly[0].r.to(0)]+[a/(j+1) for j,a in enumerate(poly)]
def ev(poly,y):
    a=y.r.to(0)
    for c in reversed(poly): a=a*y+c
    return a
def pm(poly,k):
    return [k.to(rat(poly.nth(i))) for i in range(poly.degree()+1)]
def mul(f,g):
    o=f[0].r.to(0); c=[o]*(len(f)+len(g)-1)
    for i,a in enumerate(f):
        for j,b in enumerate(g): c[i+j]+=a*b
    return c
def sub(a,b):
    n=max(len(a),len(b)); o=a[0].r.to(0)
    return [(a[i] if i<len(a) else o)-(b[i] if i<len(b) else o) for i in range(n)]

def exact_projection():
    R=(X-z)*(X**2-(2*t+S.Rational(3,5))*z*X+t*z*z)
    p=S.Poly(X*(1-X)*R,X)
    mass=[sum(c/S.Integer(i+j+1) for (i,),c in p.terms()) for j in range(6)]
    M=S.Matrix(4,3,lambda i,j:mass[i+j])
    minors=[]
    for inds in [(0,1,2),(0,1,3),(0,2,3),(1,2,3)]:
        m=S.Poly(M[list(inds),:].det(method='domain-ge'),t,z,domain=S.QQ)
        minors.append(m.clear_denoms()[1].primitive()[1].as_expr())
    f,g,h,i=minors
    r1=S.resultant(f,g,t); r2=S.resultant(f,h,t); r3=S.resultant(f,i,t)
    assert up(S.gcd(r1,r2)).monic()==up(z**9*D.as_expr()).monic()
    assert mod(r3).is_zero and D.is_irreducible
    # Two polynomial pseudodivision identities prove that the final
    # linear polynomial vanishes at every *actual* common root.
    f,g=S.Poly(f,t,domain=S.QQ[z]),S.Poly(g,t,domain=S.QQ[z])
    u,r=f.pdiv(g)
    assert f*g.LC()**(f.degree()-g.degree()+1)==u*g+r and r.degree()==2
    u,l=g.pdiv(r)
    assert g*r.LC()**(g.degree()-r.degree()+1)==u*r+l and l.degree()==1
    tv=div(-l.nth(0),l.nth(1))
    def substitute(e):
        p=S.Poly(e,t)
        return sum((mod(v)*tv**k[0]).rem(D) for k,v in p.terms()).rem(D)
    J=[substitute(e) for e in mass]
    j0,j1,j2,j3,*_=J
    pivot=(j0*j2-j1*j1).rem(D)
    assert not pivot.is_zero
    inv=pivot.invert(D)
    assert (inv*pivot).rem(D).is_one
    su=((j0*j3-j1*j2)*inv).rem(D)
    pr=((j1*j3-j2*j2)*inv).rem(D)
    assert all((J[k+2]-su*J[k+1]+pr*J[k]).rem(D).is_zero for k in range(4))
    assert all(substitute(m).is_zero for m in minors)
    print("Hermite old-clock contact: exact irreducible degree24, linear t, unique later quadratic",flush=True)
    return tv,su,pr

def ranks(research,prime):
    assert S.isprime(prime) and prime>11
    here=Path(__file__).resolve().parent
    dep=research/'dirk11-thirteen-invisible-six-constant-exclusion'/'replay.py'
    assert sha256(dep.read_bytes()).hexdigest()==(here/'ring.sha256').read_text().strip()
    Ring,det=(lambda d:(d['Ring'],d['det']))(run_path(str(dep)))
    tv,su,pr=exact_projection()
    F=Ring('base residue',prime=prime)
    F.to(rat(D.LC())).inv()
    K=Ring('z',F,pm(D.monic(),F)[:-1])
    z=K.gen()
    t=ev(pm(tv,K),z)
    s=ev(pm(su,K),z); p=ev(pm(pr,K),z)
    U=Ring('literal fourth V, with B=s−V',K,[p,-s]); V=U.gen(); B=U.to(s)-V
    W=Ring('one of the two other old clocks',U,[U.to(t*z*z),-U.to((2*t+Fraction(3,5))*z)])
    t=U.to(t); z=U.to(z); zero,one=U.to(0),U.to(1)
    lam=t/(4*t-Fraction(6,5))
    mark=[-z,one]
    R=mul(mark,[t*z*z,-(2*t+Fraction(3,5))*z,one]); P0=[zero,*R]
    m=[Fraction(3,10)*z*z,-Fraction(6,5)*z,one]; P=[zero,*m]
    IP0=prim(P0); IQ=prim(mul(mark,P))
    old=Ring('all three old weighted numerical clocks',U,R[:-1]); y=old.gen()
    def oldread(cs): return ev(list(map(old.to,cs)),y)
    mi=oldread(m).inv()
    W0=(oldread(IP0[1:])*mi).v
    rho=(oldread(prim(prim(P))[1:])*mi).v
    def polar(v): return (v-z)**2*lam-ev(rho,v)
    def pivot_read(v): return (v,z,ev(P,v),ev(P0,v),ev(IP0,v),ev(W0,v),polar(v),ev(IQ,v))
    args=pivot_read(V)
    def hinge(d,V,z,PV,P0V,IP0V,W0V,S0,IV):
        return (IP0V-d*P0V)*(S0-(V-z)*d)-W0V*(IV-(V-z)*PV*d)
    ev(IP0,V).inv()
    hinge(zero,*args).inv()
    hinge(W.gen()-W.to(V),*map(W.to,args)).inv()
    print(f"F{prime}: repeat-V zero pivot excluded at rank48; other two repeats at rank96",flush=True)

    def qterms(v):
        v,z,PV,P0V,IP0V,W0V,S0,IV=pivot_read(v)
        return [PV,P0V/(v-z)], [S0,W0V], [IV,IP0V]
    kv,LV,IV=qterms(V); bmatched,LB,IB=qterms(B)
    FV=sub(mul(kv,LV),IV)
    def resultant_unit(A,B):
        assert len(A)==len(B)==3
        mat=[[A[0],zero,B[0],zero],[A[1],A[0],B[1],B[0]],
             [A[2],A[1],B[2],B[1]],[zero,A[2],zero,B[2]]]
        det(mat).inv()
    resultant_unit(FV,sub(mul(bmatched,LB),IB))
    print(f"F{prime}: actual nonzero fifth diagonal: matched V/B determinant unit at rank48",flush=True)

    P5=mul([-V,one],P0)
    J=prim(P5)
    H=[U.to(i) for i in (0,1,-14,56,-84,42)]
    theta=ev(J,z)/ev(H,z)
    E=sub(J,[theta*h for h in H])
    assert ev(E,z)==0
    Qold=(oldread(E[1:])*mi).v
    ratio=ev(R,B)/ev(R,V)
    slope=ev(Qold,B)-ratio*ev(Qold,V)
    kvQB=[slope*kv[0]+ratio*ev(E,V),slope*kv[1]]
    GB=sub(mul([ev(E,B)*a for a in kv],LB),mul(kvQB,IB))
    resultant_unit(FV,GB)
    print(f"F{prime}: actual zero fifth diagonal: undivided quintic/match determinant unit at rank48",flush=True)

if __name__=='__main__':
    p=argparse.ArgumentParser()
    p.add_argument('--research',type=Path,default=Path(__file__).resolve().parent.parent)
    p.add_argument('--prime',type=int,default=103)
    a=p.parse_args()
    ranks(a.research,a.prime)
