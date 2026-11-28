"""Literal phase, exact field, and common star fit helpers."""
import sympy as S
from sympy.polys.rings import ring
def K(u):return 1+2*u-u*u
def DD(u):return -2+u+4*u*u-u**3
def NN(u):return (1+4*u-4*u*u)*DD(u)+4*u*u*(3*u-2)
def op(u,ph):
    if ph=='S':return (K(u)/2,K(u)/2),[u,u-1,u-2,K(u)]
    return (K(u)/2,NN(u)/(2*DD(u))),[u,DD(u),NN(u),K(u),3*u-2]
def strip(p,gg):
    for z in gg:
        while p and (d:=p.gcd(z)).degree()>0:p=p.exquo(d)
    return p
def assoc(f):
    X=S.Symbol('H')
    p=S.Poly.from_dict(f.to_dict(),X,domain=S.QQ);assert p.is_irreducible
    if p.degree()==1:return S.QQ,S.QQ.convert(-p.nth(0)/p.nth(1))
    K=S.QQ.algebraic_field((p,X))
    return K,K.unit
def evalp(p,K,z):
    ans=K.zero
    for (i,),a in p.items():ans+=K.convert(a)*z**i
    return ans
def rvalue(p,K,z):
    b=evalp(p.denom,K,z)
    assert b
    return evalp(p.numer,K,z)/b
def val(p,x):
    E=p.ring.domain
    return sum((v*x**i if i else v for (i,),v in p.items()),E.zero)
def pgcd(p,q):
    while q:p,q=q,p%q
    return p.monic() if p else p
def audstrip(p,gg):
    for z in gg:
        while p and (q:=pgcd(p,z)).degree()>0:p=p.exquo(q)
    return p
def audit(E,H,a,b,e,W,fa,fb):
    # First S at 0; D labels a,b,H may have a=H (reuse), with e the third label in that case.
    m=(H+2)/2;c=H-1
    T,y=W.ring,W.ring.gens[0]
    W0=W.get((0,),E.zero)
    if W0==0:return 'graph first zero'
    s=c*c-W0
    assert W==(y-T(c))**2-T(s)
    t=y-T(H/2)
    L4=t**4-t*t*T(6*m*m/7)+T(3*m**4/35)
    l=L4%W;l0=l.get((0,),E.zero);l1=l.get((1,),E.zero)
    if not l0:return 'nodal constant zero'
    r=E.one/(2*W0)
    ys=2*c+W0*l1/l0
    ds=[H,b,e] if H==a else [H,a,b]
    if ys in [E.zero]+ds:return 'fourth S collides'
    if not val(W,ys):return 'fourth S graph zero'
    J=y*(y-T(ys))
    A0=(L4+T(2*r*l0)*J).exquo(T(r)*W)
    P,X=ring('X',E)
    def lf(x):return P(val(A0,x))*(X-P(s))-P(2*l0*val(J,x))
    R=lambda x:r*val(W,x)
    u1=fa*(fa-R(a));u2=fb*(fb-R(b))
    if not u1 or not u2:return 'D on graph'
    jA=(X-P(s))*P(val(L4,a))-P(fa)*lf(a)
    jB=(X-P(s))*P(val(L4,b))-P(fb)*lf(b)
    if a==H:
        beta=-2*val(L4,H)/fa
        j0=(P(2)-X)*P(beta/(2*r))
        fs=[jA-j0*P(u1),jB-j0*P(u2)]
    else:
        j0=jA.exquo(P(u1))
        fs=[jB-j0*P(u2)]
    fs += [(2-X)**2*P(val(L4,H))-P(r)*(2-X)*lf(H)-
           P(r)*j0*(P(r)*(X-P(s))-(2-X)*P(R(H)))]
    Pgs=[X,X-1,X-2,X-P(s)]
    Pgs+=[X-P((y0-c)**2) for y0 in [E.zero,ys]+ds]
    if a==H:Pgs+=[P(r)*(X-P(s))-(2-X)*P(fa)]
    # A zero nonzero-guard is impossible, although all listed are generically nonzero.
    if not all(Pgs):return 'literal star guard'
    g=P.zero
    for f0 in fs:g=pgcd(g,f0)
    print('star X fit degrees',[f0.degree() for f0 in fs],
          'raw/guarded',g.degree(),audstrip(g,Pgs).degree(),flush=True)
    return 'excluded' if audstrip(g,Pgs).degree()==0 else ('survives',g,audstrip(g,Pgs))
