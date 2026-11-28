"""Both rear D labels used by the singleton-end forward S,D,D."""
from sympy.polys.fields import field
from sympy.polys.rings import ring
import sympy as S
from itertools import product
F,H=field('H',S.QQ)
m=(H+2)/2
def K(u):return 1+2*u-u*u
def DD(u):return -2+u+4*u*u-u**3
def NN(u):return (1+4*u-4*u*u)*DD(u)+4*u*u*(3*u-2)
def op(u,ph):
    if ph=='S':return (K(u)/2,K(u)/2),[u,u-1,u-2,K(u)]
    return (K(u)/2,NN(u)/(2*DD(u))),[u,DD(u),NN(u),K(u),3*u-2]
def rear(d,ph):
    z=H-d
    if ph=='S':
        (a,b),gs=op(z,'S')
        return 2*H-2-d,a,b,gs
    if ph=='A2':
        (a,b),gs=op(z,'A')
        return 2*d-H,a,b,gs
    (a,b),gs=op(z/2,'A')
    return (H+d)/2,b,a,gs
def L3(y):
    t=y-H/2
    return t**3-3*m*m*t/5
def L4(y):
    t=y-H/2
    return t**4-6*m*m*t*t/7+3*m**4/35
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
def reconstruct(p,seq):
    H,d,s,fa,fb,gd,gs,slope,lcw,polys=seq
    for f,n in p.factor_list()[1]:
        K,hh=assoc(f)
        ev=lambda x:rvalue(x,K,hh)
        x,y,z,fa,fb,gd,gs,lo,b=[ev(q) for q in (H,d,s,fa,fb,gd,gs,slope,lcw)]
        if not lo or not b:
            print('nonquadratic or zero first S graph factor',f.degree(),flush=True)
            continue
        T,e=ring('e',K)
        q=T.from_dict({ix:ev(g) for ix,g in polys.items()})
        assert q.degree()==3
        l0,lh,ld,ls=[ev(L4(yy)) for yy in (F.zero,H,d,s)]
        beta=-2*lh/fa
        def val(a,b,c):
            return a*(z-x)*(z-y)/(x*y) + b*z*(z-y)/(x*(x-y)) + c*z*(z-x)/(y*(y-x))
        v0=val(-beta/2,-beta*fa,-beta*fb)
        v1=val(2*l0,-beta/2,-beta*gd)
        P0=ls-gs*v0;P1=gs*v1+beta*gs*gs
        M0=q.get((0,),K.zero);Ms=q.evaluate(e,z)
        assert M0==b and M0
        if not Ms:
            print('rear S on projection',f.degree(),flush=True);continue
        fit=2*M0*gs*(T(z)-e)*P0+e*Ms*P1
        g=q.gcd(fit)
        print('scalar H degree',f.degree(),'raw third-D gcd',g.degree(),flush=True)
        # Any third label is distinct, noncentral, and not antipodal to H or d.
        g=strip(g,[e,e-x,e-y,e-z,2*e-x,e+y-x])
        print('guarded third-D degree',g.degree(),flush=True)
        yield f.degree(),g
EXPECTED={('A','A2'):(11,7),('A','A3'):(14,10),('A','S'):(11,7),
          ('S','A2'):(8,4),('S','A3'):(11,8),('S','S'):(8,4)}
def run():
 visited=set()
 for fm,rm in product('AS',('A2','A3','S')):
    d=2*H if fm=='A' else 2-H
    # Arithmetic orientation (d,H) would make d=H/2, forbidden by parity.
    # A star orders (H,d) or (d,H); both have identical graph and paid residuals.
    (fa,fb),fg=op(H,fm)
    s,gd,gs,rg=rear(d,rm)
    guards=[m,H,d,d-H,2*d-H,s,s-H,s-d,L4(H),L4(d),H-2]+fg+rg
    if fm=='S':guards += [d-2]
    if not all(guards):
        print(fm,rm,'identical clock or literal obstruction',flush=True)
        continue
    exact=L4(H)*fb*gd-L4(d)*fa/2
    gfs=[q.numer for q in guards]+[q.denom for q in guards]
    assert strip(exact.denom,gfs).degree()==0
    f=strip(exact.numer,gfs)
    assert f
    assert (exact.numer.degree(),f.degree())==EXPECTED[fm,rm]
    assert [(a.degree(),b) for a,b in f.factor_list()[1]]==[(f.degree(),1)]
    print(fm,rm,'raw/guarded product degrees',exact.numer.degree(),f.degree(),
          'factor degrees',[(a.degree(),b) for a,b in f.factor_list()[1]],flush=True)
    slope=(L3(d)/L4(d)-L3(H)/L4(H))/(d-H)
    T,y=ring('y',F.to_domain())
    t=y-T(H/2)
    l3=t**3-T(3*m*m/5)*t;l4=t**4-T(6*m*m/7)*t*t+T(3*m**4/35)
    proj=l3-(T(L3(H)/L4(H))+T(slope)*(y-T(H)))*l4
    q=proj.exquo((y-T(H))*(y-T(d)))
    assert q.degree()==3
    for c in list(q.values())+[slope]:
       assert strip(c.denom,gfs).degree()==0
    [(deg,g)]=reconstruct(f,(H,d,s,fa,fb,gd,gs,slope,q.get((0,),F.zero),q))
    assert deg==f.degree() and g.degree()==0
    print(fm,rm,'post-fit',deg,g.degree(),flush=True)
    visited.add((fm,rm))
 assert visited==set(EXPECTED)
if __name__=='__main__':run()
