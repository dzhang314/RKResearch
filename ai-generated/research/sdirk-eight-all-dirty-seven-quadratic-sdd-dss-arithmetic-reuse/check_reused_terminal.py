"""Reused terminal D, singleton front S,D,D, reverse true arithmetic D,S,S."""
from sympy.polys.fields import field
from sympy.polys.rings import ring
from flint import fmpz_mpoly_ctx as MC
from itertools import combinations
from math import lcm
import sympy as S
def K(u):return 1+2*u-u*u
def DD(u):return -2+u+4*u*u-u**3
def NN(u):return (1+4*u-4*u*u)*DD(u)+4*u*u*(3*u-2)
def op(u,ph):
    if ph=='S':return (K(u)/2,K(u)/2),[u,u-1,u-2,K(u)]
    return (K(u)/2,NN(u)/(2*DD(u))),[u,DD(u),NN(u),K(u),3*u-2]
F,H,v=field('H,v',S.QQ)
C=MC.get(('H','v'),'lex')
m=(H+2)/2;s=H-v;p=H-2*v
D=DD(v);k=K(v);q=D-v*(v-2)*(3*v-2)
assert NN(v)==k*q
def L(z,j=4):
    t=z-H/2
    return t**3-3*m*m*t/5 if j==3 else t**4-6*m*m*t*t/7+3*m**4/35
def poly(a):
    if not a:return C.constant(0)
    l=lcm(*(int(S.Rational(c).q) for c in a.values()))
    return C.from_dict({tuple(map(int,i)):int(c*l) for i,c in a.items()})
def num(x):return poly(x.numer)
def strip(p,gs):
    for q in gs:
        while p and (g:=p.gcd(q)).total_degree()>0:
            p,r=divmod(p,g);assert not r
    return p
def ip(y,pts):
    a=F.zero
    for x,t in pts:
        for z,_ in pts:
            if z!=x:t*= (y-z)/(x-z)
        a+=t
    return a
def data(fm):
    d=2*H if fm=='A' else 2-H
    (fH,fd),guards=op(H,fm)
    guards += [m,H,d,d-H,2*d-H,H-2]+[D,k,q,v,3*v-2]
    guards += [x-y for x,y in combinations([F.zero,H,d,s,p],2)]
    guards += [L(H),L(d)]
    assert all(guards)
    base=[num(g) for g in guards]
    assert all(poly(g.denom).total_degree()==0 for g in guards)
    V,y=ring('y',F.to_domain())
    a=L(H,3)/L(H);b=(L(d,3)/L(d)-a)/(d-H)
    t=y-V(H/2)
    L4=t**4-V(6*m*m/7)*t*t+V(3*m**4/35)
    L3=t**3-V(3*m*m/5)*t
    M=(L3-(V(a)+V(b)*(y-V(H)))*L4).exquo((y-V(H))*(y-V(d)))
    assert b and M.degree()==3
    M0=M.get((0,),F.zero);Ms=M.evaluate(y,s);Mp=M.evaluate(y,p)
    A=(D*Mp*s-q*Ms*p)/v;B=(q*Ms-D*Mp)/v
    # Identities have cancelled v as a polynomial, not an inverse in a fibre.
    assert A and B and poly(A.denom).degrees()[1]==poly(B.denom).degrees()[1]==0
    e=-A/B;mu=A/(M0*q)
    assert M0 and Ms and Mp and e and mu
    beta=-2*L(H)/fH
    T0=[(F.zero,-beta/2),(H,-beta*fH),(d,-beta*fd)]
    T1=[(F.zero,2*L(F.zero)),(H,-beta/2),(d,L(d)/fd)]
    Fs=4*L(s)-2*k*ip(s,T0)
    Gs=2*ip(s,T1)+beta*k
    Fp=4*D*D*L(p)-2*k*q*D*ip(p,T0)
    Gp=2*q*D*ip(p,T1)+beta*k*q*q
    E=sum((a*(-A)**i*B**(3-i) for (i,),a in M.items()))
    P=M0*q*Fs-A*Gs;Q=M0*q*Fp-A*Gp
    guards += [b,M0,Ms,Mp,B,A]
    assert all(strip(poly(g.denom),base).total_degree()==0 for g in guards)
    base += [num(B),num(M0),num(q)]
    # Ratio slope is a true unit; recovering e introduces no new pole.
    # e sits at a distinct noncentral D, off both actual S labels.
    guards += [e,e-H,e-d,e-s,e-p,2*e-H,e+d-H,L(e)]
    guards += [mu-k*fH*2] # lambda/2 != fH at reused terminal
    assert all(guards)
    assert all(strip(poly(g.denom),base).total_degree()==0 for g in guards)
    gs=[num(a) for a in guards]+[poly(a.denom) for a in guards]
    assert all(strip(poly(z.denom),gs).total_degree()==0 for z in [E,P,Q])
    e1,p1,q1=[strip(num(z),gs) for z in [E,P,Q]]
    return gs,(e1,p1,q1),(e,mu,guards,M,A,B)
def project():
 for fm in 'AS':
    gs,rows,dta=data(fm)
    E,X,Y=rows;hs=[g for g in gs if g.degrees()[1]==0]
    shape=[(18,9),(20,5),(20,8)] if fm=='A' else [(18,9),(14,5),(14,8)]
    assert [z.degrees() for z in rows]==shape
    print(fm,'necessary rows',[p.degrees() for p in rows],flush=True)
    ops=[X.resultant(Z,'v') for Z in (Y,E)]
    r=[strip(z,hs) for z in ops]
    assert all(r)
    q=r[0].gcd(r[1])
    assert q and q.total_degree()==0
    assert [z.total_degree() for z in r]==([173,229] if fm=='A' else [127,179])
    fac=q.factor()[1]
    print(fm,'projected degrees',[x.total_degree() for x in r],
          'H factors',[(x.total_degree(),n) for x,n in fac],flush=True)
    yield fm,fac,rows,gs,dta
if __name__=='__main__':list(project())
