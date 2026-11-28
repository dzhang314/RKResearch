"""New terminal D, singleton front S,D,D, true reverse D,S,S arithmetic."""
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
F,H,u,v=field('H,u,v',S.QQ)
C=MC.get(('H','u','v'),'lex')
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
    a=u;b=2*u if fm=='A' else 2-u
    (fa,fb),guards=op(a,fm)
    guards += [m,H,a-2]+[D,k,q,v,3*v-2]
    guards += [x-y for x,y in combinations([F.zero,H,a,b,s,p],2)]
    guards += [2*x-H for x in [H,a,b]]
    guards += [x+y-H for x,y in combinations([H,a,b],2)]
    guards += [L(H),L(a),L(b)]
    assert all(guards)
    base=[num(z) for z in guards]
    assert all(poly(z.denom).total_degree()==0 for z in guards)
    V,y=ring('y',F.to_domain())
    a0=L(H,3)/L(H);a1=(L(a,3)/L(a)-a0)/(a-H)
    t=y-V(H/2)
    L4=t**4-V(6*m*m/7)*t*t+V(3*m**4/35)
    L3=t**3-V(3*m*m/5)*t
    M=(L3-(V(a0)+V(a1)*(y-V(H)))*L4).exquo((y-V(H))*(y-V(a)))
    W=M.div(y-V(b))[0]
    assert W.degree()==2 and a1
    E=M.evaluate(y,b)
    M0=M.get((0,),F.zero)
    r=lambda x:-b*W.evaluate(y,x)/(2*M0)
    Rs,Rp,Ra,Rb,RH=map(r,(s,p,a,b,H))
    mu=2*Rs
    ratio=D*(W.get((2,),F.zero)*(2*H-3*v)+W.get((1,),F.zero))-(v-2)*(3*v-2)*W.evaluate(y,s)
    assert ratio and num(ratio).degrees()[2]==3
    assert D*W.evaluate(y,p)-q*W.evaluate(y,s)== -v*ratio
    pts=[(F.zero,2*mu*L(F.zero)),(s,2*L(s)),(p,2*D*L(p)/q)]
    pa=fa*(fa-Ra);pb=fb*(fb-Rb)
    Ja=mu*L(a)-fa*ip(a,pts)
    Jb=mu*L(b)-fb*ip(b,pts)
    ZF=pa*Jb-pb*Ja
    ZT=pa*(4*k*k*L(H)-2*k*ip(H,pts))-Ja*(mu-2*k*RH)
    assert all(strip(poly(x.denom),base).total_degree()==0 for x in [a1,M0])
    base+=[num(M0)]
    guards += [a1,M0,Rs,Rp,pa,pb]
    assert all(guards)
    assert all(strip(poly(x.denom),base).total_degree()==0 for x in guards)
    gs=[num(a) for a in guards]+[poly(a.denom) for a in guards]
    assert all(strip(poly(x.denom),gs).total_degree()==0 for x in [E,ratio,ZF,ZT])
    rows=[strip(num(x),gs) for x in [E,ratio,ZF,ZT]]
    return gs,rows
def project():
 for fm in 'AS':
    gs,rows=data(fm)
    E,R,X,Y=rows
    hs=[g for g in gs if g.degrees()[1:]==(0,0)]
    hus=[g for g in gs if g.degrees()[2]==0]
    expected=[(9,6,0),(8,5,3),(24,21 if fm=='A' else 15,7),(24,16,8)]
    assert [z.degrees() for z in rows]==expected
    print(fm,'necessary rows',expected,flush=True)
    outs=[];uvs=[]
    for j,Z in enumerate([X,Y]):
        q=R.resultant(Z,'v')
        assert q
        q=strip(q,hus)
        uvs.append(q)
        print(fm,j,'outer v degrees',q.degrees(),flush=True)
        p=E.resultant(q,'u')
        assert p
        p=strip(p,hs)
        print(fm,j,'outer u degree',p.total_degree(),flush=True)
        outs.append(p)
    q=outs[0].gcd(outs[1])
    assert q
    fac=q.factor()[1]
    expected=([(2,36),(4,2),(4,9),(36,1),(42,1)] if fm=='A' else
              [(1,9),(2,38),(4,9),(18,2),(21,2)])
    assert sorted((z.total_degree(),n) for z,n in fac)==expected
    assert [z.total_degree() for z in outs]==([788,651] if fm=='A' else [622,656])
    assert [z.degrees() for z in uvs]==([(121,96,0),(133,85,0)] if fm=='A' else
                                       [(121,78,0),(133,85,0)])
    print(fm,'H factors',[(x.total_degree(),n) for x,n in fac],flush=True)
    yield fm,fac,rows,gs,uvs
if __name__=='__main__':list(project())
