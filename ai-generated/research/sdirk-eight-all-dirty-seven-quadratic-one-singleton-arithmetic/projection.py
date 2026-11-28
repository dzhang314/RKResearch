"""Projection for an actual S,S,S arithmetic opener opposite a double."""
import sympy as S
from sympy.polys.fields import field
from sympy.polys.rings import ring
from flint import fmpz_mpoly_ctx as MC
from math import lcm
F,h,u=field('h,u',S.QQ)
K=F.to_domain(); R,y=ring('y',K)
ctx=MC.get(('h','u'),'lex')
X,U=ctx.gens()
m=1+h;H=2*h;t=y-R(h)
L4=t**4-R(6*m*m/7)*t*t+R(3*m**4/35)
L3=t*t*t-R(3*m*m/5)*t
k=1+2*u-u*u
D=-2+u+4*u*u-u**3
N=(1+4*u-4*u*u)*D+4*u*u*(3*u-2)
A1=2*D-2*u*(3*u-2)
A2=-D+2*(3*u-2)
assert A2==(u-1)**2*(u-2)
b=A1/A2;c=D/A2
W=y*y+R(b)*y+R(c)
def rem_ratio(J,L):
    j0=J.get((0,),F.zero);j1=J.get((1,),F.zero)
    l0=L.get((0,),F.zero);l1=L.get((1,),F.zero)
    det=l0*l0-b*l0*l1+c*l1*l1
    a=(j0*(l0-b*l1)+c*l1*j1)/det
    s=(l0*j1-l1*j0)/det
    q=R(a)+R(s)*y
    assert (L*q)%W==J
    return q,det
line,det=rem_ratio(L3%W,L4%W)
P=(L3-line*L4).exquo(W)
assert P.degree()==3 and P.LC
term=P.evaluate(y,H)
delta=(P.div(y-R(H))[0]).exquo(R(P.LC))
assert delta.degree()==2
sumD=-delta.get((1,),F.zero)
Q3=y*(y-R(u))*(y-R(2*u))
rest,det3=rem_ratio(L4%W,Q3%W)
assert rest.degree()==1
lead=rest.LC
s=-rest.get((0,),F.zero)/lead
gs=[m,h,u,u-1,u-2,k,D,N,3*u-2,det,P.LC,L4.evaluate(y,H)]
g3=[det3,lead]
assert all(gs+g3)
def it(f):
    if not f:return ctx.constant(0)
    d=lcm(*(int(S.Rational(c).q) for c in f.values()))
    return ctx.from_dict({tuple(map(int,k)):int(v*d) for k,v in f.items()})
def num(f):return it(f.numer)
def strip(p,guards):
    for f in guards:
        while p and (g:=p.gcd(f)).total_degree()>0:
            p,r=divmod(p,g)
            assert not r
    return p
def branches():
    pairs={'triple star':sumD-4*h+2,'triple arithmetic':delta.evaluate(y,(sumD+H)/3)}
    pairs.update({ss:delta.evaluate(y,dd) for ss,dd in [
        ('extra D A2',(s+H)/2),('extra D A3',2*(s-h)),('extra D star',4*h-2-s)]})
    assert all(pairs.values())
    expected={
      'triple star':[(6,1),(12,1),(36,1)],
      'triple arithmetic':[(2,1),(6,2),(7,1),(12,2),(63,1)],
      'extra D A2':[(6,3),(12,3),(117,1)],
      'extra D A3':[(6,3),(12,3),(117,1)],
      'extra D star':[(6,3),(12,3),(117,1)],
    }
    for mode,f in pairs.items():
        gg=gs if mode.startswith('triple') else gs+g3
        all_guards=[it(q.numer) for q in gg]+[it(q.denom) for q in gg]
        for q in (term,f):
            assert strip(it(q.denom),all_guards).total_degree()==0
        p0,p1=[strip(num(q),all_guards) for q in (term,f)]
        out=strip(p0.resultant(p1,'u'),[q for q in all_guards if not q.degrees()[1]])
        assert out
        ff=out.factor()[1]
        assert sorted((z.total_degree(),e) for z,e in ff)==expected[mode]
        print(mode,'degree pairs',p0.degrees(),p1.degrees(),
              'projected',[(z.total_degree(),e) for z,e in ff],flush=True)
        yield mode,ff,(p0,p1),gg
if __name__=='__main__':assert len(list(branches()))==5
