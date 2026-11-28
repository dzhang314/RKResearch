"""Exact S,S,S-star opener opposite a doubled endpoint."""
import sympy as S
from sympy.polys.fields import field
from sympy.polys.rings import ring
F,h=field('h',S.QQ)
K=F.to_domain(); R,y=ring('y',K)
m=1+h;t=y-R(h)
L4=t**4-R(6*m*m/7)*t*t+R(3*m**4/35)
L3=t*t*t-R(3*m*m/5)*t
W=y*y-2*y-1
ell,H=2*m,2*h
inv,_,gg=L4.gcdex(W);assert gg==R.one
line=(L3*inv)%W
B1=line.get((1,),F.zero)
Q=(L3-line*L4).exquo(W)
assert Q.degree()==3 and B1
fterm=Q.evaluate(y,H)
def strip(f,guards):
    g=f
    for a in guards:
        while (d:=g.gcd(a)).degree()>0:g=g.quo(d)
    return g
def row(q,y,u):
    return q.evaluate(y,u)
def rec(P,q,alpha):
    r=0
    for ix,c in q.to_dict().items():
      r+=P.convert(S.Rational(c))*alpha**ix[0]
    return r
def ev(E,q,a):
    z=rec(E,q.numer,a);d=rec(E,q.denom,a)
    assert d
    return z/d
def run():
    b0=(L4%W).get((0,),F.zero)
    b1=(L4%W).get((1,),F.zero)
    gs=[m,h,B1]
    # Check inverse and terminal denominators against det(L4· | F[y]/W).
    det=b0*b0+2*b0*b1-b1*b1
    assert det
    gs+=[det]
    assert strip(fterm.denom,[z.numer for z in gs]+[z.denom for z in gs]).degree()==0
    pp=strip(fterm.numer,[z.numer for z in gs]+[z.denom for z in gs])
    fs=pp.factor_list()[1]
    print('projected h factors',[(f.degree(),n) for f,n in fs],flush=True)
    for f,n in fs:
      x=S.Symbol('h')
      fk=S.Poly.from_dict(f.to_dict(),x,domain=S.QQ)
      assert fk.is_irreducible
      if fk.degree()==1:
        E=S.QQ;a=E.convert(-fk.nth(0)/fk.nth(1))
      else:
        E=S.QQ.algebraic_field((fk,x));a=E.unit
      U,v=ring('v',E)
      def e(q):return ev(E,q,a)
      for g in gs:assert e(g)
      p=U.from_dict({ix:e(c) for ix,c in Q.items()})
      assert p.degree()==3
      dh=2*a
      d=p.exquo(v-U(dh)).monic()
      # Every actual D label required distinct; coprime defects m(H)>0
      assert d.degree()==2
      if d.gcd(d.diff(v)).degree() or not row(d,v,dh):
        print('coincident D',fk.degree(),flush=True);continue
      sumD=-d.get((1,),E.zero)
      # reverse D,D,D star and both arithmetic directions.
      print('triple D phase equations',sumD==4*a-2,row(d,v,(sumD+dh)/3)==E.zero,flush=True)
      assert sumD!=4*a-2 and row(d,v,(sumD+dh)/3)!=E.zero
      # reverse D,D,S / D,S,D: a paid proportionality without left gap.
      if not e(b0):
          assert e(b1)
          print('zero constant remainder forces contradiction',flush=True)
          continue
      s=2-e(b1)/e(b0)
      # Inverse formulas d=(s+2h)/2, d=2(s-h), d=4h-2-s.
      drows=[(s+dh)/2,2*(s-a),4*a-2-s]
      vals=[row(d,v,l) for l in drows]
      print('one-extra D phase guards',[bool(w) for w in vals],flush=True)
      assert all(vals)
    assert [(f.degree(),n) for f,n in fs]==[(9,1)]
    print('all SSS stars excluded opposite doubled endpoint')
if __name__=='__main__':run()
