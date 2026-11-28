"""Exact number-field reconstruction for a singleton-first S,S,D and a doubled terminal."""
import sympy as S
from sympy.polys.rings import ring
a,b,y,z,D=S.symbols('a b y z D')
L3=lambda v,d:5*v**3-3*d*d*v
L4=lambda v,d:35*v**4-30*d*d*v*v+3*d**4
K,srem=S.div(L3(y,D)*L4(z,D)-L4(y,D)*L3(z,D),y-z,y)
assert srem==0
end=S.Poly(K.subs({y:-a-b,z:b-a,D:2-a-b}),a,b,domain=S.QQ)
F={md:S.Poly(S.cancel(K.subs({y:((8+a+b-4/a) if md=='A' else (a+b+2/a)),z:b-a,D:2-a-b})).as_numer_denom()[0],a,b,domain=S.QQ) for md in ('A','S')}
def rec():
  expected={'A':[(1,2),(1,12),(9,1),(22,1)],'S':[(1,2),(1,12),(8,1),(20,1)]}
  for md,pol in F.items():
    resa=S.Poly(pol.as_expr(),b,a).resultant(S.Poly(end.as_expr(),b,a))
    factors=resa.factor_list()[1]
    assert sorted((f.degree(),p) for f,p in factors)==expected[md]
    for f,power in factors:
      if f.degree()==1:
        print(md,'linear',str(f.as_expr()),power)
        assert f.monic().as_expr() in (a,a-1)
        continue
      assert f.is_irreducible
      E=S.QQ.algebraic_field((f,a))
      aa=E.unit
      RR,Z=ring('B0',E)
      def atA(P):
        return sum(RR(E(c)*aa**i)*Z**j for (i,j),c in P.terms())
      gg=atA(pol).gcd(atA(end))
      print(md,'a degree',f.degree(),'b gcd degree',gg.degree(),flush=True)
      assert gg.degree()==1
      bb=-gg[(0,)]/gg[(1,)]
      dd=2-aa-bb
      zz=bb-aa
      xf=5-E(2)/aa if md=='A' else 1+E.one/aa
      yf=2*xf-dd
      ye=dd-2
      assert atA(pol).evaluate(Z,bb)==E.zero and atA(end).evaluate(Z,bb)==E.zero
      assert all((dd,dd-2,L3(zz,dd),L4(zz,dd),bb))
      assert (yf==ye)==(f.degree() in (8,9))
      print('guarded normalized mesh; coincident third/terminal double:',yf==ye,flush=True)
      yield md,E,aa,bb,dd,zz,xf,yf,ye

if __name__=='__main__':
  list(rec())
