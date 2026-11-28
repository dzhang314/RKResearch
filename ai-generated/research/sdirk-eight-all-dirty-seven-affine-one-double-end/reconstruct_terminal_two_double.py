"""Exact mesh list for S,D,D at the lone singleton endpoint."""
import sympy as S
from sympy.polys.rings import ring
from sympy.polys.agca.extensions import MonogenicFiniteExtension
from exact_scalars import kk,l3,l4,hub,kap,num

class ExactTower(MonogenicFiniteExtension):
    # Field quotient must use the inverse modulo the checked irreducible
    # extension polynomial, not exact divisibility of representatives.
    def exquo(self,x,y):
        return x/y
    quo=exquo
    def convert(self,x,base=None):
        if getattr(x,'ext',None)==self:
            return x
        return super().convert(x,base)

e,s,y=S.symbols('e s y')
K=S.Poly(kk(y,s,1),y)
L,M=K.nth(3),-K.nth(2)
E=S.Poly(K.as_expr().subs(y,e),e,s,domain=S.QQ)
W=S.cancel((M-2*e*L)/(3*L))
pols={
    'A_dist':S.cancel(K.as_expr().subs(y,W)).as_numer_denom()[0],
    'S_dist':M-(2-3*e)*L,
    'A_pair2':K.as_expr().subs(y,3*e),
    'A_pair3':K.as_expr().subs(y,0),
    'S_pair':K.as_expr().subs(y,2-5*e),
}

def candidates():
 for mode,P0 in pols.items():
    P=S.Poly(P0,e,s,domain=S.QQ)
    fac=E.resultant(P).factor_list()[1]
    census={'A_dist':[(1,3),(2,3),(8,1),(18,1)], 'S_dist':[(1,1),(2,1),(9,1)],
            'A_pair2':[(1,1),(2,2),(12,1)], 'A_pair3':[(2,3)],
            'S_pair':[(1,1),(2,1),(3,1),(12,1)]}
    assert sorted((F.degree(),j) for F,j in fac)==sorted(census[mode])
    for F,j in fac:
      if F.monic().as_expr() in (s,s*s-S.Rational(3,5)):
        continue
      PF=S.QQ.algebraic_field((F,s)); ss=PF.unit
      PP,X=ring('e',PF)
      def et(P): return sum(PP(PF(c)*ss**j)*X**i for (i,j),c in P.terms())
      e_master=et(P).gcd(et(E)).monic()
      print(mode,'s deg',F.degree(),'e gcd degree',e_master.degree(),flush=True)
      e_fac=e_master.factor_list()[1]
      for etr,pow in e_fac:
        assert etr.degree()==1
        ee=-etr[(0,)]/etr[(1,)]
        print('  guard e,e-1,s+e,L3,L4,K(-e)',[bool(q) for q in (ee,ee-1,ss+ee,l3(ss,PF.one),l4(ss,PF.one),kk(-ee,ss,PF.one))],flush=True)
        if not all((ee,ee-1,ss+ee,l3(ss,PF.one),l4(ss,PF.one),kk(-ee,ss,PF.one))):
          continue
        G=kk(X,ss,PF.one).monic()
        assert G.degree()==3 and not G.evaluate(X,ee)
        G2=G.exquo(X-ee)
        if mode=='S_dist':
          M2=S.Poly.from_dict(G2.to_dict(),S.Symbol('w'),domain=PF)
          print('  remaining degree-two factorization',[(q.degree(),m) for q,m in M2.factor_list()[1]],flush=True)
          if M2.is_irreducible:
            FF=ExactTower(M2)
            emb=lambda a:FF.convert(a,PF)
            d2=FF.generator;d3=-emb(G2[(1,)])-d2
            assert d2!=d3
          else:
            FF=PF
            emb=lambda a:a
            fac2=G2.factor_list()[1]
            assert len(fac2)==2
            d2,d3=(-gg[(0,)]/gg[(1,)] for gg,jj in fac2)
          d0=emb(ee)
          sm=emb(ss)
          zero=FF.one
          choices=[(d2,d3),(d3,d2)]
        else:
          FF=PF
          d0,sm,zero=ee,ss,PF.one
          if mode=='A_dist':
            M0=-G[(2,)]
            d2=(M0-2*ee)/3
            d3=2*d2+ee
            choices=[(d2,d3)]
            others=[d2,d3]
          elif mode=='A_pair2':
            d2,d3=ee,3*ee
            choices=[(d2,d3)]
            others=[d3,-G[(2,)]-d2-d3]
          elif mode=='S_pair':
            d2,d3=ee,2-5*ee
            choices=[(d2,d3),(d3,d2)]
            others=[d3,-G[(2,)]-d2-d3]
          else:assert False
        if mode=='S_dist':others=[d2,d3]
        if len({d0,d2,d3})<3 and mode in ('A_dist','S_dist'):
          assert mode=='A_dist' and F.degree()==8 and d2==d0
          print('  discarded from distinct branch: second label equals terminal',flush=True)
          continue
        if any(q==d0 for q in others) or others[0]==others[1]:
          assert mode=='S_pair' and F.degree()==3 and d3==d0
          print('  failed distinct opener: both early D labels equal terminal',flush=True)
          continue
        assert all(not kk(x,sm,zero) for x in [d0]+others)
        ell=2*zero/(zero-d0)
        a=-(d0+sm)/(zero-d0)
        b=(sm-d0)/(zero-d0)
        assert a and ell and ell!=2*zero
        R=lambda x:(x-1+a)/(2*a)
        toc=lambda theta:ell*(1+theta)/2
        D=[toc(x) for x in [d0]+others]
        assert D[0]==ell-1 and not(FF.one in D)
        for yd2,yd3 in choices:
          x2,x3=toc(yd2),toc(yd3)
          u=x2-1
          if not u or not kap(u):continue
          if mode.startswith('A'):
            assert x3==1+2*u
            if 3*u==2*zero:continue
            assert hub(u)
            q=num(u)/hub(u)
          else:
            assert x3==3-u
            if u in (zero,2*zero):continue
            q=kap(u)
          if not q or kap(u)/2==R(x2) or q/2==R(x3):
            continue
          print('  kept literal opener',mode,'projected degree',F.degree(),flush=True)
          yield mode,F.degree(),FF,ell,a,b,sm,D,x2,x3,kap(u)/2,q/2

if __name__=='__main__':
    data=list(candidates())
    assert len(data)==6
    print('literal opener count',len(data))
