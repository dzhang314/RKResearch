"""Distinct both-D, one-extra-D vs literal D,S,S star."""
import sympy as S
from sympy.polys.rings import ring
from itertools import combinations,product
from scalar_geometry import shape,exact_trace

H0=S.Symbol('h')
D0=2-2*H0
M0=H0+1
F=S.Poly(35*H0**2*D0**2-21*M0**2*(H0**2+D0**2)+15*M0**4,H0,domain=S.QQ)
print('split axis projection',S.factor(F.as_expr()),flush=True)
def meshes():
    yield 'even',S.QQ,S.QQ.one,S.QQ.zero,S.QQ(156,49)
    fac=F.factor_list()[1]
    assert len(fac)==1 and fac[0][0].degree()==4
    P=fac[0][0]
    E=S.QQ.algebraic_field((P,H0));h=E.unit
    d=2-2*h
    yield 'split',E,h,d,(h-1)**2

def check(kind,E,h,d,S0):
    count=0
    m=1+h;c=h-1
    R,t=ring('t',E)
    L=t**4-t*t*(E.convert(S.Rational(6,7))*m*m)+E.convert(S.Rational(3,35))*m**4
    L3=t**3-t*(E.convert(S.Rational(3,5))*m*m)
    ds=[-h,h,d]
    P=R.one
    for j in ds:P*=t-j
    W=(t-c)**2-S0
    mu=(h*h-E.convert(S.Rational(3,5))*m*m)/L.evaluate(t,h)
    Q0=L3-t*L*mu
    assert Q0==-mu*P*W
    ct,trace=exact_trace(E,R,t,P,W,L,Q0,m)
    assert S0
    # Both polynomials T and X live over the exact coefficient field.
    Z,T,X=ring('T,X',E)
    tp=lambda p:Z.from_dict({(i,0):z for (i,),z in p.items()})
    LP=tp(L)
    tau=(2-X)/2
    VV,V=ring('X',E)
    def vals(p):
       q=p.compose(T,T+c)
       r=[VV.zero,VV.zero]
       for (i,j),a in q.items():r[i%2]+=V**(j+i//2)*a
       return r
    def ip(pts):
       out=Z.zero
       for i,(z,w) in enumerate(pts):
         for j,(p,r) in enumerate(pts):
            if i!=j:w=w*(T-p)/(Z(z-p))
         out+=w
       return out
    def eat(p,x):
       return sum((X**j*(a*x**i) for (i,j),a in p.items()),Z.zero)
    def lin(p):
       q=VV.zero
       for j in range(3):
        c0=sum(V**k*z for (i,k),z in p.items() if i==j)
        q+=c0*trace(t**j)
       return q
    for choice,f in product(('reuse','third'),('A2','A3','S')):
      nd=h if choice=='reuse' else d
      delta=h+nd
      # Check guards before evaluating a literal arithmetic ratio.
      u=delta/2 if f=='A3' else delta
      zz=E.zero
      kk=lambda u:1+2*u-u*u
      hs=lambda u:-2+u+4*u*u-u**3
      if not (u and kk(u) and (hs(u) and 3*u!=E(2) if f!='S' else u not in (E.one,E(2)))):
          continue
      gd,sf,gf,gs=shape(delta,f);sf-=h
      if sf in ds or not gf or not gd or not W.evaluate(t,sf):
          continue
      ws=W.evaluate(t,sf)
      r=gf/ws
      uu=(X-S0)*r # λ τ
      ellh=L.evaluate(t,h)
      allguard=[V,V-1,V-2,V-S0]+[V-(y-c)**2 for y in ds+[sf]]
      if choice=='reuse':
        beta=-2*ellh/gd
        a=2*uu*ellh-beta*tau/2+beta*r*tau*W.evaluate(t,-h)
        b=-beta*(tau*gd+uu/2)+beta*r*tau*W.evaluate(t,h)
        pp=ip([(-h,a),(h,b),(sf,uu*L.evaluate(t,sf)/gf)])
        z0,z1=vals(LP-pp)
        g=z0.gcd(z1)
        allguard.append(V*0 + (V-S0)*(-r/2)+(2-V)*(gd/2))
      else:
        a0=ip([(-h,2*tau*uu*ellh),(h,2*tau*tau*ellh),
               (d,tau*uu*L.evaluate(t,d)/gd)])
        a1=ip([(-h,tau*(r*W.evaluate(t,-h)-E.one/2)),
               (h,tau*(r*W.evaluate(t,h))-uu/2),
               (d,tau*(r*W.evaluate(t,d)-gd))])
        # a0+a1 β represents τ μ C, β=B μ, μ=r(X−S).
        # Three true singleton equations and one normalized trace.
        p0=vals(tau*LP-a0)
        p1=vals(-a1)
        g0=vals((tau*uu*L.evaluate(t,sf)/gf)-eat(a0,sf))[0]
        g1=vals(-eat(a1,sf))[0]
        tr0=lin(a0)+(2-V)*(V-S0)*ct/2
        tr1=lin(a1)+(2-V)*(-r*trace(W))/2
        rows=[(p1[0],p0[0]),(p1[1],p0[1]),(g1,g0),(tr1,tr0)]
        g=VV.zero
        for (a,b),(c1,d1) in combinations(rows,2):g=g.gcd(a*d1-b*c1)
      pre=g.degree()
      assert g
      for z in allguard:
          if not z:raise AssertionError
          while (j:=g.gcd(z)).degree()>0:g=g.exquo(j)
      print(kind,choice,f,'X gcd before/after',pre,g.degree(),flush=True)
      assert g.degree()==0
      count+=1
    return count

if __name__=='__main__':
  assert sum(check(*rr) for rr in meshes())==6
  print('all six actual reverse-star branches excluded')
