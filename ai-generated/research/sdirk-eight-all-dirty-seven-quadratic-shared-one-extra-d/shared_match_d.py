"""Shared doubled endpoints, matching extra D in two one-singleton prefixes."""
import sympy as S
from itertools import combinations_with_replacement
from sympy.polys.fields import field
from sympy.polys.rings import ring
from sympy.polys.agca.extensions import MonogenicFiniteExtension

class ExactTower(MonogenicFiniteExtension):
    def exquo(self,x,y):return x/y
    quo=exquo
    def convert(self,x,base=None):
        if getattr(x,'ext',None)==self:return x
        return super().convert(x,base)

FF,d=field('d',S.QQ)
X=S.Symbol('d')
def kap(u):return 1+2*u-u*u
def H(u):return -2+u+4*u*u-u**3
def qnum(u):return (1+4*u-4*u*u)*H(u)+4*u*u*(3*u-2)
def shape(u,lab):
    """Input u is literal D clock coordinate, not always the second gap."""
    if lab=='A2':
        gap=u
        return kap(gap)/2,2*u,qnum(gap)/(2*H(gap)),[gap,gap-2,3*gap-2,kap(gap),H(gap),qnum(gap)]
    if lab=='A3':
        gap=u/2
        return qnum(gap)/(2*H(gap)),gap,kap(gap)/2,[gap,gap-2,3*gap-2,kap(gap),H(gap),qnum(gap)]
    return kap(u)/2,2-u,kap(u)/2,[u,u-1,u-2,kap(u)]

def base_cases():
  for f,r in combinations_with_replacement(('A2','A3','S'),2):
    gf,sf,gs,gu=shape(d,f)
    hr,sr,gr,gv=shape(-d,r)
    sr=-sr
    h4=d**4-FF(6)*d*d/7+FF(3)/35
    guards=gu+gv+[d,5*d*d-3,h4,sf,sr,sf-d,sr-d,sf-sr]
    if not all(guards):
        print(f,r,'identical singleton clock',flush=True)
        continue
    eq=h4-4*FF(3)/35*gf*hr
    den=eq.denom
    for z in guards:
        while (g:=den.gcd(z.numer)).degree()>0:den=den.exquo(g)
    assert den.degree()==0
    N=eq.numer
    for a in guards:
        while (g:=N.gcd(a.numer)).degree()>0:N=N.exquo(g)
    print(f,r,'projection factor degrees',[(z.degree(),ex) for z,ex in N.factor_list()[1]],flush=True)
    for g,pow in N.factor_list()[1]:
        P=S.Poly.from_dict(g.to_dict(),X,domain=S.QQ)
        assert P.is_irreducible
        q0=8*X**5+64*X**4-44*X**3-146*X**2+45*X+60
        sample={('A2','A3'):q0,('A3','S'):-q0.subs(X,-X)}.get((f,r),8*X*X-3)
        assert P.monic()==S.Poly(sample,X,domain=S.QQ).monic()
        if P.degree()==1:
            K=S.QQ;delta=K.convert(-P.nth(0)/P.nth(1))
        else:
            K=S.QQ.algebraic_field((P,X));delta=K.unit
        def ev(r):
            def at(p):return sum((K.convert(c)*delta**i for (i,),c in p.items()),K.zero)
            n,den=at(r.numer),at(r.denom);assert den
            return n/den
        assert all(ev(a) for a in guards)
        yield (f,r,P.degree()),K,delta,*map(ev,(gf,sf,gs,hr,sr,gr))

def coordinates(K,d):
    H=(21*d*d-15)/(35*d*d-21)
    yield 'even' if H else 'Hermite',K,lambda x:x,-d,H
    if not H or H==d*d:
        return
    RR,t=ring('t',K)
    S0=t*t-H
    fs=S0.factor_list()[1]
    for f,n in fs:
        assert n==1
        if f.degree()==1:
            yield 'split',K,lambda x:x,-f[(0,)]/f[(1,)],H
        else:
            QQ=S.Poly.from_dict(f.to_dict(),S.Symbol('t'),domain=K)
            assert QQ.is_irreducible
            E=ExactTower(QQ)
            t=E.generator
            emb=lambda z:E.convert(z,K)
            for e in (t,-t):yield 'split',E,emb,e,emb(H)

def fit(K,d,e,h,s,gd,xf,gf,rd,xr,gr):
    one,z=K.one,K.zero
    l=lambda t:t**4-K.convert(S.Rational(6,7))*t*t+K.convert(S.Rational(3,35))
    if h=='split':w=lambda t:(t+d)*(t+e)
    else:w=lambda t:t*t-s
    if xf==e or xr==e:
        return 'singleton equals third D'
    if not(w(xf)*w(xr)):
        return 'singleton is graph zero'
    r=gf/w(xf);lam=r*w(xr)/gr
    assert r and lam
    if lam==one or gd==lam*rd:
        return 'duplicate physical pair'
    b0=-4*l(z)
    B=b0/lam
    assert B and b0==-l(d)/(gd*rd)
    C0=-B*(1+lam)/2+B*r*w(z)
    Cd=-B*(gd+lam*rd)+B*r*w(d)
    vals=[(z,C0),(d,Cd),(xf,l(xf)/gf)]
    def ip(x):
        value=z
        for j,(p,q) in enumerate(vals):
            for i,(w,v) in enumerate(vals):
                if i!=j:q=q*(x-w)/(p-w)
            value+=q
        return value
    if ip(xr)!=l(xr)/(lam*gr):
        return 'quartic fit'
    return 'survive'

def check():
  out=[]
  for lab,K,d,*dat in base_cases():
    for kind,E,emb,e,S0 in coordinates(K,d):
        dd=emb(d);gm=list(map(emb,dat))
        R,t=ring('t',E)
        L=t**4-t*t*E.convert(S.Rational(6,7))+E.convert(S.Rational(3,35))
        P=t*(t-dd)*(t-e)
        W=(t+dd)*(t+e) if kind=='split' else t*t-S0
        assert len({E.zero,dd,e})==3
        mu=(dd*dd-E.convert(S.Rational(3,5)))/L.evaluate(t,dd)
        L3=t**3-t*E.convert(S.Rational(3,5))
        assert L3-t*L*mu==-P*W*mu
        s=fit(E,dd,e,kind,S0,*gm)
        print(lab,kind,'fit',s,flush=True)
        out.append((lab,kind,s))
        assert s=='quartic fit'
  assert len(out)==12
  assert [kind for lab,kind,val in out].count('even')==4
  assert [kind for lab,kind,val in out].count('split')==8
  print('verified shared-matching D chart',len(out),flush=True)
if __name__=='__main__':check()
