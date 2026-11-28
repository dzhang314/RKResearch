"""Exact number-field check of every degree <= 12 projection factor."""
import sympy as S
from sympy.polys.rings import ring
from projection import branches,it

def rational_factor(f):
    x=S.Symbol('h')
    g=S.Poly.from_dict({(int(ix[0]),):int(c) for ix,c in f.to_dict().items()},x,domain=S.QQ)
    assert g.is_irreducible and g.degree()>=2
    return S.QQ.algebraic_field((g,x))

def specialize(f,R,h):
    K=R.domain
    out={}
    for (i,j),c in f.to_dict().items():
        out[(int(j),)]=out.get((int(j),),K.zero)+K.convert(int(c))*h**int(i)
    return R.from_dict({i:c for i,c in out.items() if c})
def gcd(p,q):
    while q:p,q=q,p%q
    assert p
    return p.monic()
def strip(g,guards):
    for z in guards:
        while (v:=gcd(g,z)).degree()>0:g=g.exquo(v)
    return g
def special_seven(K,h,u):
    T,y=ring('y',K)
    m=1+h;H=2*h;t=y-T(h)
    L3=t**3-t*T(3*m*m/5)
    L4=t**4-t*t*T(6*m*m/7)+T(3*m**4/35)
    D=-2+u+4*u*u-u**3
    Ru=(1+2*y-y*y)/2+T((3*u-2)/D)*y*(y-T(u))
    W=Ru.monic()
    li,_,z=L4.gcdex(W)
    assert z==T.one
    F=(L3*li)%W
    P=(L3-F*L4).exquo(W).monic()
    de=P.exquo(y-T(H))
    sig=-de.get((1,),K.zero)
    d=(sig+H)/3;e=2*d-H
    assert not de.evaluate(y,d) and not de.evaluate(y,e)
    front={'front1':K.zero,'front2':u,'front3':2*u}
    rear={'terminal':H,'reverse2':d,'reverse3':e}
    cc=[(a,b) for a in front for b in rear if front[a]==rear[b]]
    assert cc==[('front1','reverse3')]
    print('degree-seven provisionally D/S share:',cc,flush=True)
    return cc

def run():
    outcomes=[]
    for mode,ff,(a,b),gg in branches():
      for f,n in ff:
        deg=f.total_degree()
        if deg>12:continue
        K=rational_factor(f);h=K.unit
        R,u=ring('u',K)
        raw=gcd(specialize(a,R,h),specialize(b,R,h))
        guards=[specialize(it(g.numer),R,h) for g in gg]+[specialize(it(g.denom),R,h) for g in gg]
        z=strip(raw,guards)
        print(mode,'degree',deg,'raw and guarded u degrees',raw.degree(),z.degree(),flush=True)
        assert raw.degree()==1 and z.degree()==int(deg==7)
        if z.degree():
            assert mode=='triple arithmetic'
            v=-z.get((0,),K.zero)
            assert all(q.evaluate(u,v) for q in guards)
            special_seven(K,h,v)
        outcomes.append((mode,deg))
    assert sorted(outcomes)==sorted([(m,d) for m in ['triple star','triple arithmetic',
      'extra D A2','extra D A3','extra D star'] for d in [6,12]]+
      [('triple arithmetic',2),('triple arithmetic',7)])
if __name__=='__main__':run()
