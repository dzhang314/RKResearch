"""Literal two overlap products for D,D,D versus exactly one additional D."""
import sympy as S
from itertools import product
from sympy.polys.fields import field
from sympy.polys.rings import ring
Q,h=field('h',S.QQ)
x=S.Symbol('h')
qu=lambda r:Q(S.Rational(r))
def k(u):return 1+2*u-u*u
def H(u):return -2+u+4*u*u-u**3
def num(u):return (1+4*u-4*u*u)*H(u)+4*u*u*(3*u-2)
def g(u,mode):
    return num(u)/(2*H(u)) if mode=='A' else k(u)/2
def phaseguards(u,mode):
    return [u,k(u),H(u),num(u),3*u-2] if mode=='A' else [u,k(u),u-1,u-2]
def l4(t,m):return t**4-qu(S.Rational(6,7))*m*m*t*t+qu(S.Rational(3,35))*m**4
def sqroot(a,b,m):return 35*a*a*b*b-21*m*m*(a*a+b*b)+15*m**4
def f_specs():
    pp=Q.one
    yield 'AM','A',h+1,[-h,Q.zero,h],h,pp # no additional Q condition
    yield 'AN','A',h+1,[-h,h,3*h],2*h,sqroot(h,3*h,h+1)
    d=2-3*h
    for mode,D,u in [('S1',[-h,h,d],2*h),('S2',[-h,d,h],2-2*h)]:
        yield mode,'S',h+1,D,u,d*sqroot(h,d,h+1)
    yield 'C_A','A',pp,[Q.zero,h,2*h],h,sqroot(h,2*h,pp)
    yield 'C_S','S',pp,[Q.zero,h,2-h],h,sqroot(h,2-h,pp)

def mathcases():
  for la,pf,m,ds,u,F in f_specs():
    hf=m-1
    G=[Q.one/2,k(u)/2,g(u,pf)]
    end=ds.index(hf)
    base=phaseguards(u,pf)+[m]
    if la.startswith('C'):
        base+=[ds[1]**2-ds[2]**2,ds[1]**2-qu(S.Rational(3,5))]
    else:
        base += [hf,hf*hf-qu(S.Rational(3,5))*m*m]
    base += [d-e for i,d in enumerate(ds) for e in ds[i+1:]]
    base += [l4(d,m) for d in ds]
    for j in range(3):
      if j==end:continue
      for mode,pos in product(('A','S'),(2,3)):
        delta=hf-ds[j]
        v=delta if pos==2 else delta/2 if mode=='A' else 2-delta
        if mode=='A' and not H(v):
            raise AssertionError
        d2,d3=k(v)/2,g(v,mode)
        Sg=d3 if pos==2 else d2
        Dg=d2 if pos==2 else d3
        sigma=hf-(2*v if mode=='A' else 2-v) if pos==2 else hf-v
        guards=base+phaseguards(v,mode)+[sigma-d for d in ds]
        eq=l4(hf,m)*G[j]*Dg-l4(ds[j],m)*G[end]/2
        key=(la,j,mode,pos)
        if not all(guards):
            print(key,'identically forbidden guard')
            continue
        if not eq and F==Q.one:
            print(key,'free projection')
            yield key,m,ds,G,end,j,Dg,Sg,sigma,None
            continue
        # All candidate rational formulas divide only by the
        # nonzero arithmetic D values before this projection.
        def guarded_denominator(val):
            vv=val.denom
            for q in guards:
                while (ff:=vv.gcd(q.numer)).degree()>0:vv=vv.exquo(ff)
            return vv.degree()==0
        assert all(guarded_denominator(vv) for vv in [eq,F,*guards])
        test=eq.numer.gcd(F.numer) if F!=Q.one else eq.numer
        for d in guards:
            while (gcd:=test.gcd(d.numer)).degree()>0:test=test.exquo(gcd)
        if test.degree()>0:
            print(key,'degree',test.degree(),'factors',[(ff.degree(),i) for ff,i in test.factor_list()[1]],flush=True)
            for ff,e in test.factor_list()[1]:
                yield key,m,ds,G,end,j,Dg,Sg,sigma,ff

if __name__=='__main__':
    sol=list(mathcases())
    assert len(sol)==14 and all(q[-1] is not None for q in sol)
    assert not any(q[0][0].startswith('C') for q in sol)
    print('total projected finite factors',len(sol))
