"""One doubled second and one singleton second at opposite chart ends."""
import sympy as S
from sympy.polys.fields import field
from itertools import combinations
from check_const_double_ends import K,a,hub,num,kappa

RF,u0=field('u',K)
Pc,u=RF.ring,RF.ring.gens[0]
q0,q1,q2=K.zero,K.one,K(2)
rng=(-1,0,1)
wg={-1:K(S.Rational(5,18)),0:K(S.Rational(4,9)),1:K(S.Rational(5,18))}

def interp(dd,Z,Z0):
    d=Z0
    return Z[0]+(Z[1]-Z[-1])*dd/(2*d)+(Z[1]+Z[-1]-2*Z[0])*dd*dd/(2*d*d)

def exact_gate(fs,gs):
    if not all(gs):
        return "guard"
    if (fr := next((f for f in fs if f),None)) is None:
        return "survive"
    return "excluded"

def linear_gate(eq,guards):
    if not all(guards): return "guard"
    if (pivot:=next(((p,q) for p,q in eq if p),None)) is None:
        return "excluded" if any(q for p,q in eq) else "survive"
    d,n=pivot; B=-n/d
    return "excluded" if not B or any(p*B+q for p,q in eq) else "survive"

def guards_and_gcd(E,guards):
    if not all(guards): return "guard"
    # Assert that any denominator removed by rational arithmetic is
    # already supported by the numerators of declared nonzero guards.
    guard_polys=[z.numer for z in guards]
    def strip(f):
        for h in guard_polys:
            while (v:=f.gcd(h)).degree()>0: f=f.exquo(v)
        return f
    assert all(strip(z.denom).degree()==0 for z in [*E,*guards])
    pols=[p.numer for p in E if p]
    if not pols: return "identically dependent"
    g=pols[0]
    for p in pols[1:]: g=g.gcd(p)
    return strip(g)

def check(m,end):
    D={e:m*(1+e*a) for e in rng}
    assert D[end]==q1 and D[-end]==2*m-1
    L4=lambda t:t**4-K(S.Rational(6,7))*m*m*t*t+K(S.Rational(3,35))*m**4
    LL={e:L4(D[e]-m) for e in rng}
    piv={e:(2-2*m*wg[e])/LL[e] for e in rng}
    right=[]
    left=[]
    for e in rng:
        if e==end: continue
        z=D[e]-q1
        k=kappa(z)
        for mode in ('arith','star'):
            if mode=='arith':
                if 3*z==q2: continue
                assert hub(z)
                q3=num(z)/hub(z)
                x3=1+2*z
            else:
                if z in (q1,q2): continue
                q3=k;x3=3-z
            if not k or not q3: continue
            e3=next((i for i in rng if D[i]==x3),None)
            if e3 in (end,e): continue
            left.append((mode,e,e3,x3,k/2,q3/2))
    # Reverse opener starts on a double and reads a singleton second.
    for d in rng:
        if d==end:continue
        for mode in ('arith','star'):
            x3=D[d]
            z=(x3-1)/2 if mode=='arith' else 3-x3
            if not z or 1+z in D.values(): continue
            k=kappa(z)
            if not k:continue
            if mode=='arith':
                if 3*z==q2:continue
                assert hub(z)
                q3=num(z)/hub(z)
            else:
                if z in (q1,q2): continue
                q3=k
            if not q3:continue
            right.append((mode,d,z,q3/2,False))
    # If the reverse third is singleton, arithmetic gives a cubic
    # factorization whose only guarded root is u=2; star is free.
    z=RF.gens[0]
    assert num(z)-kappa(z)*hub(z)==z*(z-2)*(3*z-2)*(z*z-2*z-1)
    right += [('arith',None,q2,q1/2,False),('star',None,z,kappa(z)/2,True)]
    recap={}
    for mr,dm,uu,gred,free in right:
      kR=kappa(uu)
      rr=kR/2
      xr=(1+uu,1+2*uu if mr=='arith' else 3-uu)
      f=lambda s:RF(s) if free else K.convert(s)
      # Original uncentered clock labels for reverse singleton rows.
      sR=[f(2*m)-xr[0]]+([f(2*m)-xr[1]] if dm is None else [])
      rem={-end:f(q1/2)}
      if dm is not None: rem[-dm]=f(gred)
      baseguard=[rr,uu,xr[1]-xr[0]]
      if mr=='star':baseguard+=[uu-1,uu-2]
      for x in sR: baseguard +=[x-f(d) for d in D.values()]
      for ml,e,e3,x3,g2,g3 in left:
        label=(ml,e,e3,mr,dm)
        lm={end:q1/2,e:g2}
        if e3 is not None:
            lm[e3]=g3
            Bscales={-LL[d]/(lm[d]*K.convert(rem[d])) for d in rem} if not free else {-LL[-end]/(lm[-end]*(q1/2))}
            if len(Bscales)!=1:
                report='paired-product'
            else:
                M=Bscales.pop()
                T0=sum((2-2*m*wg[d])/lm[d] for d in rng)
                T1=sum(piv[d]*lm[d] for d in rng)
                # Trace is T0*lambda = M*T1−(8−2m)/r_R.  In
                # particular the exact T0=0 branch must not be divided.
                rhs=f(M*T1)-f(8-2*m)/rr
                eq=[(-rr*interp(x-f(m),{d:f(LL[d]/lm[d]) for d in rng},f(m*a))-f(M)*rr*rr,
                      L4(x-f(m))+f(M)*rr*interp(x-f(m),{d:f(lm[d]) for d in rng},f(m*a))) for x in sR]
                if not T0:
                    if free:
                        report=guards_and_gcd([rhs]+[v*z-w*p for (v,w),(p,z) in combinations(eq,2)],baseguard)
                    elif rhs:
                        report='excluded'
                    else:
                        # Dropping additional duplicate-pair constraints only
                        # enlarges this necessary affine solution set.
                        report=linear_gate(eq,baseguard)
                else:
                    lam=rhs/f(T0)
                    if not lam:
                        report='guard'
                    else:
                        guards=baseguard+[lam]+[f(lm[d])-lam*rem[d] for d in rem]
                        ess=[v*lam+w for v,w in eq]
                        report=guards_and_gcd(ess,guards) if free else exact_gate(ess,guards)
        else:
            rrF=f(g3); lam=rrF/rr
            known={d:(f(LL[d])/f(g),-f(g)) for d,g in lm.items()} # const, B
            eq=[]; guards=baseguard+[f(x3)-x for x in sR]
            for d,g in rem.items():
                rgv=lam*g
                val=(f(LL[d])/rgv,-rgv)
                if d in known:
                    guards.append(f(lm[d])-rgv)
                    eq.append((val[1]-known[d][1],val[0]-known[d][0]))
                else:known[d]=val
            if len(known)==2:
                miss=(set(rng)-known.keys()).pop()
                known[miss]=tuple(((-f(8-2*m)/rrF if j==0 else f(0))-sum(f(piv[d])*v[j] for d,v in known.items()))/f(piv[miss]) for j in (0,1))
            else:
                eq.append(tuple(sum(f(piv[d])*v[j] for d,v in known.items())+(f(8-2*m)/rrF if j==0 else f(0)) for j in (1,0)))
            for x in [f(x3)]+sR:
                t=x-f(m)
                H=lambda j:interp(t,{d:v[j] for d,v in known.items()},f(m*a))
                eq.append((-rrF*(H(1)+rrF),L4(t)-rrF*H(0)))
            report=(guards_and_gcd([v*z-w*p for (v,w),(p,z) in combinations(eq,2)],guards)
                    if free else linear_gate(eq,guards))
        if hasattr(report,'degree'):report=str(report) if report.degree()>0 else 'unit gcd'
        recap[label]=report
    print('m',K.to_sympy(m))
    for (l,e,d,r,dR),v in recap.items():
        print((l,e,d,r,dR),v)
    assert all(z in ('guard','paired-product','unit gcd','excluded') for z in recap.values())

if __name__=='__main__':
    check(K.one,0)
    check(K.one/(1-a),-1)
    print('verified all constant-graph doubled-endpoint cases with exactly one doubled second row')
