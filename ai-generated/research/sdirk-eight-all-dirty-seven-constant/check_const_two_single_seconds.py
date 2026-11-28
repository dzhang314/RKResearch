"""Both second rows singleton, at least one third row doubled."""
import sympy as S
from itertools import combinations, product
from check_const_one_second import RF, K, a, hub, num, kappa, interp, linear_gate, guards_and_gcd, wg, rng, q1, q2

def check(m,end):
    D={e:m*(1+e*a) for e in rng}
    assert D[end]==q1 and D[-end]==2*m-1
    L4=lambda t:t**4-K(S.Rational(6,7))*m*m*t*t+K(S.Rational(3,35))*m**4
    LL={e:L4(D[e]-m) for e in rng}
    piv={e:(2-2*m*wg[e])/LL[e] for e in rng}
    third_doubles=[]
    for d in rng:
      if d==end:continue
      for mode in ('arith','star'):
        x3=D[d]
        u=(x3-1)/2 if mode=='arith' else 3-x3
        x2=1+u
        if not u or x2 in D.values():continue
        k=kappa(u)
        if not k or k==q1:continue # both D and S with the same g forbidden
        if mode=='arith':
            if 3*u==q2:continue
            assert hub(u)
            q=num(u)/hub(u)
        else:
            if u in (q1,q2):continue
            q=k
        if not q or q==k:continue # third doubled, shares no g with singletons
        third_doubles.append((mode,d,x2,k/2,q/2))
    # A star third has q=k; on a doubled third this has already been pruned.
    assert all(md=='arith' for md,*_ in third_doubles)
    u=RF.gens[0]
    rec={}
    for lf,rg in product(third_doubles,third_doubles+[('star',None,1+u,kappa(u)/2,None)]):
        ml,dl,xl,rl,gl=lf
        mr,dr,x2r,rr,g3r=rg
        free=dr is None
        f=lambda s:RF(s) if free else K.convert(s)
        lam=f(rl)/rr
        if not lam: continue
        sR=[f(2*m)-x2r]
        if free:sR.append(f(2*m)- (4-x2r))
        guards=[f(xl)-x for x in sR]
        if free:
            guards +=[rr, kappa(u)-1,u,u-1,u-2]+[x-f(d) for d in D.values() for x in sR]
        lm={end:q1/2,dl:gl}
        rem={-end:f(q1/2)}
        if not free: rem[-dr]=f(g3r)
        known={d:(f(LL[d])/f(g),-f(g)) for d,g in lm.items()}
        eq=[]
        for d,g in rem.items():
            rgv=lam*g
            val=(f(LL[d])/rgv,-rgv)
            if d in known:
                guards.append(f(lm[d])-rgv)
                eq.append((val[1]-known[d][1],val[0]-known[d][0]))
            else: known[d]=val
        rrF=f(rl)
        if len(known)==2:
            miss=(set(rng)-known.keys()).pop()
            known[miss]=tuple(((-f(8-2*m)/rrF if j==0 else f(0))-sum(f(piv[d])*v[j] for d,v in known.items()))/f(piv[miss]) for j in (0,1))
        else:
            assert len(known)==3
            eq.append(tuple(sum(f(piv[d])*v[j] for d,v in known.items())+(f(8-2*m)/rrF if j==0 else f(0)) for j in (1,0)))
        for x in [f(xl)]+sR:
            t=x-f(m)
            H=lambda j:interp(t,{d:v[j] for d,v in known.items()},f(m*a))
            eq.append((-rrF*(H(1)+rrF),L4(t)-rrF*H(0)))
        report=(guards_and_gcd([v*z-w*p for (v,w),(p,z) in combinations(eq,2)],guards)
                if free else linear_gate(eq,guards))
        if hasattr(report,'degree'):report=str(report) if report.degree()>0 else 'unit gcd'
        rec[ml,dl,mr,dr]=report
    print('both seconds S, some third D',K.to_sympy(m),rec)
    assert all(z in ('guard','excluded','unit gcd') for z in rec.values())
    assert len(third_doubles)==(2 if m==K.one else 1)

check(K.one,0)
check(K.one/(1-a),-1)
print('verified both-second singleton cases with a doubled third')
