
"""Literal opener restrictions on five doubled clocks at the all-dirty SDIRK8 floor."""
import sympy as S
from itertools import permutations
m,j,u=S.symbols('m j u')
h=m-1
W=15*m**4-21*m**2*(h*h+j*j)+35*h*h*j*j
L4=lambda t:t**4-S.Rational(6,7)*m*m*t*t+S.Rational(3,35)*m**4
kap=lambda u:1+2*u-u*u
H=lambda u:-2+u+4*u*u-u**3
qnum=lambda u:S.expand((1+4*u-4*u*u)*H(u)+4*u*u*(3*u-2))
def norm(f,x):
    return S.Poly(f,x,domain=S.QQ).monic()
def fac(f,x,guards=()):
    f=S.Poly(S.cancel(f),x,domain=S.QQ)
    assert not f.is_zero
    out=[]
    for g,e in f.factor_list()[1]:
        if all(g.gcd(S.Poly(p,x,domain=S.QQ)).degree()==0 for p in guards):
            out.append(g.monic())
    return out
def branch_type(rel):
    e=S.Poly(rel,m,j,domain=S.QQ)
    if e.is_zero:return "identical",None
    bj=e.coeff_monomial(j)
    if bj:
        return 'sloped',S.expand(j-e.as_expr()/bj)
    bm=e.coeff_monomial(m)
    if bm:
        return 'fixed',S.expand(m-e.as_expr()/bm)
    return 'impossible',None

def m_census():
    result={}
    for mode in ('arith','star'):
     for p,q in permutations((h,S.Integer(0),j,-j),2):
        eq=(q-2*p-h if mode=='arith' else p+q-4+2*m)
        case,z=branch_type(eq)
        rec=(mode,str(p),str(q))
        if case=='identical':
            assert rec==('arith','0','m - 1')
            result[rec]=case
            continue
        if case=='impossible':
            result[rec]=()
            continue
        if case=='fixed':
            assert z.free_symbols==set()
            if z in (0,1):
                result[rec]=()
                continue
            # Need a nonzero j, neither ±h.
            assert z!=0
            jf=fac(W.subs(m,z),j,(j,j-(z-1),j+(z-1)))
            result[rec]=(str(m-z),tuple(str(k.as_expr()) for k in jf)) if jf else ()
            continue
        assert j not in z.free_symbols
        guarded=[m,m-1,z,z-h,z+h]
        pt=p.subs(j,z);qt=q.subs(j,z)
        U=S.expand(pt+h)
        guarded.extend([U,kap(U)])
        if mode=='arith':
            guarded.extend([H(U),3*U-2,qnum(U)])
        else:
            guarded.extend([U-1,U-2])
        # Keep only irreducible factors not forcing an exact invalid guard.
        ps=fac(W.subs(j,z),m,guarded)
        result[rec]=tuple(str(k.as_expr()) for k in ps)
    return result
ans=m_census()
for k,val in ans.items(): print(k,val)
F=S.expand(qnum(h)*L4(0)-kap(h)**2*H(h)*L4(h))
print('midpoint arithmetic both-end guard',S.factor(F))
print('midpoint arithmetic degrees',[(f.degree(),e) for f,e in S.Poly(F,m).factor_list()[1]])
rhalf={}
for mode,z in [('arith',2*u),('star',2-u)]:
    ff=S.expand(15-21*(u**2+z**2)+35*u**2*z**2)
    guards=[u,z,z-u,z+u,kap(u)]
    if mode=='arith':guards.extend([H(u),3*u-2,qnum(u)])
    else:guards.extend([u-1,u-2])
    rhalf[mode]=fac(ff,u,guards)
print('half', {k:[str(x.as_expr()) for x in v] for k,v in rhalf.items()})

quartics=set()
fixed={}
for key,data in ans.items():
    if data=="identical": continue
    if not data: continue
    if len(data)==2 and isinstance(data[-1],tuple):
        q=S.sympify(data[0],locals={'m':m})
        mm=-S.Poly(q,m).coeff_monomial(1)
        fixed[mm]=tuple(S.Poly(S.sympify(z,locals={'j':j}),j).monic().as_expr() for z in data[-1])
    else:
        quartics.update(S.Poly(S.sympify(z,locals={'m':m}),m).monic().as_expr() for z in data)
qt=[
    8*m**4-56*m**3+112*m*m-84*m+21,
    2*m**4-14*m**3-21*m*m+28*m-7,
    8*m**4-56*m**3+28*m-7,
    120*m**4-1008*m**3+2744*m*m-2800*m+875,
    50*m**4-462*m**3+1463*m*m-1680*m+560,
]
assert quartics=={S.Poly(f,m).monic().as_expr() for f in qt}
assert fixed=={S.Rational(5,3):(j*j-S.Rational(485,231),),S.Integer(2):(j*j-S.Rational(156,49),)}
mid=2*m**7-38*m**6+270*m**5-882*m**4+1365*m**3-985*m**2+315*m-35
assert S.expand(F-S.Rational(4,35)*(m-1)**2*(m*m-4*m+2)*mid)==0
assert S.Poly(mid,m).is_irreducible
assert {k:[q.as_expr() for q in r] for k,r in rhalf.items()}=={
 'arith':[u**4-S.Rational(3,4)*u*u+S.Rational(3,28)],
 'star':[u**4-4*u**3+S.Rational(14,5)*u*u+S.Rational(12,5)*u-S.Rational(69,35)]
}
print("verified complete centered clock census")
