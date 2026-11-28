"""Exact seven-label late-zero pressure and three sixth-row factors."""
import sympy as S
p,c,s,Y,L,A=S.symbols("p c s Y L A", nonzero=True)
q=2*p
F=lambda a,b,y:-y*y/4+(a+b)*y/3-a*b/2
assert S.expand(F(p,q,Y)+(Y-q)**2/4)==0
assert (q-Y).subs(Y,0)==q
assert ((q-Y)/2).subs(Y,0)==q/2
assert (-p*(Y-q)/A).subs(Y,0)==p*q/A
print("sixth-row cubic left coefficients at zero: q, q/2, pq/alpha")
assert S.cancel(1/(p*(p-c))+1/(c*(c-p))+1/(p*c))==0
assert S.cancel(sum(1/S.prod(x-y for y in [p,c,s] if y!=x)
                    for x in [p,c,s]))==0
mu=S.symbols("mu")
assert S.expand(-(s-q)*L-mu*s*s*(s-q)**2/4+(s-q)*(4*L+mu*s*s*(s-q))/4)==0
print("missing Y produces nonzero -D/(pc); restored cofactor gives raw Z_s=0")
