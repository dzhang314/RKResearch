#!/usr/bin/env python3
"""Independent replay of two fixed physical polynomial fixtures, including derivatives.
No primality search, rational interpolation, or calls to the discovery script."""
from math import isqrt
F=[-1,20,-120,300,-330,132]; j=[7,-168,1260,-4200,6930,-5544,1716]
def out(a):
 a=list(a)
 while a and a[-1]==0:a.pop()
 return a
def ev(a,t,p):return sum(c*t**i for i,c in enumerate(a))%p
def plus(a,b):return out([(a[i] if i<len(a) else 0)+(b[i] if i<len(b) else 0) for i in range(max(len(a),len(b)))])
def times(a,b):return out([sum(a[i]*b[n-i] for i in range(max(0,n+1-len(b)),min(len(a),n+1))) for n in range(max(0,len(a)+len(b)-1))])
def scale(k,a):return out([k*c for c in a])
def mod(a,p):return out([c%p for c in a])
def rec(n,P,p):
 # Construct the primitive modulo p, verify its derivative by integer lifting.
 Q=[0]+[0]*n+[(c*pow(n+i+1,-1,p))%p for i,c in enumerate(P)]
 assert mod([i*a for i,a in enumerate(Q)][1:],p)==mod([0]*n+P,p)
 return Q
p=23;t=14;u=15;b=1;k=5;P=[15,8,19,22];N=[0,22,11,10,18,14];T=[9,22];D=[17,13,1]
W=plus(j,scale(b,F));G=[0]+W;js=lambda x:x*ev(j,x,p)%p
mu=lambda n,t:ev(rec(n,P,p),t,p)
assert ev(W,t,p)==ev(W,u,p)==0 and (js(t),js(u))==(10,10)
assert [mu(n,t) for n in (1,2,3)]==[0,0,4] and [mu(n,u) for n in (1,2,3)]==[19,13,2]
assert (mu(2,u)-t*mu(1,u))%p==0 and mu(3,t)==k*js(t)%p and (mu(3,u)-t*mu(2,u))%p==k*js(u)%p
assert (ev(P,t,p),ev(P,u,p))==(3,0)
assert mod(times(G,T),p)==mod(times(N,P),p) and mod(times(D,T),p)==P and mod(times(D,N[1:]),p)==mod(W,p)
assert len(N)-1==5 and len(P)-1==3 and set([u,18])=={x for x in range(p) if ev(D,x,p)==0}
p=53;t=17;u=37;b=3;k=52;R=[7,22,51,13,20];Q0=[46,52,1];N=[0]+Q0
W=plus(j,scale(b,F));G=[0]+W;js=lambda x:x*ev(j,x,p)%p
mu=lambda n,t:ev(rec(n,R,p),t,p)
assert ev(W,t,p)==ev(W,u,p)==0 and (js(t),js(u))==(21,26)
assert [mu(n,t) for n in (1,2)]==[0,32] and [mu(n,u) for n in (1,2)]==[18,15]
assert (mu(2,u)-t*mu(1,u))%p==k*js(u)%p and mu(2,t)==k*js(t)%p
assert (R[0],ev(R,t,p),ev(R,u,p))==(7,38,38)
assert mod(times(N,R),p)==mod(G,p) and mod(times([-t,1],[-u,1]),p)==Q0
assert all(p%v for p in (23,53) for v in range(2,isqrt(p)+1))
print('F23 literal five cubic primitives, rank-two common divisor and full mesh; F53 nonzero-origin quartic factorization, primitive leakage and all three knot amplitudes: verified.')
