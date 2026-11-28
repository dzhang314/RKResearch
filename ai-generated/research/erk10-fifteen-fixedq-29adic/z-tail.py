"""Exact reduction of the two late Z output guards to the base decic."""
from importlib.machinery import SourceFileLoader
from pathlib import Path
import sys
import sympy as sy
m=SourceFileLoader('eq',str(Path(__file__).with_name('exact-quad.py'))).load_module()
m.S.F=m.L.F=m.Q
c,d,g,R=map(m.Q,(m.C,26,6,15))
e,f,h,M,JM=m.S.late(c,d,g,R)
s,q=m.symmetric(c,d,g,R,(e,f,h,M,JM))
k=m.K
S=k.poly_ring(sy.Symbol('Y'))
Y=S.gens[0]
C=S.ring.ground_new
c,d,g,R,e,f,h,s,q=(v.x for v in (c,d,g,R,e,f,h,s,q))
dec=(Y*Y-C(s)*Y+C(q))*(Y-C(d))
dd=(Y-C(d))*(Y-C(e))*(Y-C(f))*(Y-C(g))*(Y-C(h))*(Y*Y-C(s)*Y+C(q))
p3=Y*(Y-1)*(Y-C(c))
isum=lambda p:sum((x/k.convert(kj[0]+1) for kj,x in p.items()),k.zero)
mus=[sum((dd.get((j,),k.zero)*isum(p3*Y**(j-1-i)) for j in range(i+1,8)),k.zero)
     for i in range(7)]
mu=sum((C(v)*Y**i for i,v in enumerate(mus)),S.zero)
ev=lambda p,y:sum((v*y**i[0] for i,v in p.items()),k.zero)
J=Y-14*Y**2+56*Y**3-84*Y**4+42*Y**5
Jc=ev(J,c)
P=C(Jc)*(6*Y**5-15*C(c)*Y**4+10*C(c*c)*Y**3)-C(c**5)*J
Nu=2*C(q*c)+2*C(-2*q+c*s-c*c)*Y
Lo=Y*Y*(Y-C(c))**2
invLo,ddQ,hcd=Lo.gcdex(dec)
assert hcd==S.one
V=(-Nu*P*invLo)%dec
qu,re=(Lo*V+Nu*P).div(dec)
assert not re and V.degree()==2 and qu.degree()<=3
sig=ev(mu,d)*d*(d-R)*(d-c)/((d-k.one)*ev(Nu,d))
for y in (e,f):
    assert ev(mu,y)*(y-R)*ev(P,y)+(y-k.one)*y*sig*(y-c)*ev(V,y)==k.zero
a=lambda x:m.mod(m.Q(x))
print('paid Jacobi and d-ratio',a(Jc),a(ev(Nu,d)),a(sig))
print('univariate V coefficients residues and quotient', [a(V.get((i,),k.zero)) for i in range(3)], [a(qu.get((i,),k.zero)) for i in range(4)])
print('Z output at e and f exact in decic algebra only')
