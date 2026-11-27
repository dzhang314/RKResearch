"""First extra zero with sole previous donor: 3×3 pure-degree-four reads."""
import literal_front as L
import check_exceptional_fibers as F
from itertools import product
for front in (True,False):
 a,b,ha,hb,hs,d,W,A,B,C,D,M=L.front_data(front)
 g,g1=L.g,L.g1;s=L.s
 _,_,_,_,a32=L.end(1,front)
 U=[[L.K.one,L.K.one,L.K.one],[g,a,b],[g*g-L.la*g1,a*a,b*b]]
 taps=[t/L.det(U) for t in L.cramer(U,[s-g,s*s/2-g*s,s**3/3-g*s*s])]
 assert taps[0]*g1==hs
 AH=[g*ha,a32*ha+g*hb,taps[1]*ha+taps[2]*hb+g*hs]
 def th(z,V,C):return g*z**3+sum(v*c**3 for v,c in zip(V,C))-z**4/4
 TA=[th(a,[ha/g1],[g]),th(b,[hb/g1,a32],[g,a]),th(s,taps,[g,a,b])]
 r0,r1=[L.det([u[:2]+[v] for u,v in zip(M,x)]) for x in (AH,TA)]
 k=F.strip(F.Gcd(F.w(r0),F.w(r1)),F.w((s-a)*(s-b)))
 print(front,k.degree(),k.as_expr(),flush=True)
