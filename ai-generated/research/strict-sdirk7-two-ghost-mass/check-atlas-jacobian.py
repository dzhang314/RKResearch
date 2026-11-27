#!/usr/bin/env python3
from math import prod
def atlas(z,u,e,p):
 def dd(a,b):return a*pow(b%p,-1,p)%p
 m=dd(z,2)
 n=lambda t:dd(t,m)-1
 leg=lambda t:[1,t,dd(3*t*t-1,2),dd(5*t**3-3*t,2)]
 k=lambda s,t:sum((2*j+1)*a*b for j,(a,b) in enumerate(zip(leg(n(s)),leg(n(t)))))%p
 g=lambda t:k(e,t)
 M=u*u-4*u+2;T=u**3-7*u*u+10*u-2;J=4*u**3-24*u*u+39*u-17
 v=2*u-1
 r1,ru,rv=dd(-1,2),dd(M,2),dd(M*J,2*T)
 tre=[1,u,v]
 nu=[dd(1, r*prod(y-h for h in tre if y!=h)) for y,r in zip(tre,[r1,ru,rv])]
 H=lambda t:sum(r*k(y,t) for y,r in zip(tre,nu))%p
 q1=dd(-(u-3)*(u-1)*(2*u-3),T);q2=dd((u-3)*(u-2)**2,2*T)
 E=lambda t:(-q1+q2*dd(-4+(2*dd(1,M)-2)*(t-1),3)-dd(1-t,M))%p
 l1=dd(dd(g(u),ru)-dd(g(1),r1),u-1)
 L=lambda t:(dd(g(1),r1)+l1*(t-1))%p
 a3=dd(7*leg(n(e))[3]*5,2*m**3)
 H3=sum(dd(w*7*leg(n(y))[3]*5,2*m**3) for y,w in zip(tre,nu))
 kap=(a3-q2*l1)%p;sig=dd(-2*q2*(u-1)**3,3*M*T)
 F=lambda t:(sig*L(t)+kap*E(t))%p
 pivot=(F(1)-F(0))%p;c=dd(-F(0),pivot)
 Q=lambda t:(H(t)*g(c)-g(t)*H(c))%p
 return (H(e),Q(z-1)),(c,pivot,kap,(H3*g(c)-a3*H(c))%p, L(c))
a=(6,9,16)
assert atlas(*a,19)[0]==(0,0)
r=atlas(*a,361)[0]
cols=[]
for i in range(3):
 b=list(a);b[i]+=19
 s=atlas(*b,361)[0]
 assert all((x-y)%19==0 for x,y in zip(s,r))
 cols.append(tuple((x-y)//19%19 for x,y in zip(s,r)))
print(atlas(*a,19),cols,[(i,j,(cols[i][0]*cols[j][1]-cols[j][0]*cols[i][1])%19) for i in range(3) for j in range(i+1,3)])
assert atlas(*a,19)==((0,0),(0,9,2,18,7))
assert cols==[(18,13),(10,0),(6,5)]
