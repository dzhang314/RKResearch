#!/usr/bin/env python3
"""Independent exact polynomial identities and finite irreducibility test."""
import sympy as S
Y,a,b,c,z,alpha=S.symbols('Y a b c z alpha')
# Unconditional identity in the polynomial algebra; no denominator pivots.
M=Y**2*(Y-2*a)**2
G=Y*(Y-a)*(Y-2*a)*(Y-c)
J=lambda p:sum(t*Y**(k+1)/(k+1)for (k,),t in S.Poly(p,Y).terms())
I=lambda p:sum(t/(k+1)for (k,),t in S.Poly(p,Y).terms())
assert S.expand(4*J(G)-(Y-c)*M+J(M))==0
print('unconditional identity: 4JG=(Y−c)M−JM')
# Sixth-row scalar equation for the delayed exceptional head.
b=2*a
β=(4*a-6*alpha)/(3*alpha)
φ=2*a*a/alpha-2*alpha-a*z/alpha
t=-alpha/(2*(alpha-a)*(alpha-b))
F=S.factor(1-t*(φ-(a+b)*β))
A=S.factor(t*(z*z/4-(a+b)*z/3+a*b/2))
assert S.cancel(F-a*(2*a-z)/(2*(alpha-a)*(alpha-b)))==0
assert S.cancel(A+alpha*(z-2*a)**2/(8*(alpha-a)*(alpha-b)))==0
print('late-active sixth-row cofactor normalization checked')

B=896*a**4-840*a**3+300*a*a-48*a+3
NM=5600*a**4-5400*a**3+1984*a*a-327*a+21
NN=1600*a**4-1600*a**3+611*a*a-105*a+7
N=5376000*a**9-10590720*a**8+9105600*a**7-4477616*a**6+1385568*a**5-279450*a**4+36720*a**3-3036*a*a+144*a-3
tau=[I((Y-1)*Y**j*J(M))for j in range(4)]
assert S.expand(tau[1]**2-tau[0]*tau[2]+B/6350400)==0
assert S.expand(tau[2]*tau[1]-tau[3]*tau[0]+NM/31752000)==0
assert S.expand(tau[1]*tau[3]-tau[2]**2-NN/31752000)==0
assert S.resultant(B,NM,a)==2**14*3**2*7**3*13
assert S.resultant(B,NN,a)==2**12*7**2*13*31
print('Cramer numerators and Gram pivot-resultant guards verified')
assert N.subs(a,16)%17==0 and S.diff(N,a).subs(a,16)%17==4
print('nonic N has simple 17-root a=16; derivative 4')
F=S.Poly(N,a,modulus=29).monic()
X=S.Poly(a,a,modulus=29)
def mod_exp(b,n):
    q=S.Poly(1,a,modulus=29)
    while n:
        if n%2:q=(q*b)%F
        b=(b*b)%F
        n//=2
    return q
powers=[X]
for j in range(9):powers.append(mod_exp(powers[-1],29))
assert powers[9]==X and S.gcd(powers[3]-X,F).degree()==0
print('nonic N irreducible mod29 (Frobenius order-nine and degree-three gcd)')
def param(a0,p):
 b=B.subs(a,a0)%p
 z=pow(int(5*b),-1,p)
 return int(-z*NM.subs(a,a0)%p),int(z*NN.subs(a,a0)%p)
assert N.subs(a,14)%17==0 and S.diff(N,a).subs(a,14)%17==4
assert B.subs(a,14)%17==13 and param(14,17)==(12,5)
assert B.subs(a,16)%17!=0 and param(16,17)==(7,7)
assert (12*12-4*5)%17==5 and all(i*i%17!=5 for i in range(17))
print('other simple 17-place a=14 has nonsquare V discriminant 5; a=16 splits V at 4,6')
D=NM*NM-20*B*NN
N0=S.Poly(N,a);D0=S.Poly(D,a)
brackets=[(S.Rational(9,100),S.Rational(1,10)),(S.Rational(11,50),S.Rational(23,100)),
          (S.Rational(39,100),S.Rational(2,5))]
assert N0.count_roots(-S.oo,S.oo)==3
for l,r in brackets:
    assert N0.count_roots(l,r)==1 and D0.count_roots(l,r)==0 and D0.eval((l+r)/2)>0
print('exact real signature via root intervals:',brackets,
      '; all three real base places split V, so degree-18 field has signature (6,6)')
