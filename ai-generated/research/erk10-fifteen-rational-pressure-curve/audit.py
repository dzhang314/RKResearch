#!/usr/bin/env python3
"""Exact polynomial elimination of three rational slices, plus optional full bidegrees."""
import sympy as S
import sys
Y,a,e,m,n,c,d=S.symbols('Y a e m n c d')
R=S.Rational
I=lambda f:sum(z/(k+1)for (k,),z in S.Poly(f,Y).terms())
J=lambda f:sum(z*Y**(k+1)/(k+1)for (k,),z in S.Poly(f,Y).terms())
b=2*a
M=Y**2*(Y-b)**2
G1=Y*(Y-a)*(Y-b);G0=Y*G1;G=G0-c*G1
U=(Y-1)*(Y**2+m*Y+n);N=(Y-e)*U
assert S.expand(M-G-Y*(Y-b)*((c-a)*Y-a*c))==0
assert S.expand(J(M)/4-(Y**5/20-b*Y**4/8+b*b*Y**3/12))==0
assert S.expand(c*(c-b)*(Y-d)-d*(d-b)*(Y-c)-(c-d)*((c+d-b)*Y-c*d))==0
assert S.expand(Y*(Y-b)*G1-(Y-a)*M)==0
BL=I(N*J(M));J0=I(N*J(G0));J1=I(N*J(G1))
VM=[I(N*f) for f in (G0,G1,M)]
UM=[I(N*Y*f) for f in (G0,G1,M)]
WM=[I(U*J(f))for f in (G0,G1,M)]
D=S.Poly(BL,n).nth(1)
NN=S.factor(S.solve(BL,n)[0])
nvec=[J0,J1]+VM+UM+WM
def pressure(vec):
    j0,j1=vec[:2];v0,v1,vm=vec[2:5];u0,u1,um=vec[5:8];w0,w1,wm=vec[8:]
    vg=j1*v0-j0*v1;ug=j1*u0-j0*u1;wg=j1*w0-j0*w1
    return [S.factor(S.fraction(S.cancel(x))[0])for x in (vg*um-vm*ug,vg*wm-vm*wg)]

def deny_projective(poly,p):
    coeff=[int(x)%p for x in poly.all_coeffs()]
    if not coeff[0]:return
    def val(z):
        y=0
        for k in coeff:y=(y*z+k)%p
        return y
    return all(val(z)for z in range(p))

def only_linear_roots(f,a0,expected):
    roots=[]
    for poly,n in S.factor_list(f,a0)[1]:
        P=S.Poly(poly,a0)
        if P.degree()==1:
            rr=S.solve(poly,a0)[0]
            roots.append(rr)
            print('linear factor root',rr,'multiplicity',n,flush=True)
        else:
            p=next((p for p in S.primerange(2,1500)if
                all(x.is_Integer for x in P.all_coeffs()) and deny_projective(P,p)),None)
            if p:
                print('degree',P.degree(),'multiplicity',n,'no projective roots modulo',p,flush=True)
            else:
                assert not S.polys.polytools.ground_roots(P)
                print('degree',P.degree(),'multiplicity',n,'exact ground-root check',flush=True)
    assert set(roots)==set(expected)
    return roots

print('=== centered distinguished last-three row e=1/2 ===')
S0={e:R(1,2)}
assert S.discriminant(S.fraction(S.cancel(D.subs(S0)))[0],a)<0
F0,F1=pressure([S.cancel(z.subs(S0).subs(n,NN.subs(S0)))for z in nvec])
res=S.resultant(F0,F1,m)
only_linear_roots(res,a,[0,R(1,6)])
gcd=S.gcd(F0.subs(a,R(1,6)),F1.subs(a,R(1,6)))
r0=S.polys.polytools.ground_roots(gcd,m)
assert list(r0)==[-R(67,40)]
ss={a:R(1,6),e:R(1,2),m:-R(67,40),n:R(7,10)}
assert NN.subs({k:v for k,v in ss.items()if k!=n})==R(7,10)
assert J1.subs(ss)==0 and J0.subs(ss)==-R(1,345600)
print('only nonzero a=1/6; split tail 4/5,7/8; blind equation gives 0*c=-1/345600')

print('=== alternate blind pivot D=0 ===')
Se=S.factor(S.solve(D,e)[0])
assert S.discriminant(14*a*a-7*a+1,a)<0
p0=S.cancel(BL.subs(e,Se))
coef=S.Poly(p0,m).nth(1)
q4=896*a**4-840*a**3+300*a*a-48*a+3
assert deny_projective(S.Poly(q4,a),19)
assert S.cancel(coef+q4/(30240*(14*a*a-7*a+1)))==0
sm=S.factor(S.solve(p0,m)[0])
A0,A1=pressure([S.cancel(z.subs({m:sm,e:Se},simultaneous=True))for z in nvec])
res=S.resultant(A0,A1,n)
only_linear_roots(res,a,[0,R(1,4)])
gcd=S.gcd(A0.subs(a,R(1,4)),A1.subs(a,R(1,4)))
r0=S.polys.polytools.ground_roots(gcd,n)
assert list(r0)==[R(2,5)]
assert Se.subs(a,R(1,4))==R(2,3) and sm.subs(a,R(1,4))==-R(6,5)
assert R(36,25)-4*R(2,5)==-R(4,25)
print('only nonzero a=1/4; e=2/3; tail V=Y²−6Y/5+2/5 has discriminant −4/25')

print('=== no first terminal Z response (Z_d=0) ===')
W=[I(U*J(M)),I(Y*U*J(M))]
subs={k:S.factor(v)for k,v in S.solve(W,(m,n)).items()}
assert S.cancel(S.linear_eq_to_matrix(W,(m,n))[0].det()+q4/6350400)==0
T=[S.factor(I(U*Y**j*M).subs(subs,simultaneous=True)) for j in range(3)]
q9=5376000*a**9-10590720*a**8+9105600*a**7-4477616*a**6+1385568*a**5-279450*a**4+36720*a**3-3036*a*a+144*a-3
assert S.cancel(T[0]*T[2]-T[1]**2+a*a*q9/(39690000*q4**2))==0
assert deny_projective(S.Poly(q9,a),11)
print('q4 projectively rootless mod19; q9 projectively rootless mod11')

if '--all' in sys.argv:
    v0=-S.Poly(BL,n).nth(0)
    def red(z):
        z=S.Poly(z,n)
        return (D*z.nth(0)+v0*z.nth(1)).expand()
    pp=pressure([red(z)for z in nvec])
    F,G=[next(x for x,j in S.factor_list(f,m,a,e)[1] if S.degree(x,m)>0)for f in pp]
    rr=S.resultant(F,G,m)
    print('regular resultant bidegrees and multiplicities',
          [(S.Poly(z,a,e).degree_list(),j)for z,j in S.factor_list(rr,a,e)[1]])
