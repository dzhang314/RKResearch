"""Exact two-pole even profile filter for the half-diagonal endpoint pair."""
import sympy as S
from itertools import product
X,t=S.symbols('X t')
R=t*t-S.Rational(1,2)
g=S.Rational(1,2);g1=g*g/2
red=lambda f:S.rem(S.expand(f),R,t)
L=lambda x:70*x**4-140*x**3+90*x*x-20*x+1
I=lambda f:red(sum(c/S.Integer(k+1) for (k,),c in S.Poly(f,X).terms()))
def inv(f):
 a=S.invert(red(f),R,t);assert red(a*f)==1;return a
def matinv(A):
 d=inv(A.det())
 return A.adjugate().applyfunc(lambda a:red(d*a))
def gcd(a,b):
 a,b=red(a),red(b)
 while b:
  B=S.Poly(b,X);e=inv(B.LC())
  while a and (m:=S.Poly(a,X).degree())>=B.degree():
   a=red(a-red(e*S.Poly(a,X).LC())*X**(m-B.degree())*b)
  a,b=b,a
 return red(a*inv(S.Poly(a,X).LC()))
def endpoint(e,st):
 u=1+2*e*t;w=2-u if st else 2*u
 r=0 if st else 3*u/2-1
 return tuple(map(red,(g*(1+u),g*(1+w),g*g1*u,g*g1*(w-r))))
def qr(f,d):
 a,b=S.div(red(f),d,X)
 a,b=red(a),red(b)
 assert red(f-a*d-b)==0
 return a,b
def lv(x):
    return [red(S.legendre(j,2*x-1)) for j in (3,4,5)]
for fs,rs,e in product((True,False),(True,False),(1,-1)):
    a,b,h,k=endpoint(1,fs)
    c,d,j,v=endpoint(e,rs); c,d=red(1-c),red(1-d)
    for q0 in (X*X+X+1, (X-g)**2):
        q=red(q0)
        M=S.Matrix([lv(a),lv(b),[red(v*q.subs(X,d)*w-j*q.subs(X,c)*z) for w,z in zip(lv(c),lv(d))]])
        inv(M.det())
        co=(matinv(M)*S.Matrix([h*q.subs(X,a),k*q.subs(X,b),0])).applyfunc(red)
        p=red(sum(k*S.legendre(j,2*X-1) for j,k in zip((3,4,5),co)))
        if gcd(p,q)!=1:
            assert q0==(X-g)**2
            print(fs,rs,e,"double central phase non-coprime")
            continue
        D=red(q*q)
        fs0=[qr(f,D) for f in (p*q,X*p*q,p*p,X*p*p)]
        N=S.Matrix([[S.Poly(vv,X).nth(k) for k in range(4)] for uu,vv in fs0])
        omega=(matinv(N)*S.Matrix([-I(uu) for uu,vv in fs0])).applyfunc(red)
        def mm(f):
            u,v=qr(f,D)
            assert S.degree(u,X)<=7
            return red(I(u)+sum(omega[j]*S.Poly(v,X).nth(j) for j in range(4)))
        U=S.Matrix([[1,1,1],[g,a,b],[g*g-S.Rational(2,3)*g1,a*a,b*b]])
        tap=(matinv(U)*S.Matrix([X-g,X*X/2-g*X,X**3/3-g*X*X])).applyfunc(red)
        F=red(q*g1*tap[0]-p)
        P=(X-a)*(X-b)*(X-c)*(X-d)
        for n in (7,8):
            r=n-4
            H=S.Matrix(r,r,lambda i,j:mm(P*X**(i+j)))
            inv(H.det())
            coeffs=(matinv(H)*S.Matrix([-mm(P*X**(r+i)) for i in range(r)])).applyfunc(red)
            U=red(X**r+sum(k*X**j for j,k in enumerate(coeffs)))
            assert S.degree(F,X)==5 and gcd(F,U)==1
            inv(F.subs(X,c)); inv(F.subs(X,d))
            if n==7: inv(mm(P*U*X**3))
            print(fs,rs,e,q,n,"nonzero eliminants",flush=True)
