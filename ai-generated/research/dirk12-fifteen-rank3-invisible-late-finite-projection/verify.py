#!/usr/bin/env python3
"""Exact identities for the geometry-free DIRK12 late-fourth projection."""
import sympy as s


def eq(f, g=0):
    assert s.cancel(f-g) == 0, s.factor(f-g)


def J(f, t):
    primitive=s.integrate(s.expand(f), t)
    return primitive-primitive.subs(t,0)


def integ(f, t):
    return J(f, t).subs(t, 1)


def main():
    t, x, z, a, y, l0, l1, H, w = s.symbols("t x z a y l0 l1 H w")
    P = 10*t**2-12*t+3
    N = t*(t-1)*(5*t-3)/2
    Q = s.Rational(64,3)-40*t
    E = (30*t**2-28*t+1)/3
    Z = x*(5*x-2)/(3*(2*x-1))
    m = (4*x-3)/x
    ell = l0+l1*t
    B0 = N-ell*P
    C0 = s.Rational(5,2)-10*l1
    eq(s.Poly(B0,t).LC(),C0)
    T0 = (z-1)*P.subs(t,z)-m*N.subs(t,z)
    eq(T0.subs(z,Z), (Z-1)*5*x*(x-1)**2/(6*(2*x-1)**2))
    Dz = z-1-m*ell.subs(t,z)
    Bz = B0.subs(t,z)
    sig = (z-1)*Q.subs(t,z)+m*E.subs(t,z)
    eq(Q*N+E*P,1)
    eq((E+Q*ell).subs(t,z)*T0+sig*Bz,Dz)
    eq(T0*(z*N.subs(t,z)-ell.subs(t,z)*H)-(z-1)*H*Bz,
       N.subs(t,z)*(z*T0-H*Dz))
    eq((1-Q*B0)/P,E+Q*ell)
    print("late amplitude identity, pole-free Bezout, and all partial-fraction residues")
    b=[s.Integer(4),s.Rational(8,3),s.Integer(2),s.Rational(8,5),s.Rational(33,25)]
    eq_series=s.series((-Q/P).subs(t,1/w),w,0,6).removeO()
    eq(eq_series,sum(v*w**j for j,v in enumerate(b,1)))
    ms=[s.factor((sig/T0).subs(z,Z))]
    for v in b[:4]:
        ms.append(s.factor(Z*ms[-1]+v))
    def M(f):
        p=s.Poly(f,t)
        assert p.nth(0)==0
        return sum(p.nth(i)*v for i,v in enumerate(ms,1))
    W=t**2*(t-1)**2*(t-x)
    eq(M(W))
    eq(M(s.diff(W,t)))
    for j in range(1,5):
        eq(M(t**(j+1))-Z*M(t**j),8*integ(t**j,t))
    eq(Z.subs(x,s.Rational(2,5)))
    assert [v.subs(x,s.Rational(2,5)) for v in ms]==[s.Rational(15,2),4,s.Rational(8,3),2,s.Rational(8,5)]
    print("geometry-independent moments and genuine W and W-prime cancellations")
    eq(integ(t*P,t)); eq(integ(t**2*P,t)); eq(integ(t*N,t)); eq(integ(t*B0,t))
    eq(integ(t**2*B0,t),-(1+2*l1)/120)
    eq(integ(t**3*P,t),s.Rational(1,60))
    eq(integ(t**3*P,t)-10*integ(t**2*B0,t)/C0,1/(8*C0))
    eq((b[-1]+1/(10*C0))/8-(1/(80*C0)-s.Rational(1,600)),s.Rational(1,6))
    B=5*x**4*(x-1)**4/(12*(2*x-1)**2)
    eq(B,(x**3*(x-1)**2/2)*(T0/(z-1)).subs(z,Z))
    eq(B.subs(x,s.Rational(2,5)),3*s.Rational(2,5)**3*(s.Rational(2,5)-1)**2/2)
    print("paid a-row remainder, degree-six cancellation, and literal late-tap normalization")
    L={j:s.diff(s.legendre(j,2*t-1),t) for j in (5,6,7)}
    assert s.Poly(L[6],t).LC()==5544
    coeff=s.symbols('q5:8')
    nr=s.Poly(t*L[6]-sum(coeff[j-5]*L[j] for j in (5,6,7)),t)
    ss=s.solve(nr.all_coeffs(),coeff,dict=True)
    assert len(ss)==1
    eq(nr.as_expr().subs(ss[0]))
    eq(s.det(s.Matrix([[L[j].subs(t,0) for j in (5,6)],
                       [a*s.diff(L[j],t).subs(t,0) for j in (5,6)]])),7560*a)
    C=lambda X:L[6].subs(t,X)
    Ax=(2*x-1)*C(a*x)-x**3*(2*x**2-6*x+5)*C(a)
    axcoeff=s.Poly(Ax,a)
    eq(axcoeff.nth(0)/C(0)-axcoeff.nth(1)/s.diff(L[6],t).subs(t,0),
       (2*x-1)*(1-x))
    eq(Ax.subs(x,s.Rational(2,5)), -s.Rational(126,15625)*
       (129888*a**5-330000*a**4+312000*a**3-136800*a**2+27800*a-2015))
    D=2*x*y-x-3*y**2+2*y
    Pxy=-10*x*x+(20*x*x+5*x)*y+(-18*x*x-6*x)*y*y+(6*x*x+8*x-3)*y**3+(2-4*x)*y**4
    Ay=(2*x-1)*D*C(a*y)+y*y*Pxy*C(a)
    eq(Ay.subs(y,1)); eq(Ay.subs(y,x),D.subs(y,x)*Ax)
    eq(s.Poly(Ay,y).LC(),-3*(2*x-1)*5544*a**5)
    eq(s.discriminant(5*x*x-(2+6*z)*x+3*z,x),4*(9*z*z-9*z+1))
    print("all scalar leading coefficients, inadmissible factors, neighboring modes, and two-jet rank")
    # Separately verify the genuine diagonal elimination as a polynomial identity.
    q=t-y-w
    d, U, Wt, Wc = s.symbols("d U Wt Wc")
    V=U*Wc+d*Wt
    eq(q*V-d*(V+q*Wt),(q-d)*U*Wc-d*d*Wt)
    print("literal fourth-row commutator identity")


if __name__ == '__main__':
    main()
