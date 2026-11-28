#!/usr/bin/env python3
"""Exact general-x scalar derivations for the no-late first-root projection."""
import sympy as S


def eq(f,g=0):
    assert S.cancel(f-g)==0, S.factor(f-g)


def J(f,T):
    p=S.Poly(f,T)
    return sum(p.nth(j)*T**(j+1)/(j+1) for j in range(p.degree()+1))


def main():
    T,x,y,a=S.symbols('T x y a')
    I=lambda f:J(f,T).subs(T,1)
    Db=5*x*x-5*x+1
    D=2*x*y-x-3*y*y+2*y
    H=3*x*x-2*x*y-2*x+y
    eps=-(7*x*x-7*x+2)/1260
    K=lambda f:I(T*f)-eps*S.Poly(f,T).nth(5)
    W=T*T*(T-1)**2*(T-S.Rational(1,2))
    beta=x*(x-1)*(2*x-1)/(2*Db)
    eq(beta*S.diff(W,T).subs(T,x),W.subs(T,x))
    rb=x**3*(15*x**3-49*x*x+55*x-20)/Db
    kb=-30*x**3*(x-1)**3/Db
    Qx=T*(T-1)*(T-x)
    for f in (Qx,T*Qx,T*T*Qx):
        eq(J(f,T).subs(T,x),rb*I(f)+kb*K(f))
    eq(S.det(S.Matrix([[I(f),K(f)] for f in (Qx,T*Qx)])),Db/3600)
    print("genuine second-row scalar system, diagonal, and quintic excess")
    P0=Qx*(T-y)
    mat=S.Matrix([[I(f),K(f)] for f in (P0,T*P0)])
    rhs=S.Matrix([J(f,T).subs(T,y) for f in (P0,T*P0)])
    det=-Db*D/10800
    eq(mat.det(),det)
    numer=mat.adjugate()*rhs
    eq(numer[1],-y**3*(y-1)**3*H/360)
    eq(S.resultant(D,H,y),-3*x*(x-1)*Db)
    ry,ky=map(S.factor,numer/det)
    omega=y*(x-y)*(y-1)/(2*D)
    eq(J(Qx,T).subs(T,y)-ry*I(Qx)-ky*K(Qx),omega*Qx.subs(T,y))
    xx=S.Rational(1,2);Dy=6*y*y-6*y+1
    eq(ry.subs(x,xx),-y**3*(24*y**4-114*y**3+204*y**2-165*y+50)/Dy)
    eq(ky.subs(x,xx),-60*y**3*(y-1)**3/Dy)
    print("genuine third pivot, zero-pivot impossibility, and physical diagonal")
    L={j:S.diff(S.legendre(j,2*T-1),T) for j in (5,6,7)}
    g=lambda v:L[6].subs(T,v)
    Y=x*x*(x-1)**3*D*g(a*y)+y*y*(y-1)**3*H*g(a*x)
    eq(Y.subs(y,1),x*x*(x-1)**3*D.subs(y,1)*g(a))
    eq(Y.subs(y,x))
    eq(S.Poly(Y,y).LC(),-3*x*x*(x-1)**3*5544*a**5)
    eq(64*Y.subs(x,xx),Dy*g(a*y)-16*y*y*(y-1)**3*g(a/2))
    u,v,w=S.symbols('u v w')
    assert len(S.solve(S.Poly(T*L[6]-u*L[5]-v*L[6]-w*L[7],T).all_coeffs(),
                       [u,v,w],dict=True))==1
    eq(S.det(S.Matrix([[L[j].subs(T,0) for j in (5,6)],
                       [a*S.diff(L[j],T).subs(T,0) for j in (5,6)]])),7560*a)
    print("leading and invalid third factors, exact half-clock specialization, neighboring two-jet")
    p,q,d,z,w0,w1,w2,tau=S.symbols('p q d z w0 w1 w2 tau')
    primitive=p*w0+q*w1+d*w2
    literal=(z-x-beta-d)*p*w0+(z-y-omega-d)*q*w1-q*tau*w0-d*d*w2
    m=z-y-omega
    simplified=m*primitive-d*(primitive+m*w2)+w0*((y+omega-x-beta)*p-tau*q)
    eq(literal,simplified)
    eq(simplified.subs({z:x,p:beta-d,q:0,w2:w0}),-beta**2*w0)
    eq(simplified.subs({z:y,p:tau,q:omega-d,w2:w1}),
       (y-x-omega-beta)*tau*w0-omega**2*w1)
    print("literal two-source fourth commutator, indirect tap and exact earlier roots")


if __name__=='__main__':
    main()
