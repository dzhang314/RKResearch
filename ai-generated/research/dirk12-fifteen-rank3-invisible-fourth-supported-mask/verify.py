#!/usr/bin/env python3
"""Exact symbolic checks for the paid Hankel, commutator and primitive gates."""
import sympy as S

def eq(lhs,rhs=0):
    assert S.cancel(lhs-rhs)==0, S.factor(lhs-rhs)

def main():
    x,a,b,c,e,f,g,u,d,v,w=S.symbols("X a b c e f g u d v w")
    y=S.Symbol("Y")
    W=S.symbols("Wd Wv Wu")
    H=S.Matrix(3,3,lambda i,j:sum(s**(i+j)*t for s,t in zip([d,v,u],W)))
    eq(H.det(),S.prod(W)*(d-v)**2*(d-u)**2*(v-u)**2)
    P=x*(x-a)*(x-b)*(x-c);K=(x-e)*P;Q=(x-f)*K
    E,Z,l,m=S.symbols("E Z lambda mu")
    r=S.Symbol("zeta");tau=e-r
    eq((x-r)*P,K+tau*P)
    eq(y*Q.subs(x,1-y),
       y*(y-(1-f))*(y-(1-e))*P.subs(x,1-y))
    q,h=S.symbols("q h")
    la=(3-2*q)/(6*(q-1));cp=-la**2/(1+la)
    nr=S.Rational(2,3)*h
    eq(la*(2*q*h/(9-6*q)-nr),nr/2)
    eq(la+cp,la/(1+la))
    A0,A1,A2=S.symbols("A_K A_Q A_P")
    U=A0+tau*A2
    old=x*U-(A1+f*A0+tau*(U+r*A2))-(l*(A1+f*A0)+m*A0)
    beta=(1+l)*f+m-r
    eq(old,(x-e)*U-(1+l)*A1-beta*A0)
    col=l*(x-f)
    eq(((x-e)*col-((1+l)*f-l*f-r)*A0).subs(r,f),
       l*(x-e)*(x-f))
    s,t=S.symbols("s t")
    L=s*(x-g)
    exp=(x-f)*L-(1+L)*la*(x-g)-s*cp*(x-g)**2
    eq(S.Poly(S.cancel(exp/(x-g)),x).LC(),s/(1+la))
    Xj=S.symbols("j")
    Mk1,Nk,Nk1,Nk2=S.symbols("M1 N0 N1 N2")
    tM=lambda j,N0,N1:(1+(j+2)*l)*N1-(j+2)*(l+m)*N0
    MR=tM(Xj+1,Nk1,Nk2)-E*tM(Xj,Nk,Nk1)-(Z-E)*Nk1
    eq(MR,(1+(Xj+3)*l)*Nk2-((Xj+3)*(l+m)+Z+E*(Xj+2)*l)*Nk1
          +E*(Xj+2)*(l+m)*Nk)
    print("signed Hankel determinant, true mask commutator, fifth slope cancellation and paid one-primitive recurrence")

if __name__=="__main__":
    main()
