"""Exact divided-difference identity for the corrected SDIRK signed rule."""
from sympy import Poly, QQ, symbols, Rational

X,Y,R,A,B=symbols("X Y r alpha beta")
ring=(X,Y,R,A,B)


def P(value):
    return Poly(value,*ring,domain=QQ)


def subst(f,x,y):
    return P(f.as_expr().subs(x,y))


def exact(a,b):
    q,r=a.div(b)
    assert r.is_zero
    return q


def integral(f):
    return sum((Poly.from_dict({(i,0,k,j,l):v/QQ(jY+1)},*ring,domain=QQ)
                for (i,jY,k,j,l),v in f.rep.to_dict().items()),P(0))


def main():
    l=[P(v) for v in (1,2*Y-1,6*Y**2-6*Y+1,20*Y**3-30*Y**2+12*Y-1,
                       70*Y**4-140*Y**3+90*Y**2-20*Y+1)]
    K=sum(((2*j+1)*l[j]*subst(l[j],Y,R) for j in range(4)),P(0))
    H=P(A)*l[4]+P(B)*K
    M=P(Y-R)*l[4]
    Hr=subst(H,Y,R)
    Lr=subst(l[4],Y,R)

    def signed(f):
        # H(r)*I_r, so the proof introduces no coefficients with denominators
        # except the ordinary rational scalar integration moments.
        return Hr*integral(f)-P(B)*subst(f,Y,R)

    def divided(f):
        return exact(subst(f,Y,X)-f,P(X-Y))

    for j in range(4):
        assert integral(P(Y**j)*K)==P(R**j)
        assert integral(P(Y**j)*l[4]).is_zero
        assert signed(P(Y**j)*H).is_zero
    for j in range(3):
        assert signed(P(Y**j)*M).is_zero
    assert integral(P(Y**4)*l[4])==P(Rational(1,630))
    assert signed(P(Y**4)*H)==Hr*(P(A*Rational(1,630))-P(B*Rational(1,70))*Lr)
    assert signed(P(Y**3)*M)==Hr*Rational(1,630)
    assert subst(H,Y,X)*signed(divided(M))-subst(M,Y,X)*signed(divided(H))==-Hr*P(B)*Lr

    # H U may be added for every cubic cofactor; check all basis products.
    for j in range(4):
        F=H*P(Y**j)
        assert signed(F).is_zero
        assert signed(divided(F))==P(X**j)*signed(divided(H))
    print("verified symbolic signed Bezout identity and complete cubic cofactor action")


if __name__=="__main__":
    main()
