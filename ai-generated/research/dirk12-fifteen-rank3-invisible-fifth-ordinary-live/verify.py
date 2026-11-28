#!/usr/bin/env python3
"""Exact rank and fixed-quartic checks for the genuine fifth ordinary row."""
import sympy as S


def eq(f,g=0):
    assert S.cancel(f-g)==0,S.factor(f-g)


def main():
    T,x,y,b,a=S.symbols('T x y b a')
    W=T*T*(T-1)**2*(T-S.Rational(1,2))
    Db=5*x*x-5*x+1
    beta=x*(x-1)*(2*x-1)/(2*Db)
    eq(beta*S.diff(W,T).subs(T,x),W.subs(T,x))
    S0=3*x*x-2*x*y-2*x+y
    Y=x*(3*x-2)/(2*x-1)
    eq(S0.subs(y,Y));eq(S0.subs(x,S.Rational(1,2)),-S.Rational(1,4))
    eq(Y.subs(x,S.Rational(2,3)));eq(Y.subs(x,S.Rational(1,3)),1)
    h=x-S.Rational(1,2)
    B=18*h**4-h*h+S.Rational(1,8)
    eq(72*B,(36*h*h-1)**2+8)
    eq((W-beta*S.diff(W,T)).subs(T,y).subs(y,Y),
       x*x*(x-1)**2*(3*x-2)*(3*x-1)*B/(2*(2*x-1)**5))
    print("actual first-Legendre-root third-Jacobi rank: nonzero bracket at k(y)=0")
    L={j:S.diff(S.legendre(j,2*T-1),T) for j in (5,6,7)}
    H=S.Rational(98,45)*L[5]+S.Rational(26,9)*L[6]+L[7]
    eq(H,S.Rational(728,3)*T*T*(99*T**4-231*T**3+189*T*T-63*T+7))
    eq(H.subs(T,0));eq(S.diff(H,T).subs(T,0))
    M=S.Matrix([[L[j].subs(T,0) for j in (5,6)],
                [S.diff(L[j],T).subs(T,0) for j in (5,6)]])
    eq(M.det(),7560)
    F=99*T**4-165*T**3+90*T*T-18*T+1
    eq(S.diff(T*H,T,2),10192*T*F)
    print("unique double-zero Jacobi profile and its physical fixed quartic")
    P=73;rs=[24,36,47,65]
    assert 8**2<P<9**2 and all(P%j for j in range(2,9))
    assert [s for s in range(P) if int(F.subs(T,s))%P==0]==rs
    assert all(s and int(S.diff(F,T).subs(T,s))%P for s in rs)
    roots=[int(L[6].subs(T,s))%P for s in rs]
    assert roots==[58,7,34,54]
    gate=a**4*(2*b-a)*L[6].subs(T,b)-b**3*(2*b*b-6*a*b+5*a*a)*L[6].subs(T,a)
    pairs=[[int(gate.subs({a:i,b:j}))%P for j in rs if i!=j] for i in rs]
    assert pairs==[[13,69,37],[9,26,32],[21,4,1],[61,30,8]]
    print(f"prime {P}, simple roots {rs}, nonzero L6' {roots}, ordered pair checks {pairs}")


if __name__=='__main__':
    main()
