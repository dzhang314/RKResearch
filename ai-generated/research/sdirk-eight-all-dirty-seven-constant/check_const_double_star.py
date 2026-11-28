"""Both literal ends start D,S,S in the seven-clock constant graph."""
import sympy as S
from sympy.polys.rings import ring
from check_const_double_ends import K,a,gweight
R,X=ring('X',K)
q0,q1,q2=K.zero,K.one,K(2)
r0=q1/2

# Normalize t=x−m; the two singleton blocks have means ±a_0,
# squared half-gaps X,Y.  The equality of the two scaled endpoint B
# equations is (C−Y)(2−X)=(C−X)(2−Y).
Lh,bb,cc,XX,YY=S.symbols('ell d C X Y')
assert S.expand((cc-YY)*(2-XX)-(cc-XX)*(2-YY)-(cc-2)*(YY-XX))==0

def check(m,end):
    L4=lambda t:t**4-K(S.Rational(6,7))*m*m*t*t+K(S.Rational(3,35))*m**4
    h=m-1
    a0=2-m
    C=L4(h)+(3-2*m)**2
    assert C!=q2
    # Therefore X=Y, lambda=1, defeating the case with a shared
    # literal endpoint clock: those two physical pairs would coincide.
    if m==q1:
        assert not h
        print('m=1: equal endpoint pair')
        return
    assert h==m*a
    H=lambda t:((t-a0)**2-X)*((t+a0)**2-X)
    D=(-h,q0,h)
    # Multiply the scalar trace by r=(2−X)/2, retaining only the necessary
    # equation. Because H and (C−X)(2−X) have matching quadratic terms its
    # degree is at most 1.
    trace=R(8-2*m)+sum(R((2-2*m*w)/L4(d))*(L4(d)-H(d)+(C-X)*(2-X)) for d,w in zip(D,gweight))
    assert trace.degree()==1
    xx=-trace[(0,)]/trace[(1,)]
    assert xx not in (q0,q1,q2) and xx!=C
    k=2-xx
    r=k/2
    B=-4*(C-xx)/k
    aux=lambda d:(L4(d)-H(d).evaluate(X,xx))/r-B*r
    U=lambda d,g:L4(d)-g*(aux(d)+B*g)
    assert not U(h,r0)
    assert all(H(d).evaluate(X,xx) for d in D)
    # All four singleton rows are used by the two disjoint star
    # opener prefixes. The first fourth row can only read a double.
    # Forward D,S,S star has T_2=−1+2x−x²/2, independently of X.
    def fourth(g,x):
        f=K(S.Rational(4,3))-(k+4)*(x-1)/(3*k)
        n=-1+3*x-K(S.Rational(3,2))*x*x+x**3/6
        return g*f-n
    spare=-L4(h)/(B*r0)
    assert spare and spare!=r0 and not U(h,spare) and not U(-h,spare)
    assert all(fourth(spare,m+d) for d in (-h,h))
    G=U(q0,X).gcd(fourth(X,m))
    assert G.degree()==0
    print('quadratic diagonal: trace fixes the half-gap square and no fourth paired root passes')

check(q1,0)
check(q1/(1-a),-1)
print('verified both D,S,S starred ends are impossible')
