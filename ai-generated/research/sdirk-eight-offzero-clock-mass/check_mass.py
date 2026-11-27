"""Exact eliminants for the off-zero scalar-mass exclusion (Python + SymPy)."""
from itertools import product
from sympy import Matrix, Poly, Rational as Q, expand, gcd, integrate, invert, rem, resultant, symbols

X, u, v, t, d, z = symbols("X u v t d z")
C = 4*u**3-12*u*u+3*u+2
half = u*u-2*u-1

def gauss(x):
    return 70*x**4-140*x**3+90*x*x-20*x+1

def rho(f):
    return rem(expand(f), C, u)

def rhov(f):
    return rho(rem(expand(f), v*v-2, v))

def rhalf(f):
    return rem(expand(f), half, u)

def rt(f):
    return rem(expand(f), t*t-Q(1,2), t)

def moment(f, j, red):
    return red(sum(c/Q(i+j+1) for (i,),c in Poly(f,X).terms()))

def hankel(f, n, red):
    return red(Matrix(n,n,lambda i,j:moment(f,i+j,red)).det())

def prim(f):
    p = integrate(f,X)
    return p-p.subs(X,0)

def coprime_at(poly, a, variable=u):
    assert Poly(gcd(poly,a,variable),variable).degree() == 0

def fiber_gcd(A, B, modulus):
    def red(f):
        return rem(expand(f),modulus,u)
    A,B=red(A),red(B)
    while B:
        n=Poly(B,X).degree()
        inv=invert(Poly(B,X).LC(),modulus,u)
        assert red(inv*Poly(B,X).LC()) == 1
        while A and (m:=Poly(A,X).degree()) >= n:
            A=red(A-X**(m-n)*red(Poly(A,X).LC()*inv)*B)
        A,B=B,A
    return red(A*invert(Poly(A,X).LC(),modulus,u))

def inv_matrix(M):
    inv = invert(rhalf(M.det()),half,u)
    assert rhalf(inv*M.det())==1
    return M.adjugate().applyfunc(lambda a:rhalf(a*inv))

# The sole active off-zero clock d and a latest paid zero z cannot both
# be Gauss nodes: evaluate the reverse linear anchor.
line = (1-z*z)-2*d*(1-z)-2*(1-d)*(z-d)
res = expand(resultant(gauss(z),line,z))
assert res == 78400*d**8-313600*d**7+459200*d**6-246400*d**5-58880*d**4+121120*d**3-41800*d*d+640*d+1321
coprime_at(gauss(d),res,d)

# Independent short certificate for exactly three distinct zero clocks.
for image in (2-3*d,3*d-1,2*d-Q(1,2)):
    coprime_at(gauss(d),gauss(image),d)
print("Gauss reverse-line and mixed-repeat affine charts: no roots")

# Two distinct physical off-zero clocks, with one or two active sites.
G = invert(u+2,C,u)
assert rho(G*(u+2))==1
a = rho(G*(1+2*u))
Ds = (G,rho(1-G),(1+u)/2)
for D in (*Ds,Q(1,2)):
    coprime_at(C,rho(gauss(D)))
coprime_at(C,C.subs(u,-u))
for D in Ds[:2]:
    det=hankel((X-D)*(X-a)*(X-1+a),3,rho)
    coprime_at(C,det)
print("A second active off-zero site: no 5-site quadrature after reflection")

for D,g in ((rho(1-G),G),(Q(1,2),Q(1,2))):
    a = rho(g*(1+2*u))
    z = rho(2*D-1+v*(1-D))
    def norm(f):
        return rhov(f*f.subs(v,-v))
    coprime_at(C,norm(a-z))
    det=hankel((X-D)*(X-a)*(X-z),3,rhov)
    coprime_at(C,norm(det))
    coprime_at(C,rho(gauss(a)))
    p=(X-D)*(X-a)
    Ds=[rho(g*f-prim(f)) for f in (p,X*p)]
    fs=[rho(F*rho(gauss(a))-rho(F.subs(X,a))*gauss(X)) for F in Ds]
    assert fiber_gcd(*fs,C) == X-a
print("One active site, two physical off-zero clocks: no nodal or second-zero continuation")

# If every off-zero row has c=gamma=1/2, four actual zero clocks are
# pegged by the first and last triples.  One further zero clock cannot
# satisfy the two paid degree-six nodal moments, even if it repeats.
pairs = [(1+e*t,1-e*t if star else Q(3,2)+2*e*t)
         for e,star in product((1,-1),(True,False))]
for (a,b),(c,e) in product(pairs,repeat=2):
    P=(X-Q(1,2))*(X-a)*(X-b)*(X-1+c)*(X-1+e)
    det=hankel(P,2,rt)
    assert rt(det*det.subs(t,-t)) != 0
print("Half-diagonal chart: at least six distinct zero clocks")

# Six distinct zero clocks imply stage four is itself a distinct zero.
# The actual taps are fixed by c, Ac and Ac^2 at this row.  The pure
# restrictions Ch and Ah must both lie in span(h, L4(c)).
g=Q(1,2)
g1=g*g/2
for star in (True,False):
    w=2-u if star else 2*u
    tap_poly=-2+u+4*u*u-u**3
    r=0 if star else rhalf(2*u*(3*u-2)*invert(rhalf(tap_poly),half,u))
    a,b=[rhalf(g*(1+j)) for j in (u,w)]
    t21,t31,t32=[rhalf(g*j) for j in (u,w-r,r)]
    ha,hb=rhalf(g1*t21),rhalf(g1*t31)
    lam=rhalf((t21*g*g+g*a*a-a**3/3)*invert(ha,half,u))
    assert lam==Q(2,3)
    assert rhalf(t31*g*g+t32*a*a+g*b*b-b**3/3-lam*hb)==0
    assert rhalf(a+b-4*g/3) != 0
    coprime_at(half,rhalf(a+b-4*g/3))
    M=Matrix([[1,1,1],[g,a,b],[g*g-lam*g1,a*a,b*b]])
    taps=(inv_matrix(M)*Matrix([X-g,X*X/2-g*X,X**3/3-g*X*X])).applyfunc(rhalf)
    h=rhalf(g1*taps[0])
    coeff=inv_matrix(Matrix([[ha,rhalf(gauss(a))],[hb,rhalf(gauss(b))]]))
    def projected(F,Fa,Fb):
        j,k=(coeff*Matrix([rhalf(Fa),rhalf(Fb)])).applyfunc(rhalf)
        return rhalf(F-j*h-k*gauss(X))
    P=projected(X*h,a*ha,b*hb)
    H=projected(taps[1]*ha+taps[2]*hb+g*h,g*ha,t32*ha+g*hb)
    assert fiber_gcd(P,H,half)==rhalf((X-a)*(X-b))
print("Half-diagonal chart: Ch and Ah force the fourth clock to repeat")
