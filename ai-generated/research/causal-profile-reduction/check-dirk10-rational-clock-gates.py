#!/usr/bin/env python3
"""Independent exact arithmetic for the DIRK10/11 rational clock cuts."""
from fractions import Fraction as Q
from itertools import product
from math import prod, isqrt


def trim(a):
    a = list(a)
    while a and not a[-1]:
        a.pop()
    return a


def add(a, b):
    return trim((a[j] if j < len(a) else 0) + (b[j] if j < len(b) else 0)
                for j in range(max(len(a), len(b))))


def scl(a, b):
    return trim(x * b for x in a)


def sub(a, b):
    return add(a, scl(b, -1))


def mul(a, b):
    out = [0] * max(0, len(a) + len(b) - 1)
    for j, x in enumerate(a):
        for k, y in enumerate(b):
            out[j + k] += x * y
    return trim(out)


def power(a, j):
    out = [1]
    for _ in range(j):
        out = mul(out, a)
    return out


def divrem(a, b):
    a = trim(a)
    quo = [0] * max(0, len(a) - len(b) + 1)
    while len(a) >= len(b):
        j = len(a) - len(b)
        c = Q(a[-1]) / b[-1]
        quo[j] = c
        a = sub(a, [0] * j + scl(b, c))
    return trim(quo), a


def ev(a, x):
    b = 0
    for c in reversed(a):
        b = x * b + c
    return b


def bareiss(M):
    A = [[Q(x) for x in row] for row in M]
    sg, prev = 1, 1
    for k in range(len(A) - 1):
        d = next((j for j in range(k, len(A)) if A[j][k]), None)
        if d is None:
            return 0
        if d != k:
            A[k], A[d] = A[d], A[k]
            sg = -sg
        pivot = A[k][k]
        for j in range(k + 1, len(A)):
            for l in range(k + 1, len(A)):
                A[j][l] = (pivot*A[j][l] - A[j][k]*A[k][l]) / prev
            A[j][k] = 0
        prev = pivot
    return sg*A[-1][-1]


def res(A, B, m, n):
    assert len(A) <= m + 1 and len(B) <= n + 1
    a = ([0]*(m+1-len(A)) + list(reversed(A)))
    b = ([0]*(n+1-len(B)) + list(reversed(B)))
    mat = ([[0]*i+a+[0]*(n-1-i) for i in range(n)] +
           [[0]*i+b+[0]*(m-1-i) for i in range(m)])
    return bareiss(mat)


def early_coeff(t):
    return [108-108*t+33*t*t-3*t**3, -504+252*t-28*t*t,
            1008-168*t, -1008, 420]


def profile_coeff(t):
    a = [2*t**3-37*t*t+192*t-252, 42*t*t-378*t+756, 112*t-672, 252]
    b = [6*t**4-83*t**3+363*t*t-468*t-108,
         56*t**3-616*t*t+1596*t+504, 336*t*t-1848*t-1008, 336*t+1008]
    c = [6*t**3-81*t*t+351*t-486, 56*t*t-609*t+1638, 336*t-2016, 756]
    return a, b, c


def coefficients(t):
    a, _, c = profile_coeff(t)
    R = [0, 5*(2*t-3)*t*(t-6)]
    Z = scl(c, 2*t)
    U = [0] + scl(a, 12)
    F = sub([0]*4+[840*(2*t-3)], scl(Z, 4))
    return R, Z, U, F


def one_equations(t):
    R, Z, U, F = coefficients(t)
    W, S = add(R, Z), add(U, F)
    B0, ee = 10*(3-2*t), 6-8*t
    V = sub(scl(S, t), mul(W, [ee, 2]))
    d = [t, -1]
    w = sub(sub(add(scl(mul(mul(power(d, 2), R), W), B0),
                    scl(mul(mul(d, V), add(R, F)), t)),
                scl(power(V, 2), t)),
            scl(mul(mul(d, W), V), ee))
    shift = sub(S, W)
    sd = add(scl(W, B0), scl(shift, ee))
    ld = sub(scl(mul(S, shift), t), mul(sd, W))
    yd = sub(mul(Z, S), mul(F, W))
    y = add(mul(mul(yd, mul([0, 1], add(scl(W, -B0), scl(shift, 2*t)))), W),
            scl(mul(sub(mul(R, S), mul(U, W)), ld), t))
    return y, w


def excludes_root(c, p):
    assert c[-1] % p and all(ev(c, x) % p for x in range(p))


def split_mod(c, p):
    c = trim(x % p for x in c)
    for x in range(p):
        while len(c) > 1 and ev(c, x) % p == 0:
            q, r = divrem(c, [-x, 1])
            assert not any(int(z) % p for z in r)
            c = trim(int(z) % p for z in q)
    return len(c) == 1


ORIGIN = [898128, -4953312, 11344536, -14054040, 10142289,
          -4220844, 917612, -76572, 144]
TERMINAL = [-17391024, 178564176, -788814936, 1958064192,
            -2995869699, 2926969947, -1853235405, 786863737,
            -252973320, 71305848, -14737680, 1224720]
CONSTANT = [-104976, 1123632, -5695272, 16545168, -29284353,
            32274681, -21940163, 8813235, -1940256, 244216, -37584, 3888]
Y7 = [-2798960508, 15509199708, -34140048183, 39352695372,
      -27569823944, 13830539904, -5243842800, 925888320]
Y12 = [1342328112, -10899798048, 40534482024, -100843722792,
       203063839947, -333562344624, 412854204240, -374892171456,
       266419563040, -161999440128, 79899892992, -25577192448, 3673320192]
W2A, W2B = [2178, -7405, 6300], [7572, -24500, 19845]
PHI = [1, -14, 56, -84, 42]
FIXED_FRONT = [1314, -87, -100, 125]
REGULAR = [-30, 175, -308, 168]
EXCEPTIONAL = [-4, 26, -49, 28]


def verify_prescribed_poles():
    for q, p in [(ORIGIN, 23), (TERMINAL, 11), (CONSTANT, 11), (PHI, 11),
                 (FIXED_FRONT, 13)]:
        excludes_root(q, p)
    # Each side is a polynomial in t of degree at most 28.
    # A determinant term uses n rows from E and 4 from the other operand.
    for t in range(29):
        e = early_coeff(t)
        a, b, _ = profile_coeff(t)
        e0 = 170698752000//12**4*(t-6)**3*(t-2)*ev(ORIGIN, t)
        e1 = 42674688000//6**4*(t-6)**4*(t-3)*ev(TERMINAL, t)
        e2 = 32006016000//6**4*(t-6)**4*(t-3)*ev(CONSTANT, t)
        assert res(e, a, 4, 3) == e0
        assert res(e, sub([0]+scl(a, 2), b), 4, 4) == e1
        assert res(e, b, 4, 3) == e2
    print("prescribed slopes and Jacobi/front modular rational-root cuts PASS")


def verify_unit_head_resultants():
    for q, p in [(Y7, 11), (Y12, 11), (W2A, 17), (W2B, 17),
                 ([3, -37, 180, -261, -25, 420], 13)]:
        excludes_root(q, p)
    # R, Z, U, F have total degrees <= 4,4,4,5;
    # B0,ee are affine. Total degrees of the two expressions are <= 25;
    # reducing by E (constant leading coefficient) does not raise total degree.
    # A padded (4,3) determinant consequently has t-degree <= 9+4*25.
    for t in range(110):
        e = early_coeff(t)
        rawY, rawW = one_equations(t)
        Y, W = scl(divrem(rawY, e)[1], 68359375), scl(divrem(rawW, e)[1], 350)
        assert all(Q(c).denominator == 1 for c in Y+W)
        common = (3*t-2)**2*(4*t-3)*(5*t-3)**2
        ry = (404295860789716243743896484375000000*t**12*(t-6)**18*
              (t-3)**10*(t-2)**2*(2*t-3)**4*common*ev(Y7,t)*ev(Y12,t))
        rw = (-3906984375000000*t**8*(t-6)**9*(t-3)**5*(t-2)*
              (2*t-3)**8*(3*t-2)**3*(4*t-3)**2*(5*t-3)**3*ev(W2A,t)*ev(W2B,t))
        assert res(e, Y, 4, 3) == ry, ("Y", t)
        assert res(e, W, 4, 3) == rw, ("W", t)
    for a in range(1, 14):
        t = Q(4)-a-Q(1,a)
        assert a**3*ev(early_coeff(t), 1+a) == (a+1)**2*ev([3,-37,180,-261,-25,420],a)
    for s in range(5):
        assert ev(early_coeff(Q(2,3)),s)==Q(28,9)*(3*s-2)**3*(5*s-2)
        assert ev(early_coeff(s),s)==(3*s-2)*(4*s-3)*(5*s-3)*(7*s-6)
    for j in (Q(5,21),Q(7,27),Q(2,9)):
        assert isqrt(j.numerator)**2 != j.numerator or isqrt(j.denominator)**2 != j.denominator
    print("rational unit-head resultants (early a,b,u,y,w) and split guards PASS")


def specialized(s, t, k):
    a, _, c = profile_coeff(t)
    D = 5*s**4*(2*t-3)
    R,Z,U,F = (ev(e,s) for e in coefficients(t))
    r,z,e,f=(Q(q)/D for q in (R,Z,U,F))
    B,N,E=Q(t)/(10*(3-2*t)), Q(s)/(5*(3-2*t)), Q(3-4*t)/(5*(3-2*t))
    SS=1+(k-1)*E; L=k*(k-1)*B-SS
    yN,yD=e-r*k,z*k-f
    wN,wD=r*L,z*SS-(k-1)*B*f
    K=yD*(-Q(s)/t+(k-1)*N)-yN*L
    return K,yN,yD,wN,wD,[e,f]


MOMENT_INV=[[300,-2100,4200,-2520],[-2100,16800,-36120,22680],
            [4200,-36120,81480,-52920],[-2520,22680,-52920,35280]]


def q4(s,t):
    v=[(6-3*t)*(6-t)*(3-t),2*s*(6-t)*(3-t),3*s*s*(6-t),12*s**3]
    return mul([1,-1],[sum(a*b for a,b in zip(row,v)) for row in MOMENT_INV])


def verify_fixed_front_and_local():
    for k in range(4):
        assert specialized(Q(2,5),Q(2,3),k)[0] == -Q(4,225)*ev(FIXED_FRONT,k)
        assert specialized(Q(2,3),Q(2,3),k)[0] == -Q(12,25)*(k-6)*(k-3)**2
    _,yn,yd,wn,wd,_=specialized(Q(2,3),Q(2,3),6)
    assert yd==wd==0 and yn!=0
    _,yn,yd,wn,wd,_=specialized(Q(2,3),Q(2,3),3)
    assert yn==yd and wn==wd and yd*wd != 0
    P = 11
    sq = {x*x%P for x in range(P)}
    candidates = [(s,t) for s,t in product(range(P),repeat=2)
                  if not ev(early_coeff(t),s)%P and ((t-2)*(t-6))%P in sq]
    assert candidates==[(0,2),(0,6),(6,0),(7,8),(8,8),(9,0),(9,6)]
    sm,tm=Q(2,5),Q(2,3)
    def mod(x):
        x=Q(x)
        return x.numerator*pow(x.denominator,-1,P)%P
    assert [k for k in range(P) if not mod(specialized(sm,tm,k)[0])]==[9]
    _,yn,yd,wn,wd,M=specialized(sm,tm,9)
    assert mod(yd)*mod(wd)
    y,w=yn/yd,wn/wd
    assert (mod(y),mod(w))==(9,1)
    MQ=mul(M,q4(sm,tm))
    Ly,Lw=-ev(MQ,y)/ev(PHI,y),-ev(MQ,w)/ev(PHI,w)
    l1=(Ly-Lw)/(y-w);l0=Ly-l1*y
    SUF, rem=divrem(add(MQ,mul(PHI,[l0,l1])),mul([-y,1],[-w,1]))
    assert not rem and len(SUF)==4 and mod(SUF[-1])
    monic=[mod(c/SUF[-1]) for c in SUF]
    assert monic==[1,1,9,1] and not split_mod(monic,P)
    q0=mul([1,-1],MOMENT_INV[0])
    assert sub(scl(PHI,q0[0]),q0)==[0]+scl(REGULAR,60)
    assert sub(q0,scl(PHI,60))==scl(EXCEPTIONAL,-60)
    primes=[11,13,17,19,29,31,37,41]
    assert all(not split_mod(REGULAR,p) and not split_mod(EXCEPTIONAL,p) for p in primes)
    print("fixed t=2/3 front and integral mod-11 cut, both infinity residue cubics PASS")



class Jet:
    """Exact scalar modulo delta squared."""
    def __init__(self, x=0, y=0):
        self.x, self.y = Q(x), Q(y)

    @staticmethod
    def coerce(other):
        return other if isinstance(other, Jet) else Jet(other)

    def __add__(self, other):
        other = self.coerce(other)
        return Jet(self.x+other.x, self.y+other.y)

    __radd__ = __add__

    def __neg__(self):
        return Jet(-self.x, -self.y)

    def __sub__(self, other):
        return self+-self.coerce(other)

    def __rsub__(self, other):
        return self.coerce(other)+-self

    def __mul__(self, other):
        other = self.coerce(other)
        return Jet(self.x*other.x, self.x*other.y+self.y*other.x)

    __rmul__ = __mul__

    def __bool__(self):
        return bool(self.x or self.y)

    def inverse(self):
        return Jet(1/self.x, -self.y/self.x**2)

    def __truediv__(self, other):
        return self*self.coerce(other).inverse()

    def __rtruediv__(self, other):
        return self.coerce(other)*self.inverse()

    def __pow__(self, n):
        return prod(self for _ in range(n))


def verify_boundary_11():
    p = 11

    def mod(x):
        x = Q(x)
        return x.numerator*pow(x.denominator, -1, p)%p

    # s ≡ 6, t ≡ 0: the front at kappa=t k has integral coefficients.
    s = 6
    a, _, c = profile_coeff(0)
    r, z, e, f = Q(-6,s**3), Q(-2,15*s**4)*ev(c,s), Q(-4,5*s**3)*ev(a,s), 168
    K = add(mul([-f,z], [-s,Q(s,15)]), mul([-e,r], [0,-Q(1,5),Q(1,30)]))
    assert mod(K[-1]) and all(mod(ev(K,k)) for k in range(p))

    # s ≡ 12/5, t ≡ 6: exact first-order expansions at the finite root k=-2.
    s,t,k = Jet(Q(12,5),Q(93,448)),Jet(6,1),Jet(-2,-Q(1,12))
    assert not ev(early_coeff(t),s)
    D = 5*s**4*(2*t-3)
    r,z,e,f = [ev(v,s)/D for v in coefficients(t)]
    B,N,E = t/(10*(3-2*t)), s/(5*(3-2*t)), (3-4*t)/(5*(3-2*t))
    S = 1+(k-1)*E
    L = k*(k-1)*B-S
    yd,wd = z*k-f, z*S-(k-1)*B*f
    assert not (yd*(-s/t+(k-1)*N)+(r*k-e)*L)
    assert not (yd.x or wd.x or L.x)
    assert (yd.y,wd.y,L.y) == (Q(28,9),Q(14,9),-Q(1,90))
    assert (r.x,z.x,e.x,f.x)==(0,84,Q(336,5),-168)
    assert (mod(84*Q(12,5)**3*5), mod(Q(-56,5)), mod(yd.y),
            mod(wd.y), mod(Q(-25,864))) == (6,2,8,4,5)
    # Two exact residue cubics for the possibilities k finite or at infinity.
    Q0 = mul([1,-1],[row[3] for row in MOMENT_INV])
    M = [e.x,f.x]
    MQ = mul(M,Q0)
    l0 = -MQ[0]
    for y_pole in (False, True):
        l1 = -M[1]*Q(Q0[4],42) if y_pole else -(MQ[1]+14*MQ[0])
        N0 = add(MQ,mul(PHI,[l0,l1]))
        j = 1 if y_pole else 2
        assert not any(N0[:j])
        cubic = N0[j:]
        assert len(cubic)==4 and mod(cubic[-1])
        assert not split_mod(list(map(mod,cubic)),p)
    print("mod-11 boundary cuts (6,0) and (9,6) PASS")


def height_cut(limit=10**9):
    """Exhaust all primitive ratio heights in the given finite box."""
    from math import gcd

    small = (2,3,5,7)
    infinity_blocked = (11,13,17,19,29,31,37,41)

    def smooth(t=1, j=0):
        if j==len(small):
            yield t
        else:
            while t<=limit:
                yield from smooth(t,j+1)
                t*=small[j]

    def strip_small(n):
        for p in small:
            while n%p==0:
                n//=p
        return n

    def fourth(n):
        return isqrt(isqrt(n))**4==n

    def prime(n):
        return n>1 and all(n%d for d in range(2,isqrt(n)+1))

    values = sorted({v*q**4 for v in smooth()
                     for q in range(1,isqrt(isqrt(limit//v))+1)
                     if gcd(q,210)==1 and all(q%p for p in infinity_blocked)})
    primes = [p for p in range(11,150) if prime(p)]
    residues = {p:{t for t in range(p)
                   if any(ev(early_coeff(t),s)%p==0 for s in range(p))}
                for p in primes}
    total, fourth_cases, candidates = 0, 0, []
    for i,n in enumerate(values):
        for m in values[:i]:
            if gcd(m,n)!=1:
                continue
            for a in (-m,m):
                total+=1
                shifted_numer = 17*a*n-5*a*a-5*n*n
                if not shifted_numer or not fourth(strip_small(abs(shifted_numer))):
                    continue
                fourth_cases+=1
                num,den = 4*a*n-a*a-n*n,a*n
                if all(not den%p or num*pow(den,-1,p)%p in residues[p] for p in primes):
                    candidates.append((a,n,Q(num,den)))
    assert candidates == [(1,3,Q(2,3))]
    if limit == 10**9:
        assert (len(values),total,fourth_cases)==(5898,1104666,19)
    print(f"height ≤{limit}: {len(values)} integers, {total} primitive signed ratios, "
          f"{fourth_cases} shifted-fourth candidates; only t=2/3, already excluded")


if __name__ == "__main__":
    verify_prescribed_poles()
    verify_unit_head_resultants()
    verify_fixed_front_and_local()
    verify_boundary_11()
    height_cut()
