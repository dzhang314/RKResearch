"""Continuous first-stop certificate. Exact stdlib only; no physical tableau is fixed."""
from fractions import Fraction as Fr
from functools import cache
from itertools import combinations, product
from math import comb

if not __debug__:
    raise RuntimeError('Run without -O: every mathematical check is an assertion.')

J = (-8,252,-2520,11550,-27720,36036,-24024,6435)   # weight X
K = (-36,840,-6930,27720,-60060,72072,-45045,11440) # weight X^2
L = (-8,280,-3080,15400,-40040,56056,-40040,11440)  # weight X(1-X)
Jr = tuple(-(-1)**i*sum(c*comb(j,i) for j,c in enumerate(J) if j>=i)
           for i in range(8))   # -J(1-X), weight 1-X
XK, XL = (0,)+K, (0,)+L
XmL = tuple((L[j-1] if j else 0)-(L[j] if j<len(L) else 0)
            for j in range(9))
assert tuple(x-y for x,y in zip(XK,XmL))==J+(0,)
assert J[0]<0<sum(J) and Jr[0]<0
assert XK[-1]==XmL[-1]==XL[-1]>0 and J[-1]==Jr[-1]>0
def mom(w,k):
    if w=='X': return Fr(1,k+2)
    if w=='1-X': return Fr(1,(k+1)*(k+2))
    if w=='X^2': return Fr(1,k+3)
    if w=='X(1-X)': return Fr(1,(k+2)*(k+3))
    raise ValueError(w)

for p,w in ((J,'X'),(Jr,'1-X'),(K,'X^2'),(L,'X(1-X)')):
    for i in range(7):
        assert sum(c*mom(w,i+j) for j,c in enumerate(p))==0
for p,w in ((XK,'X'),(XmL,'X'),(XL,'1-X')):
    for i in range(7):
        assert sum(c*mom(w,i+j) for j,c in enumerate(p))==0

# Two projective endpoints and a common collection of rational isolating strips.
# Strip endpoints are hundredths. Strips within a row have positive gaps.
CASES = {
  'cubic, X': (J, J, [(5,9),(17,23),(35,41),(54,59),(73,77),
                      (88,90),(97,99)]),
  'all-interior, X': (XK, XmL, [(0,6),(7,17),(21,33),(39,51),(58,69),
                                   (75,85),(89,96),(97,100)]),
  'low exterior, X': (J+(0,), XK, [(5,9),(17,23),(35,41),(54,59),(73,77),
                                    (88,90),(97,99)]),
  'low exterior, 1-X': (Jr+(0,), XL, [(2,6),(11,17),(26,32),(45,51),
                                       (64,69),(81,85),(94,96)]),
}
UNIT = 2**24
D = 100*UNIT

def scaledpoly(P):
    return tuple(P[i]*D**(len(P)-1-i) for i in range(len(P)-1,-1,-1))
def ev(p,x):
    t=0
    for c in p: t=t*x+c
    return t

@cache
def anchor(case,s):
    A,B,wide=CASES[case]
    u,v=s.numerator,s.denominator
    p=scaledpoly([(v-u)*a+u*b for a,b in zip(A,B)])
    encl=[]
    for i,(lo,hi) in enumerate(wide):
        assert lo<hi and (i==0 or lo>wide[i-1][1])
        k=(-1)**(len(wide)-1-i)
        lo*=UNIT;hi*=UNIT
        y,z=k*ev(p,lo), k*ev(p,hi)
        assert y<=0<=z, (case,s,i,y,z)
        if y==0: hi=lo
        elif z==0: lo=hi
        else:
            while hi>lo+1:
                md=(lo+hi)//2
                t=k*ev(p,md)
                if t<0: lo=md
                elif t>0: hi=md
                else: lo=hi=md
        encl.append((lo,hi))
    return p,encl

def enclosure(case,s,t):
    p,ep=anchor(case,s)
    q,eq=anchor(case,t)
    R=[]
    for i,((l,h),(L,H)) in enumerate(zip(ep,eq)):
        lo=min(l,L); hi=max(h,H)
        k=(-1)**(len(ep)-1-i)
        # Two linear inequalities in the common parameter, checked at both
        # ends. These force a root in the closed strip throughout the cell.
        for v in (p,q): assert k*ev(v,lo)<=0<=k*ev(v,hi)
        assert not R or R[-1][1]<lo
        R.append((lo,hi))
    return R

def momentpair(I):
    # z_i=n_i/d_i; H_k = integral_0^1 Y^k product(Y-z_i) dY.
    # Return 420 * product(d_i) times (H_1,H_2). All scalings positive.
    P=[1]
    for n,d in I:
        assert d>0
        Q=[0]*(len(P)+1)
        for j,c in enumerate(P):
            Q[j]-=c*n; Q[j+1]+=c*d
        P=Q
    assert all(420%(k+1+i)==0 for k in (1,2) for i in range(len(P)))
    return (sum(c*(420//(2+i)) for i,c in enumerate(P)),
            sum(c*(420//(3+i)) for i,c in enumerate(P)))

def separated(R,role):
    a,idx=role
    al,ah=R[a]
    z=[((R[i][0],ah),(R[i][1],al)) for i in idx]
    V=[momentpair(corner) for corner in product(*z)]
    for i in (0,1):
        if all(c[i]>0 for c in V) or all(c[i]<0 for c in V):
            return True
    # Integer candidate directions p H_1 + q H_2 are equally paid.
    # Try one normal to each vector (a supporting direction). If all other
    # corner vectors lie in the same CLOSED half plane and those on its
    # boundary all point along v, the origin is not in the convex hull.
    for x,y in V:
        if (x,y)==(0,0): continue
        tests=[x*b-y*a for a,b in V]
        if min(tests)>=0 or max(tests)<=0:
            if all(t or x*a+y*b>0 for t,(a,b) in zip(tests,V)):
                return True
    return False

def prove(case):
    n=len(CASES[case][2]); hist={}
    degree=3 if case=='cubic, X' else 4
    roles=[(a,Q) for a in range(n) for Q in combinations(
        [i for i in range(n) if i!=a],degree) if sum(i<a for i in Q)>=2]
    todo=[(Fr(0),Fr(1),0,roles)]
    leaves=0
    while todo:
        s,t,depth,active=todo.pop()
        R=enclosure(case,s,t)
        left=[role for role in active if not separated(R,role)]
        hist[depth]=hist.get(depth,0)+len(active)-len(left)
        if not left:
            leaves+=1
            continue
        assert depth<18, (case,s,t,depth,left)
        m=(s+t)/2
        todo.extend([(s,m,depth+1,left),(m,t,depth+1,left)])
    print(f'{case}: {len(roles)} rank choices, {leaves} closed leaves, '
          f'maximum bisection depth {max(hist)}.')
    return len(roles),leaves,max(hist)

if __name__=='__main__':
    expected={'cubic, X':(70,1,0),'all-interior, X':(168,13,4),
              'low exterior, X':(63,14,10),'low exterior, 1-X':(63,1,0)}
    for case in CASES: assert prove(case)==expected[case]
    print('All uniform parameter boxes, root signs, and paid moment exclusions passed.')
