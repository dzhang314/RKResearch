#!/usr/bin/env python3
"""Verify the exact finite enclosure certificate in PROOF.md.

Only rational arithmetic is used. The cells cover the full continuous
parameter interval; no hypothesis restricts the original nodes to rationals.
"""
from fractions import Fraction as F
from itertools import product

BREAKS = (0, 1, 2, 3, 4, 5, 6, 8, 10, 12, 16, 20, 24, 32, 48, 64)
ROOT_LO = (
    ((557, 1222, 1988, 2754, 3415, 3884), (557, 1222, 1988, 2754, 3415, 3884)),  # s = 0/64
    ((528, 1198, 1971, 2742, 3410, 3883), (524, 1196, 1969, 2741, 3409, 3882)),  # s = 1/64
    ((502, 1177, 1955, 2732, 3404, 3881), (496, 1172, 1951, 2730, 3403, 3881)),  # s = 2/64
    ((479, 1157, 1940, 2723, 3400, 3879), (472, 1150, 1935, 2719, 3398, 3879)),  # s = 3/64
    ((459, 1139, 1926, 2714, 3395, 3878), (451, 1131, 1920, 2710, 3393, 3877)),  # s = 4/64
    ((442, 1123, 1914, 2706, 3391, 3877), (433, 1114, 1907, 2701, 3389, 3876)),  # s = 5/64
    ((427, 1108, 1902, 2698, 3387, 3875), (418, 1098, 1894, 2693, 3384, 3875)),  # s = 6/64
    ((403, 1081, 1881, 2684, 3380, 3873), (393, 1070, 1872, 2678, 3377, 3872)),  # s = 8/64
    ((383, 1058, 1862, 2671, 3373, 3871), (374, 1047, 1852, 2665, 3370, 3870)),  # s = 10/64
    ((367, 1038, 1845, 2660, 3367, 3869), (359, 1027, 1835, 2653, 3363, 3868)),  # s = 12/64
    ((344, 1004, 1814, 2639, 3356, 3866), (336, 993, 1804, 2631, 3352, 3864)),  # s = 16/64
    ((327, 977, 1788, 2620, 3346, 3862), (321, 966, 1778, 2612, 3341, 3861)),  # s = 20/64
    ((314, 954, 1765, 2603, 3336, 3859), (309, 944, 1755, 2595, 3332, 3858)),  # s = 24/64
    ((296, 918, 1726, 2572, 3319, 3854), (292, 910, 1717, 2564, 3315, 3852)),  # s = 32/64
    ((275, 869, 1665, 2520, 3288, 3843), (273, 865, 1660, 2515, 3285, 3842)),  # s = 48/64
    ((262, 836, 1619, 2476, 3259, 3833), (262, 836, 1619, 2476, 3259, 3833)),  # s = 64/64
)
CAPS = ((-744, -38), (-740, -50), (-741, -65), (-746, -88), (-758, -114), (-750, -134), (-673, -39), (-692, -99), (-704, -162), (-609, -68), (-650, -187), (-692, -301), (-594, -237), (-490, -221), (-713, -737))

DEN = 4096
RATIO = (F(2, 3), F(6, 7))
SCALE = 10**6

def require(condition, message):
    if not condition:
        raise ArithmeticError(message)

def normalized_ratio(s, c):
    return c*s/(1-s+c*s)

def monic_corner_polynomial(s, r):
    # W=x(1-x) (s+(1-s)x) (r+(1-r)x).
    w = (s*r, (1-s)*r+s*(1-r), (1-s)*(1-r))
    moments = [sum(w[j]/((i+j+2)*(i+j+3)) for j in range(3))
               for i in range(12)]
    m = [[moments[i+j] for j in range(6)]+[-moments[i+6]]
         for i in range(6)]
    for i in range(6):
        p = m[i][i]
        require(p > 0, "corner Gram pivot")
        m[i] = [x/p for x in m[i]]
        for j in range(6):
            if j != i:
                h = m[j][i]
                m[j] = [x-h*y for x,y in zip(m[j],m[i])]
    q = [m[i][6] for i in range(6)]+[F(1)]
    require(all(sum(q[j]*moments[i+j] for j in range(7)) == 0
                for i in range(6)), "corner orthogonality")
    return q

def eval_polynomial(q, x):
    z = F(0)
    for a in reversed(q):
        z = z*x+a
    return z

def check_corner(s, ratio, lower_numerators):
    q = monic_corner_polynomial(s, normalized_ratio(s, ratio))
    I = tuple((F(j,DEN),F(j+1,DEN)) for j in lower_numerators)
    require(len(I)==6, "six intervals")
    require(all(0<a<b<1 for a,b in I), "unit intervals")
    require(all(x[1]<y[0] for x,y in zip(I,I[1:])), "disjoint intervals")
    require(all(eval_polynomial(q,a)*eval_polynomial(q,b)<0 for a,b in I),
            "corner endpoint sign")
    return I

def gamma_delta(r,z):
    return ((1-r[1])*(1-z[1]),(1-r[0])*(1-z[0])), (
            r[0]+(1-r[0])*z[0],r[1]+(1-r[1])*z[1])

def centered(x,z):
    # (x-z)/(1-z) increases in x and decreases in z on the unit square.
    return ((x[0]-z[1])/(1-z[1]),(x[1]-z[0])/(1-z[0]))

def multiply(p,q):
    r = [F(0)]*(len(p)+len(q)-1)
    for i,a in enumerate(p):
        for j,b in enumerate(q):
            r[i+j] += a*b
    return r

def integral_of_product(*factors):
    p = [F(1)]
    for q in factors:
        p = multiply(p,q)
    return sum(x/(i+1) for i,x in enumerate(p))

def phase_a(g,d,c,l,r):
    return integral_of_product((d,g),(c,1),(-l,1),(-r,1),(0,1,-1))

def phase_b(g,d,l,m,r):
    return integral_of_product((d,g),(-l,1),(-m,1),(-r,1),(1,-2,1))

def main():
    require(BREAKS[0]==0 and BREAKS[-1]==64, "full s cover")
    require(all(x<y for x,y in zip(BREAKS,BREAKS[1:])), "s order")
    require(len(ROOT_LO)==len(BREAKS) and len(CAPS)==len(BREAKS)-1,
            "table dimensions")
    endpoints = [
        tuple(check_corner(F(i,64),c,row)
              for c,row in zip(RATIO,t))
        for i,t in zip(BREAKS,ROOT_LO)
    ]
    for i,(a,b) in enumerate(CAPS):
        s0,s1 = (F(BREAKS[j],64) for j in (i,i+1))
        r = normalized_ratio(s0,RATIO[0]),normalized_ratio(s1,RATIO[1])
        beta = tuple((low[0],high[1])
                     for low,high in zip(endpoints[i+1][1],endpoints[i][0]))
        require(all(0<x<=y<1 for x,y in beta), "enclosing roots")
        # All five test parameters are interval-enclosed. Evaluate a
        # multiaffine polynomial only at the 32 rectangular vertices.
        z = beta[1]
        c = (-(centered(beta[0],z)[1]),-(centered(beta[0],z)[0]))
        box_a = (*gamma_delta(r,z),c,centered(beta[2],z),centered(beta[4],z))
        z = beta[0]
        box_b = (*gamma_delta(r,z),*(centered(beta[j],z) for j in (1,3,5)))
        require(all(lo<=hi for lo,hi in (*box_a,*box_b)), "vertices bracket")
        require(a<0 and b<0, "strict cap")
        require(all(phase_a(*v)<=F(a,SCALE) for v in product(*box_a)), "phase A")
        require(all(phase_b(*v)<=F(b,SCALE) for v in product(*box_b)), "phase B")
    a, b = (max(v[i] for v in CAPS) for i in (0, 1))
    require((a,b)==(-490,-38), "uniform caps")
    print(f"Verified: {len(CAPS)} cells; phase A <= {a}/{SCALE}; phase B <= {b}/{SCALE}.")

if __name__ == "__main__":
    main()
