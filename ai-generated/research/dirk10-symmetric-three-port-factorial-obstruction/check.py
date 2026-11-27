"""Independent exact finite and rational gates in the symmetric-chart obstruction."""
from fractions import Fraction as Q
from math import gcd
from itertools import combinations

S = (2, 3, 5, 7)

def smooth(n):
    n = abs(n)
    if not n:
        return False
    for p in S:
        while n % p == 0:
            n //= p
    return n == 1

C = []
for m in range(1, 7):
    for n in range(1, 11):
        if gcd(m,n) != 1:
            continue
        U,V,W=3*m*m-n*n,2*m*m-n*n,9*m*m-5*n*n
        if all(map(smooth,(n,U,V,W))):
            C.append([m,n,U,V,W,str(Q(3*m*m-2*n*n,3*V))])
assert C==[[1,1,2,1,4,"1/3"],[1,3,-6,-7,-36,"5/7"],[2,3,3,-1,-9,"2"]]
print("necessary low height c candidates",C)
p=11
B,Csmall=Q(5,7),Q(1,3)
re=lambda f:int(f.numerator) * pow(f.denominator,-1,p)%p
b,c=map(re,(B,Csmall))
assert (b+c)%p==0 and c*c%p==5
assert all(((21*x*x*c*c-9*(x*x+c*c)+5)%p==0)==((x*x-c*c)%p==0) for x in range(p))
assert (3*pow(7,-1,p)-5*pow(9,-1,p))%p != 0
print("mod 11 collapse for (b,c)=(5/7,1/3): a^2=c^2, no five-site symmetric rule")

FORMS=((1,0),(1,1),(1,-1),(1,2),(1,-2),(3,2),(3,-2))
dets={abs(a*d-b*c) for (a,b),(c,d) in combinations(FORMS,2)}
assert dets=={1,2,3,4,5,8,12} and all(120%d==0 for d in dets)
print("all determinant sizes",sorted(dets),"and bounds m<=480, n<=720")
out=[]
for n in [i for i in range(1,721) if smooth(i)]:
    for m in [i for i in range(1,481) if smooth(i)]:
        if gcd(m,n)==1 and all(smooth(a*m+b*n) for a,b in FORMS):
            out.append([m,n,145*m*m-159*n*n])
expected=[[4,1,2161],[6,1,5061],[1,2,-491],[1,3,-1286],[4,3,889],[2,5,-3395],[2,7,-7211]]
assert out==expected and all(not smooth(v) for _,_,v in out)
print("all smooth separation candidates and the nonsmooth terminal numerators",out)

# Independently integrate the scalar cardinal polynomials on squared
# centered knots. Verify the displayed rational formula on a symbolic linear
# polynomial and all four test coefficients of the a-cardinal numerator.
def conv(U,V):
    out=[Q(0)]*(len(U)+len(V)-1)
    for i,u in enumerate(U):
        for j,v in enumerate(V):
            out[i+j]+=u*v
    return out
def moment(xs):return sum(v/Q(2*k+1) for k,v in enumerate(xs))
pa=conv(conv(conv([0,1],[-1,1]),[-4,1]),[Q(-4,9),1])
assert moment(pa)==-Q(2,135)
p1=conv(conv([0,1],[-4,1]),[Q(-4,9),1])
const=moment([0]+p1)
slope=-moment(p1)
assert (const,slope)==(-Q(53,315),Q(29,189))
for m,n,_ in out:
    y=Q(m,n)**2
    w1=(145*y-159)/(3150*(y-1))
    assert w1== (const+slope*y) / (2*(1-y)*(1-4)*Q(5,9))
    wa=-1/(15*y*(y-4)*(y-1)*(9*y-4))
    assert wa==moment(pa) / (2*y*(y-4)*(y-1)*(y-Q(4,9)))
print("independent scalar cardinal integral coefficients and all terminal weights verified")
