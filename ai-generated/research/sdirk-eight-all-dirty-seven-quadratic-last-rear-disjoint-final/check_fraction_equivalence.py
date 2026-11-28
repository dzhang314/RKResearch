"""Exact equality of two canonical fraction engines on independent frames."""
from pathlib import Path
import sys
P=Path(__file__).resolve().parent.parent
sys.path.insert(0,str(P/'sdirk-eight-all-dirty-seven-quadratic-last-rear-disjoint-two-star'))
import disjoint_projection as shared
from fast_fraction import F,frame,Cq

def agree(a,b):
    assert a.n*b.d==b.n*a.d
    assert a.n==b.n and a.d==b.d
    assert a.d.leading_coefficient()==1
    assert a.n.gcd(a.d).is_constant()

h,u=Cq.gens()
pairs=[
    ((h+u)*(h-3),(h+u)*(u+1),u*(2*h+3),u*(h+3)*(h+1)),
    ((h-u)**2*(u+5),(h-u)*(u**2+1),(h+u)*h,(h+u)*(u**2+1)),
    (h-u,2*(h-u),-3*(h+1),5*(h+1)),
    (Cq.constant(0),h+u,h-u,u+1),
    (h+u,u+1,-h-u,u+1)]
for a,b,c,d in pairs:
    f,g=F(a,b),F(c,d)
    p,q=shared.F(a,b),shared.F(c,d)
    for U,V in [(f,p),(g,q),(f+g,p+q),(f-g,p-q),(f*g,p*q),(f/g,p/q),
                (f**3,p**3)]:
        agree(U,V)

# These are full exact computations under the original physical frame,
# not representative samples of the bivariate polynomial values.
for front,rear in [('A2','S'),('A3','A2')]:
    eq_old,g_old=shared.frame(front,rear)
    eq_new,g_new=frame(front,rear)
    assert eq_old==eq_new and g_old==g_new
    print(front,rear,'complete exact rows and every guard agree',flush=True)
print('canonical fraction equivalence cross-check green',flush=True)
