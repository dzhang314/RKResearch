"""Small shared scalar polynomials, with no projection performed at import."""
def l3(y,d):return 5*y**3-3*d*d*y
def l4(y,d):return 35*y**4-30*d*d*y*y+3*d**4
def kk(y,z,d):
    return -9*d**6+15*d**4*y*y-75*d**4*y*z+15*d**4*z*z+105*d*d*y**3*z-45*d*d*y*y*z*z+105*d*d*y*z**3-175*y**3*z**3
def den(u):return 2*(u-2)*(u**3-3*u*u+1)
def hub(u):return -2+u+4*u*u-u**3
def kap(u):return 1+2*u-u*u
def num(u):return (1+4*u-4*u*u)*hub(u)+4*u*u*(3*u-2)

from itertools import combinations
from sympy.polys.agca.extensions import MonogenicFiniteExtension

class ExactTower(MonogenicFiniteExtension):
    # Field quotient must use the inverse modulo the checked irreducible
    # extension polynomial, not exact divisibility of representatives.
    def exquo(self,x,y):
        return x/y
    quo=exquo
    def convert(self,x,base=None):
        if getattr(x,'ext',None)==self:
            return x
        return super().convert(x,base)

def phase(F,u,mode):
    if not u or not kap(u):return None
    if mode=='A':
        if 3*u==2*F.one:return None
        assert hub(u)
        q=num(u)/hub(u)
        return (1+2*u,q/2) if q else None
    if u in (F.one,2*F.one):return None
    return 3-u,kap(u)/2

def affine_two(rows,F):
    for (a,b,c),(d,e,f) in combinations(rows,2):
        det=a*e-b*d
        if det:
            B,t=(c*e-b*f)/det,(a*f-c*d)/det
            if not B or any(g*B+h*t!=i for g,h,i in rows):
                return None
            return (B,t)
    row=next(((a,b,c) for a,b,c in rows if a or b),None)
    if row is None:
        return None if any(c for a,b,c in rows) else 'free'
    a,b,c=row
    if any((a*i!=g*c if a else b*i!=h*c) for g,h,i in rows):
        return None
    if not b and not c:return None # fixes B=0
    return 'rank one'
