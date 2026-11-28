import sympy as S
from sympy.polys.fields import field
FF,d=field('d',S.QQ)
X=S.Symbol('d')
def kap(u):return 1+2*u-u*u
def H(u):return -2+u+4*u*u-u**3
def qnum(u):return (1+4*u-4*u*u)*H(u)+4*u*u*(3*u-2)
def shape(u,lab):
    """Input u is literal D clock coordinate, not always the second gap."""
    if lab=='A2':
        gap=u
        return kap(gap)/2,2*u,qnum(gap)/(2*H(gap)),[gap,gap-2,3*gap-2,kap(gap),H(gap),qnum(gap)]
    if lab=='A3':
        gap=u/2
        return qnum(gap)/(2*H(gap)),gap,kap(gap)/2,[gap,gap-2,3*gap-2,kap(gap),H(gap),qnum(gap)]
    return kap(u)/2,2-u,kap(u)/2,[u,u-1,u-2,kap(u)]
