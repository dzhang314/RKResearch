"""Exact high/high off-diagonal zero R-rank rows."""
from pathlib import Path
import sys
from itertools import combinations

ROOT=Path(__file__).resolve().parent.parent
sys.path.insert(0,str(ROOT/'sdirk-eight-all-dirty-seven-quadratic-both-s-both-two-s-disjoint-hl'))
from projection_hl import F,ip,strip,H,a,b,div_linear
k=lambda u:1+2*u-u*u
D=lambda u:-2+u+4*u*u-u**3
N=lambda u:(1+4*u-4*u*u)*D(u)+4*u*u*(3*u-2)
Z,O=F(),F(1)
h=H/2;mh=1+h
L3=lambda y:(y-h)**3-3*mh*mh*(y-h)/5
L4=lambda y:(y-h)**4-6*mh*mh*(y-h)**2/7+3*mh**4/35
L0=L4(Z)
LA=[L0,-4*h**3+12*mh*mh*h/7,6*h*h-6*mh*mh/7,-4*h,O]
VA=[L3(Z),3*h*h-3*mh*mh/5,-3*h,O,Z]
def frame():
    masks={};guards=[]
    def add(group,xs):
        assert all(xs)
        assert all(not strip(ip(x.d),guards).total_degree() for x in xs),(group,[str(strip(ip(x.d),guards)) for x in xs])
        rows=[ip(x.n) for x in xs]
        masks[group]=rows
        guards.extend(rows)
    add('base',[H,mh,a,H-a])
    u=a/2
    add('front',[u-2,k(u),D(u),N(u),3*u-2])
    fs,fp,p=N(u)/(2*D(u)),k(u)/2,u
    phi=2*fs
    Ns=1+H*(phi-1)/a
    add('b-slope',[Ns])
    br=(2*H-a+H**2*(phi-1)/a)/Ns
    v=br/2
    add('rear',[br,br-4,k(v),D(v),N(v),3*v-2])
    rt,rq,q=N(v)/(2*D(v)),k(v)/2,H-v
    add('offset',[a-br])
    psi=2*rt
    s,t=a,H-br
    add('clocks',[x-y for x,y in combinations((Z,H,p,q,s,t),2)])
    add('known_D_anchors',[L4(p),L4(q)])
    dd=H-a-br
    n=a+br-2*H-H*(phi-1)*(H-br)/a
    M=a+br-2*H-H*(psi-1)*(H-a)/br
    U=H*(H-br)*L4(a)-(H-a)*dd*L0*phi
    V=H*(H-a)*L4(br)-(H-br)*dd*L0*psi
    assert not n
    add('K_scale',[U,V])
    lam=a*phi*V/(br*psi*U)
    partner=strip(ip(M.n),guards)
    Lp,Lq=L4(p),L4(q)
    S=Lp*L3(q)-Lq*L3(p)
    A=(q-p)*Lq*L3(p)-p*S
    ax=(q-p)*Lp*Lq
    X=[ax*VA[i]-A*LA[i]-(S*LA[i-1] if i else Z) for i in range(5)]+[-S]
    m0,m1,m2,m3=div_linear(div_linear(X,p),q)
    # Only actual anchor denominators clear. The additional common scale below is proven nonzero.
    add('graph_coeffs',[m0,m3])
    r2=(fs-(H-a+a*lam)/(2*H))/(a*(a-H))
    r1=(lam-1)/(2*H)-H*r2
    add('curvature',[r2]);R=lambda y:O/2+r1*y+r2*y*y
    assert not (R(s)-fs)
    l1=2*m1-4*m0*r1
    add('graph_slope',[l1])
    E=m2-2*m0*r2-l1*r1
    G=m3-l1*r2
    lin=lambda y:(H-y)*2*lam*L0/H+y*2*L0/H
    K2=(lam*L4(s)/fs-lin(s))/(s*(s-H))
    K=lambda y:lin(y)+K2*y*(y-H)
    assert not (K(t)-L4(t)/rt)
    U_p=fp*(fp-R(p));U_q=rq*(lam*rq-R(q))
    add('off_graph',[U_p,U_q])
    Y=(lam*Lp-fp*K(p))*U_q-(Lq-rq*K(q))*U_p
    equations=[E,G,Y]
    assert all(not strip(ip(x.d),guards).total_degree() for x in equations)
    return [partner,*[strip(ip(x.n),guards) for x in equations]],masks
