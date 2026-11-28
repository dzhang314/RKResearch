#!/usr/bin/env python3
"""Exact scalar-grid arithmetic for the two qualified DIRK12/15 branches."""
from fractions import Fraction as F
from functools import reduce
from math import comb
from operator import mul


def prod(xs):
    return reduce(mul,xs,1)


def pmul(a,b):
    c=[0]*(len(a)+len(b)-1)
    for i,u in enumerate(a):
        for j,v in enumerate(b):
            c[i+j]+=u*v
    return c


def hull(xs):
    return reduce(pmul,([-x,1] for x in xs),[1])


def integ(p,u=1):
    return sum(F(1,i+1)*v*u**(i+1) for i,v in enumerate(p))


def diff_lag(xs,ys):
    return sum(v/prod(x-z for j,z in enumerate(xs) if i!=j)
               for i,(x,v) in enumerate(zip(xs,ys)))


def lagrange(xs,ys,u):
    return sum(v*prod((u-z)/(x-z) for j,z in enumerate(xs) if i!=j)
               for i,(x,v) in enumerate(zip(xs,ys)))


def scalar_moments(fixed,maxdeg=4):
    p=hull(fixed)
    return [integ([0]*j+p) for j in range(maxdeg+1)]


def derivative_hull(fixed,node):
    return prod(node-x for x in fixed if x!=node)


def aggregate_weights(nodes):
    return {s: integ(hull([t for t in nodes if t!=s]))/derivative_hull(nodes,s)
            for s in nodes}


def leg_deriv(j,x):
    return sum(k*(-1)**(j-k)*comb(j,k)*comb(j+k,k)*x**(k-1)
               for k in range(1,j+1))


def exact_rref(mat, rhs):
    """Square guarded solve; no tolerance-based pivots."""
    arr=[list(row)+[b] for row,b in zip(mat,rhs)]
    for j in range(len(arr)):
        i=next(i for i in range(j,len(arr)) if arr[i][j]!=0)
        arr[j],arr[i]=arr[i],arr[j]
        v=arr[j][j]
        arr[j]=[x/v for x in arr[j]]
        for i in range(len(arr)):
            if i!=j:
                v=arr[i][j]
                arr[i]=[x-v*y for x,y in zip(arr[i],arr[j])]
    return [r[-1] for r in arr]


def reverse_seed(r):
    den=r*r-4*r+1
    w5=5*r*r-14*r+5
    t=-r*(r+1)/den
    g=-r*r*(r-2)/(6*(2*r-1))
    h10=-r*r*(r-2)*(r+1)*w5/(6*den**3)
    ell=3*(r-1)*(r-2)
    k=(r-F(1,2))/ell
    hv=r**3/(36*(r-1))
    h9=-r**3*(r+1)**2*(2*r-1)*w5/(36*(r-1)*den**4)
    return t,g,h10,ell,k,hv,h9


def reverse_hull_from_moments(m,chart,duplicate0=False):
    """Unique unordered cubic, as (d+v,dv,u), over the forward field.

    No root extraction or division by the potentially zero m0 in the
    nine-site duplicate-terminal branch.
    """
    shift=1 if chart==9 and duplicate0 else 0
    n=m[shift:shift+4]
    assert len(n)==4 and all(v!=0 for v in n)
    n0,n1,n2,n3=n
    q=n0*n2/(n1*n1)
    h=3*n1/(2*n0)
    lam=4*q/(9-4*q)
    s,p,u=h*lam,h*h*lam*lam/(lam+4),-h*lam/(lam-2)
    cs=[(3*n1*n1-n0*n2)*n3-2*n1*n2*n2]
    if not shift:
        n4=m[4]
        cs.append(2*(9*n1*n1-4*n0*n2)*n2*n4-5*(3*n1*n1-n0*n2)*n3*n3)
    else:
        a,b,c,d=m[:4]
        cs.append(3*a*d*c**3-b*(4*b*d-3*c*c)*(5*c*c-2*b*d))
    return (s,p,u),q,cs


def card_taps(nodes,at,low,high=()):
    """Actual nonzero-source aggregate taps from scalar defect inputs.

    Errors are in input degree two through four, as listed. Both zero
    actors and ghosts are absent from these positive-degree reads.
    """
    ans=[]
    for i,q in enumerate(nodes):
        oth=[v for j,v in enumerate(nodes) if i!=j]
        poly=hull([0]+oth)
        den=q*prod(q-v for v in oth)
        vals=[low]+list(high)
        ans.append((integ(poly,at)+sum(poly[j+2]*v for j,v in enumerate(vals)))/den)
    return ans


def third_and_next_ratios(chart,r,w,hw=None):
    """Normalized nodes and exact E6/G,Z/G (or (E6-2G)/H,Z/H).

    When w is nonzero, hw is the normalized barycentric-head amplitude
    at that singleton. A repeated endpoint never supplies hw.
    """
    t,g,h10,L,k,hv,h9=reverse_seed(r)
    sigma=F(1,6);one=F(1)
    if chart==10:
        assert w!=0 and hw is not None and hw!=0
        p1=r*r*(r+1)/(3*(2*r-1))
        pr=r*(4*r-5)/(6*(2*r-1))
        phi=lambda z:r+1+(F(1,2)-r)*z
        chi=lambda z:lagrange([0,one,r],
            [r*r+r+1,F(9,5),(p1+r**4*pr-r**5/5)/g],z)
        T=card_taps([one,r,t],t,h10,[phi(t)*h10])
        U=card_taps([one,r,t,w],w,hw,[phi(w)*hw,chi(w)*hw])
        e=[F(2),(p1+r**5*pr-r**6/6)/g,(r**4-1)/(r-1),
           (sum(v*q**5 for v,q in zip(T,[one,r,t]))-t**6/6)/h10,
           (sum(v*q**5 for v,q in zip(U,[one,r,t,w]))-w**6/6)/hw]
        z=[F(1,2),(sigma*p1+r*r*g*pr)/g,(r*g-sigma)/(r-1),
           sum(v*q*q*c for v,q,c in zip(T,[one,r,t],[sigma,g,h10]))/h10,
           sum(v*q*q*c for v,q,c in zip(U,[one,r,t,w],[sigma,g,h10,hw]))/hw]
        return [one,r,0,t,w],e,z,T[-1]
    assert chart==9
    p1=r**3/(6*(r-1))
    pr=r/2-p1/r
    a2=F(1,2)+1/(6*(r-1))+k
    phi= lambda z:lagrange([one,r],
        [(r*r+r-F(4,5))/k,(p1+r**4*pr-r**5/5)/hv],z)
    psi1=a2+hv/(r*(r-1)*k)
    T=card_taps([one,r,t],t,0,[L*h9])
    # The literal return split obeys delta*T_d2=h-sigma*T_d.
    e=[(r**3+r*r+r-1)/k,(p1+r**5*pr-r**6/6)/hv,
       (sum(v*q**5 for v,q in zip(T,[one,r,t]))-t**6/6)/h9]
    z=[psi1+hv/(r*k),r*pr,
       (k*(h9-sigma*T[0])+r*hv*T[1]+t*h9*T[2])/h9]
    if w==0:
        xs=[one,r,t]
        A=[L/(u*prod(u-v for j,v in enumerate(xs) if i!=j)) for i,u in enumerate(xs)]
        e.append(sum(a*q**5 for a,q in zip(A,xs)))
        z.append(k*(1-sigma*A[0])+r*hv*A[1]+t*h9*A[2])
    else:
        assert hw is not None and hw!=0
        U=card_taps([one,r,t,w],w,0,[L*hw,phi(w)*hw])
        e.append((sum(v*q**5 for v,q in zip(U,[one,r,t,w]))-w**6/6)/hw)
        z.append((k*(hw-sigma*U[0])+r*hv*U[1]+t*h9*U[2]+w*hw*U[3])/hw)
    return [one,r,t,w],e,z,T[-1]

def forward_pair(a,x,y,leg_root):
    """Two coefficients proportional to the actual (alpha,gamma)."""
    D=2*x*y-x-3*y*y+2*y
    if not leg_root:
        R=lambda s:s*leg_deriv(6,a*s)/leg_deriv(6,a)
        G=lambda j,s:s*leg_deriv(j,a*s)-R(s)*leg_deriv(j,a)
        theta=-y**3*(y-1)**3*(3*x*x-2*x*y-2*x+y)/(x**3*(x-1)**3*D)
        return tuple(exact_rref([[G(j,s) for j in [5,7]] for s in [x,y]],[1,theta]))
    db=5*x*x-5*x+1
    e=-(7*x*x-7*x+2)/1260
    rb=x**3*(15*x**3-49*x*x+55*x-20)/db
    f=hull([0,1,x,y])
    fst,sec=integ(f),integ([0]+f)
    hi=integ([0,0]+f)-e
    ry,_=exact_rref([[fst,sec],[sec,hi]],[integ(f,y),integ([0]+f,y)])
    rr=exact_rref([[s*leg_deriv(j,a*s) for j in [5,6,7]] for s in [1,x,y]],[1,rb,ry])
    return rr[0],rr[2]


def mixed_grid(a,x,y,t_f,f_f,d,v,chart,leg_root=False):
    """Exact necessary residuals for a specified ordered candidate grid.

    a,ax,ay,a*t_f,a*f_f are the ordinary first-five distinct nonzero
    live clocks. d,v are the first two reflected distinct nonzero live
    clocks, and u is forced by the literal early reverse condition.
    Rational examples use Fraction. An algebraic field input must
    implement exact arithmetic, equality, and hash; no floats are used.
    """
    assert (leg_deriv(6,a)==0)==leg_root
    r=v/d
    t,g,h10,L,k,hv,h9=reverse_seed(r)
    u=d*t
    w=1-a*f_f
    known=[F(0),F(1)]
    early=[1-a*j for j in [1,x,y,t_f,f_f]]
    assert all(s not in early[:i] and s!=1 for i,s in enumerate(early))
    for s in early:
        if s not in known:known.append(s)
    duplicate0=chart==10 or any(s==0 for s in early)
    if chart==9:
        assert len(known)==(6 if duplicate0 else 7)
    else:
        assert chart==10 and len(known)==7 and all(s!=0 for s in early)
    sites=known+[d,v,u]
    assert all(z not in sites[:i] for i,z in enumerate(sites))
    D=sites if duplicate0 else [z for z in sites if z!=0]
    assert len(D)==chart
    B=aggregate_weights(sites)
    assert all(B[s]!=0 for s in (d,v,u))
    ctests=[]
    for kdeg in range(len(sites),12):
        ctests.append(sum(B[j]*j**kdeg for j in sites)-F(1,kdeg+1))
    m=scalar_moments(known)
    (sv,pp,uu),q,rtests=reverse_hull_from_moments(m,chart,duplicate0)
    supp=[d+v-sv,d*v-pp,u-uu]
    Hd=lambda s:derivative_hull(D,s)
    if chart==10:
        rho=B[d]*d**3*Hd(d)/6
        am=[B[v]*d**3*g*Hd(v)-rho,B[u]*d**3*h10*Hd(u)-rho]
        hw=rho/(Hd(w)*B[w]*d**3)
    else:
        rho=B[v]*d**4*hv*Hd(v)
        am=[-k*B[d]*d**4*Hd(d)/6-rho,B[u]*d**4*h9*Hd(u)-rho]
        hw=None if w==0 else rho/(Hd(w)*B[w]*d**4)
    nodes,E,Z,third_diag=third_and_next_ratios(chart,r,w/d,hw)
    ez,zz=diff_lag(nodes,E),diff_lag(nodes,Z)
    alpha,gamma=forward_pair(a,x,y,leg_root)
    eps12=sum(B[s]*(1-s)**12 for s in sites)-F(1,13)
    mixed=alpha*zz+462*24024*gamma*(rho*ez-eps12*zz)
    return dict(quadrature=ctests,scale_only=rtests,support=supp,amplitudes=am,
                third_diagonal=third_diag,reverse_Z_nonzero=zz,
                ordinary_gamma_nonzero=gamma,epsilon12=eps12,mixed=mixed,
                reverse_ratio=ez/zz if zz!=0 else None)
