#!/usr/bin/env python3
"""Exact late-six suffix certificate in finite-free monic quotient bases."""
from argparse import ArgumentParser
from pathlib import Path
from runpy import run_path

here = Path(__file__).resolve().parent
parser = ArgumentParser()
parser.add_argument("--arithmetic", type=Path,
    default=here.parent / "dirk11-thirteen-fourth-clean" / "replay_mod101.py")
parser.add_argument("--prime", type=int, default=101)
args = parser.parse_args()
mod = run_path(str(args.arithmetic))
F, Q, cast, J4, J5, receipt, ev, dot, lag, quad, resultant = (
    mod[name] for name in ("F", "Q", "cast", "J4", "J5", "receipt", "ev",
                           "dot", "lag", "quad", "resultant")
)


def two_taps(r, s, m0, m1):
    """Exponents 0,1 at distinct donors r,s, in that order."""
    return [(s*m0-m1)/(s-r), (m1-r*m0)/(s-r)]


def three_taps(R, m):
    """Exponents 0,1,2 by the Lagrange dual, no individual node division."""
    taps = []
    for j, r in enumerate(R):
        s, t = [h for i, h in enumerate(R) if i != j]
        taps.append((m[2]-(s+t)*m[1]+s*t*m[0])/((r-s)*(r-t)))
    return taps


def positive_quad(u, v, pu, pv):
    """Interpolate at u,v in the basis X,X^2."""
    beta = (pv/v-pu/u)/(v-u)
    alpha = pu/u-beta*u
    return (lambda s: alpha*s+beta*s*s,
            lambda s: alpha*s*s/2+beta*s**3/3)


def geometry(u, v, w):
    r = [u,v,w]
    P = lambda x: x*(x-u)*(x-v)
    K = lambda x: x**4/4-(u+v)*x**3/3+u*v*x*x/2
    J = lambda x: x**5/5-(u+v)*x**4/4+u*v*x**3/3
    L = lambda x: x**6/6-(u+v)*x**5/5+u*v*x**4/4
    h = lambda x: x*J4(x)
    lam = lambda x: lag(x, [u,v], [J(u)/K(u), J(v)/K(v)])
    eta = (w-lam(u))*(v-u)/(lam(v)-lam(u))+u
    S, U = positive_quad(u,v,K(u),K(v))
    S1,V = positive_quad(u,v,u*K(u),v*K(v))
    mu = lambda x: lag(x,[u,v],[U(u)/K(u),U(v)/K(v)])
    # Retain unit checks for the handoff geometry at the third regular.
    K(w).inv()
    assert lam(w)*K(w) == J(w)
    assert mu(w)*K(w) == U(w)
    f = lambda x,q: (q-S(x))/P(x)
    e = lambda x,q: (x*q-S1(x))/P(x)
    q0 = lambda x: lag(x,r,[-L(s)/K(s) for s in r])
    t0 = lambda x: lag(x,r,[V(s)/K(s) for s in r])
    h0 = lambda x: lag(x,r,[h(s)/K(s) for s in r])
    return locals()


def fourth(u,v,w,a):
    g = geometry(u,v,w)
    P,K,J,L,lam,eta,U,V,mu,f,e,q0,t0,h0,h = (
        g[s] for s in ("P","K","J","L","lam","eta","U","V","mu","f","e","q0","t0","h0","h")
    )
    qa0 = K(w)
    taps = lambda q: two_taps(w, a, K(a)-q, J(a)-lam(a)*q)
    donors=[w,a]
    chi = (q0(eta)+w*w)/h0(eta)
    theta = (t0(eta)+e(w,qa0)-eta*(eta-w))/h0(eta)
    R = lambda x: q0(x)-chi*h0(x)
    T = lambda x: t0(x)-theta*h0(x)
    sc = lambda q: dot(taps(q),[s*s for s in donors])-L(a)-R(a)*q-chi*h(a)
    c = sc(a*0)
    qa = -c/(sc(a*0+1)-c)
    opt = dot(taps(qa),[e(s,q)-eta*f(s,q) for s,q in zip(donors,[qa0,qa])])
    opt -= (T(a)-eta*mu(a))*qa+theta*h(a)-V(a)+eta*U(a)
    plain = lambda q: dot(taps(q),[f(w,qa0),f(a,q)])-mu(a)*q+U(a)
    return quad(plain,a), opt


def fifth(u,v,w,a,b,qa):
    g = geometry(u,v,w)
    P,K,J,L,lam,U,V,mu,f,e,q0,t0,h0,h = (
        g[s] for s in ("P","K","J","L","lam","U","V","mu","f","e","q0","t0","h0","h")
    )
    qw = K(w)
    taps = two_taps(w,a,K(a)-qa,J(a)-lam(a)*qa)
    den = h(a)-h0(a)*qa
    chi = (dot(taps,[w*w,a*a])-L(a)-q0(a)*qa)/den
    theta = (dot(taps,[e(w,qw),e(a,qa)])+V(a)-t0(a)*qa)/den
    R = lambda x: q0(x)-chi*h0(x)
    T = lambda x: t0(x)-theta*h0(x)
    opt = lambda x: two_taps(w,a,-1,-lam(x))
    g1 = lambda x: dot(opt(x),[w*w,a*a])-R(x)
    g2 = lambda x: dot(opt(x),[e(w,qw)-x*f(w,qw),e(a,qa)-x*f(a,qa)])-T(x)+x*mu(x)
    optres = resultant(quad(g1,u),quad(g2,u))
    taps5 = lambda q: three_taps([w,a,b],[K(b)-q,J(b)-lam(b)*q,L(b)+R(b)*q+chi*h(b)])
    p1 = lambda q: dot(taps5(q),[f(w,qw),f(a,qa),f(b,q)])-mu(b)*q+U(b)
    p2 = lambda q: dot(taps5(q),[e(w,qw),e(a,qa),e(b,q)])-T(b)*q-theta*h(b)+V(b)
    return optres, resultant(quad(p1,u),quad(p2,u))


factor,(c0,c1),j5 = receipt()
prime = args.prime
T=F.start(prime,factor); u=-ev(c0,T)/ev(c1,T); v=u*T; w=u*T*(1+T)/(4*T-1-T*T)
la=-J5(u)/J4(u); summ=-(F(j5.nth(4))+42*la)/132-u-v-w
prod=(F(j5.nth(3))-84*la)/132-u*v-u*w-v*w-(u+v+w)*summ
print(f"Clock quotient: rank 60, base divisions certified modulo {prime}", flush=True)
a=Q((summ,prod),F(0),F(1)); u,v,w,b=cast(a,u,v,w,summ-a)
poly, opt=fourth(u,v,w,a); opt.inv()
print("Fourth clock quotient: rank 120, optional-fourth contradiction is a unit", flush=True)
p2,p1,p0=poly
qa=Q((-p1/p2,p0/p2),a*0,a*0+1)
rg,rn=fifth(*cast(qa,u,v,w,a,b),qa)
rg.inv()
print("Fourth tap quotient: rank 240, optional-fifth resultant is a unit", flush=True)
rn.inv()
print("Fourth tap quotient: rank 240, consecutive-fifth resultant is a unit", flush=True)
print("Checked primitive residue inverses:",F.inverse_count)
