#!/usr/bin/env python3
"""Exact audit of the multi-clock remainder system and the joint floor."""
from fractions import Fraction
from random import Random


def field(ell):
    if ell:
        return lambda a: a % ell, lambda a: pow(a % ell, -1, ell)
    return Fraction, lambda a: Fraction(1, a)


def rank(mat, ell):
    norm, inv = field(ell)
    a = [list(r) for r in mat]
    r = 0
    for c in range(len(a[0])):
        j = next((j for j in range(r, len(a)) if a[j][c]), None)
        if j is None:
            continue
        a[r], a[j] = a[j], a[r]
        rinv = inv(a[r][c])
        for j in range(r+1, len(a)):
            t = norm(a[j][c] * rinv)
            if t:
                a[j] = [norm(x-t*y) for x,y in zip(a[j],a[r])]
        r += 1
    return r


def eval_poly(P, x, norm):
    acc = norm(0)
    for a in reversed(P):
        acc = norm(acc*x+a)
    return acc


def keep_width(P, d, norm, inv):
    """Return the remainder of a polynomial modulo a nonzero degree-d mask."""
    def rem(A):
        R = [norm(c) for c in A] + [norm(0)]*max(0,d-len(A))
        ip = inv(P[-1])
        for k in range(len(R)-1,d-1,-1):
            fac = norm(R[k]*ip)
            for i,p in enumerate(P):
                j = k-d+i
                R[j] = norm(R[j]-fac*p)
        return R[:d]
    return rem


def monic_pair(n, ell):
    norm, inv = field(ell)
    one, zero, half = norm(1), norm(0), inv(2)
    prev, cur = [one], [norm(-half),one]
    for j in range(1,n):
        # The largest integer factor needed is 2*j+1, not 4*j*j-1.
        beta = norm(j*j*inv(4)*inv(2*j-1)*inv(2*j+1))
        new = [zero]*(j+2)
        for i,a in enumerate(cur):
            new[i] = norm(new[i]-half*a)
            new[i+1] = a
        for i,b in enumerate(prev):
            new[i] = norm(new[i]-beta*b)
        prev,cur = cur,new
    return cur,prev


def mask_at_sites(sites, ell):
    norm,_ = field(ell)
    poly = [norm(1)]
    for x in sites:
        new = [norm(0)]*(len(poly)+1)
        for i,p in enumerate(poly):
            new[i] = norm(new[i]-x*p)
            new[i+1] = p
        poly = new
    return poly


def square_and_remainder(P, w, ell, sites=None):
    norm,inv = field(ell)
    d,t,h = len(P)-1,(len(P)-1)//2,len(P)//2
    assert not ell or d+2*w-1 < ell
    A,B = monic_pair(w+t,ell)
    moments = [norm(sum(c*inv(j+k+1) for k,c in enumerate(P))) for j in range(2*w-1)]
    G = [[moments[i+j] for j in range(w)] for i in range(w)]
    r = rank(G,ell)
    rem = keep_width(P,d,norm,inv)
    col = [rem([0]*k+poly) for poly,b in ((A,h),(B,t)) for k in range(b)]
    rr = rank(list(zip(*col)),ell)
    assert w-r == d-rr <= min(w,h)
    if sites is not None:
        av = [eval_poly(A,x,norm) for x in sites]
        bv = [eval_poly(B,x,norm) for x in sites]
        site_rows = [
            [norm(a*x**j) for j in range(h)] + [norm(b*x**j) for j in range(t)]
            for x,a,b in zip(sites,av,bv)
        ]
        assert rank(site_rows,ell) == rr
        assert all(a or b for a,b in zip(av,bv))
        if d%2:
            assert (w-r == h) == (not any(av))
        else:
            assert (w-r == h) == (rank([av,bv],ell)==1)
    return r


def full_floor(m, z):
    if m<=0:
        return 0
    if 2*z>=m:
        return (m+1)//2
    u = m-2*z
    a=(u+1)//2
    return z+((a*a+1)//2 if u%2 else a*(a+1)//2)


def saturation_capacity(d,a):
    if d%2:
        return (a+d)//(d+1)
    return 2*(a//(d+1))+min(2,a%(d+1))


def clusters_ok(d,sats):
    if d%2:
        return all(j-i>=d+1 for i,j in zip(sats,sats[1:]))
    gaps = [j-i for i,j in zip(sats,sats[1:])]
    return all(g==1 or g>=d for g in gaps) and all(
        not (g==h==1) for g,h in zip(gaps,gaps[1:])
    )


def lower_formula(p,d,z):
    h=(d+1)//2
    u=p-d-2*h-2*z
    if u<=0:
        return 0
    a=(u+1)//2
    U=a-saturation_capacity(d,a)
    total=(u+1)**2//4+2*U-int(u%2 and U>0)
    return z+(total+1)//2


def grade_census(p,d,z,credits):
    m=p-d
    ranks=[]
    for r in range(m):
        w=1+min(r,m-1-r)
        ranks.append(credits[w-1]+(max(0,ranks[r-2]-z) if r>=2 else 0))
    return max(ranks)


def main():
    rng=Random(1729)
    width_check=joint_check=rem_check=0
    for ell in (0,5,7,11,13,17,23,31,43):
        norm,_=field(ell)
        for p in range(2,min(23,ell) if ell else 23):
            pool=range(1,ell) if ell else [Fraction(a,7) for a in range(-12,15) if a]
            for d in range(1,min(6,p-1)+1):
                for k in range(4):
                    xs=rng.sample(pool,d)
                    P=mask_at_sites(xs,ell)
                    credits=[]
                    for w in range(1,(p-d+1)//2+1):
                        credits.append(square_and_remainder(P,w,ell,xs))
                        width_check+=1
                    assert credits==sorted(credits)
                    sats=[w for w,r in enumerate(credits,1) if w-r==(d+1)//2]
                    assert clusters_ok(d,sats)
                    if k==0:
                        # Include arbitrary and repeated-factor masks in the non-ordered check.
                        Q=[norm(rng.randrange(-5,6)) for _ in range(d)]+[norm(1)]
                        for w in range(1,(p-d+1)//2+1):
                            square_and_remainder(Q,w,ell)
                            rem_check+=1
                    for z in range(len(credits)+1):
                        assert grade_census(p,d,z,credits)>=lower_formula(p,d,z)
                        if d%2==p%2==0 and p>=2*d+2*z+6:
                            assert lower_formula(p,d,z)>full_floor(p-2*d,z)
                        joint_check+=1
    capacity_check=0
    for d in range(1,11):
        for a in range(1,12):
            mx=-1
            for mask in range(1<<a):
                sats=[i+1 for i in range(a) if (mask>>i)&1]
                if clusters_ok(d,sats):
                    mx=max(mx,len(sats))
            assert mx==saturation_capacity(d,a)
            capacity_check+=1

    P=[Fraction(1,10),Fraction(-1),Fraction(1)]
    assert square_and_remainder(P,3,0)==2
    assert square_and_remainder([10,-1,1],3,11,(4,8))==2
    cases=[(8,2,0,3,3),(10,2,0,6,7),(12,2,1,7,8),
           (14,3,0,10,11),(20,4,0,21,24),(20,4,2,12,14)]
    for p,d,z,old,new in cases:
        assert full_floor(p-2*d,z)==old and lower_formula(p,d,z)==new
    print(f"{width_check:,} split-width and {rem_check:,} arbitrary-mask checks; "
          f"{joint_check:,} joint floors; {capacity_check} exact packing maxima.")
    print("Exact width witness: rank 2 over the rational moments and F11; "
          "field-uniform two-clock order-10 cut: 7 vs coarse 6.")


if __name__=='__main__':
    main()
