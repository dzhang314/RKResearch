"""Necessary rank-two four-port leading causal test on the paid ten-site mesh."""
from fractions import Fraction as Q
from math import isqrt,lcm,gcd
from itertools import combinations
import sys
from poly_utils import hull,integ,mul,scale,val,interp,quad,product,add,dot

X=[Q(j,6) for j in range(-3,7) if j]
proper=[x for x in X if x!=1]
W=dict(zip([Q(0)]+X,quad([Q(0)]+X,Q(1))))
P9={x:product(x-y for y in X if y!=x) for x in X}
P8={x:product(x-y for y in proper if y!=x) for x in proper}

def lin(f,d):
    v=sum(val(f,z)*z**d/(W[z]*P9[z]*z*P8[z]) for z in proper)
    b=sum(val(f,z)*z**(d+1)/(W[z]*P9[z]*z*P8[z]) for z in proper)
    return [v,b]

def prepare(triple):
    F=hull([Q(0)]+list(triple))
    rhs=[integ(F,z)*W[z]*P9[z] for z in triple]
    f0=[Q(0)]*3
    for t,v in zip(interp(triple),rhs):f0=add(f0,scale(t,v))
    G=hull(triple)
    al,be=lin(f0,0),lin(G,0)
    aa,bb=lin(f0,1),lin(G,1)
    eq=[a-b for a,b in zip(mul(al,bb),mul(aa,be))]
    D=lcm(*(a.denominator for a in eq));eq=[int(D*a) for a in eq]
    g=gcd(*eq) or 1; eq=[a//g for a in eq]
    return eq,(al,be,aa,bb)

def projective(eq,data):
    c,b,a=eq
    out=[]
    if a==0:
        out.append((Q(0),Q(1)))
        if b:out.append((Q(1),Q(-c,b)))
        elif not c:return None
    else:
        d=b*b-4*a*c
        if d>=0 and isqrt(d)**2==d:
            out.extend((Q(1),Q(-b+s*isqrt(d),2*a)) for s in [-1,1])
    ok=[]
    for z in set(out):
        al,be,aa,bb=[dot(q,z) for q in data]
        if be:
            if aa*be==al*bb:ok.append((z,-al/be))
        elif bb:
            if not al: ok.append((z,-aa/bb))
        elif not al and not aa:ok.append((z,Q(0)))
    return ok

stats={}
non_squares=[]
split_checks=[]
for u in combinations(proper,3):
    eq,data=prepare(u)
    roots=projective(eq,data)
    a,b,c=eq[2],eq[1],eq[0];disc=b*b-4*a*c
    flag=(len(roots) if roots is not None else -1)
    if disc<0 or isqrt(disc)**2<disc:
        non_squares.append([a,b,c,isqrt(disc) if disc>=0 else 0])
    else:
        assert a
        for sign in (1,-1):
            k=Q(-b+sign*isqrt(disc),2*a)
            A,B,C,D=[dot(f,(Q(1),k)) for f in data]
            if not B and not D:
                assert A and C
                split_checks.append([str(k),str(A),str(C)])
    stats[flag]=stats.get(flag,0)+1
    if flag!=0:print("rational leading gate",u,eq,roots,flush=True)
assert stats=={0:54,1:2} and len(non_squares)==54
assert split_checks==[["-47/71","-54/497","-54/2485"],["-397/31","-270/31","-864/217"]]
print("exact pinned mesh cases:",stats)
print("two extraneous roots with both slopes zero and nonzero constants",split_checks)

# Complete scalar compatibility on the fixed ten-site mesh, assuming
# literal projected ports and C(2) on the reflected nonport subsequence.
from sympy import Matrix
from collections import Counter
H=[0,1,-14,56,-84,42]
def hvec(f):return [val(f,z)/(W[z]*P9[z]) for z in X]
def reduced(triple,orient,r):
    a,b=orient
    U=[Q(0) if z==1 else (a+b*z)/(z*P8[z]) for z in X]
    M=Matrix([[dot(U,hvec([0]*i+[1])) for i in range(4)],
              [dot([z*t for z,t in zip(X,U)],hvec([0]*i+[1])) for i in range(4)]])
    null=[list(map(Q,v)) for v in M.nullspace()]
    assert len(null)==2
    eta0=[val(H,z)-(Q(1,30)/W[Q(1)] if z==1 else 0) for z in X]
    eta1=next(hvec(v) for v in null if Matrix([eta0,hvec(v)]).rank()==2)
    ports=list(triple)+[r]
    vp=[eta1[X.index(z)] for z in ports]
    F1=[Q(0)]*5
    for rj,c in zip(interp([Q(0)]+ports),[Q(0)]+vp):
        F1=add(F1,scale(rj,c))
    F0=hull([Q(0)]+ports)
    V0=[val(F0,z)for z in X]
    V1=[ej-val(F1,z)for ej,z in zip(eta1,X)]
    assert Matrix([V0,V1]).rank()==2
    no=[z for z in proper if z not in ports]
    results=[]
    for last in no:
        E=Q(1)
        ix=X.index(last)
        f=[V0[ix]*v-V1[ix]*u for u,v in zip(V0,V1)]
        ks=[Q(1)]+[z for z in no if z!=last]
        GP=[Q(0)]*4
        for e,z in zip(interp(ks),ks):
            GP=add(GP,scale(e,U[X.index(z)]/W[z]))
        eq=sum(fj*W[z]*(integ(GP,Q(1))-integ(GP,z)) for fj,z in zip(f,X))
        results.append((last,eq))
    return results

histo=Counter()
mixed_data=[]
for u in combinations(proper,3):
    e,ds=prepare(u)
    roots=projective(e,ds)
    if not roots:continue
    for ori,t in roots:
        for r in proper:
            if r in u:continue
            for last,eq in reduced(u,ori,r):
                histo[bool(eq)]+=1
                mixed_data.append(eq.numerator)
                if not eq:print("FULL leading feasibility",u,ori,r,last,flush=True)
assert histo==Counter({True:40})
print("mixed all-taps compatibility count",histo)
if len(sys.argv)==2 and sys.argv[1]=="--emit-core":
    def li(v):return "["+", ".join(map(str,v))+"]"
    def tpl(v):return "("+", ".join(map(str,v))+")"
    print("def nonsquares : List (Int × Int × Int × Nat) := ["+", ".join(map(tpl,non_squares))+"]")
    print("def mixedNumerators : List Int := "+li(mixed_data))
