"""Rank-loss fifth hole: full sixth/seventh ordinary assignment not needed."""
from h5_rank import rank_models
from reverse_live_quartic import gap
from aq_modular import ev,sc,add,mul,nodal,det,mon
from arith_ordinary_reconstruction import extend,factor_deriv
from gauss_separate import span_unit
from itertools import combinations

def W(V,P,hr,be,r):
    return [sum((P[j]*(hr/(j-i)-be*r**(j-i-1)) for j in range(i+1,len(P))),V(0)) for i in range(len(P)-1)]

def signed_rows(V,H,be,r,known):
    E=nodal(known);Ed=factor_deriv(E,V)
    hr=ev(H,r);Wh=W(V,H,hr,be,r)
    cols=[]
    for j in range(3):
        D=[V(0)]*j+E
        C=add(mul(H,W(V,D,hr,be,r)),sc(mul(D,Wh),-1))
        assert len(C)<=4
        C+=[V(0)]*(4-len(C))
        cols.append(C[1:])
    return list(map(list,zip(*cols))),Ed

def rank_mode(front,rear,p,t):
    cnt=0
    for V,dat,H,degree in rank_models(front,p,t):
        g,a,b,q,r,A,C,s,m,ha,hb,hq,den,alp,bet=dat
        x=1-g
        N=gap(V,g,x,rear,H)
        assert len(N)==(5 if rear is None else (3 if rear else 6))
        U,u,inc=extend(V,mon(N))
        g,a,b,q,r,x,bet=map(inc,(g,a,b,q,r,x,bet))
        H=list(map(inc,H))
        k=1+2*u-u*u
        c=x-g*u
        d=None if rear is None else x-g*(2-u if rear else 2*u)
        slots=[8] if rear is None else (2,3,4,6)
        for slot in slots:
            known=[a,b,q,x,c]
            if slot<=4:
                z=known.pop(slot-2)
                G=(x-z)*ev(H,c)-k*(c-z)*ev(H,x)
                G.inv()
                print('rank-loss literal tail alone',front,rear,slot,degree,flush=True)
                continue
            rows,Ed=signed_rows(U,H,bet,r,known)
            Ac=ev(H,c)*ev(Ed,c);Ax=ev(H,x)*ev(Ed,x)
            row=[Ac*c**j-Ax*x**j for j in range(3)]
            rows.append(row)
            if slot==6:rows.append([U(1),d,d*d])
            gates=[det(list(I)) for I in combinations(rows,3)]
            span_unit(U,*gates)
            print('rank-loss signed terminal unit',front,rear,slot,degree,flush=True)
        cnt+=1
    return cnt
