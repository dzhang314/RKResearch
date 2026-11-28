"""Propose exact source factor cover of the rational actual silent fourth."""
from literal4_projection import projections
from literal4_outer import image
from star4_guarded_fibers import modQ
from flint import fmpz_poly,fmpq_poly,nmod_poly
from pathlib import Path
from functools import lru_cache

@lru_cache(None)
def aux():
    J={}
    for l in Path('literal4-aux-factors.txt').read_text().splitlines():
        k,e,*A=l.split();A=tuple(map(int,A));e=int(e)
        if A[-1]<0:A=tuple(-x for x in A)
        J.setdefault(A,[]).append((k,e))
    return [(fmpz_poly(list(A)),l) for A,l in J.items()]

def proposal(p=65537):
    R=image(*projections(),p)
    h=next(i for i,v in enumerate(R) if v)
    F=nmod_poly(R[h:],p);F*=pow(int(F.leading_coefficient()),-1,p)
    M=F;ans=[]
    for P,l in aux():
        E=fmpq_poly(P);E=E*(1/E[E.degree()])
        try:A=modQ(E,p)
        except (ArithmeticError,ValueError):continue
        e=0;m=F
        while m and not m%A:m//=A;e+=1
        d=A.gcd(F).degree()
        if d and not e:print('partial modular guard proposal',P.degree(),l,d,flush=True)
        if e:
            print('full literal-fourth source proposal',P.degree(),l,e,flush=True)
            ans.append((P,l,e))
            for _ in range(e):
                if M%A:break
                M=M//A
    print('provisional exact cover quotient degree',M.degree(),[(q.degree(),e) for q,e in M.factor()[1]],flush=True)
    assert M.degree()==4076
    assert sorted((P.degree(),e) for P,l,e in ans)==[
        (3,10),(3,24),(5,3),(7,1),(9,42),(21,108),(45,1),(46,3)]
    return ans,M

def main():
    Q,M=proposal()
    Path('literal4-cover-plan.txt').write_text('\n'.join(
        str(e)+' '+str(l)+' '+' '.join(map(str,P)) for P,l,e in Q))

if __name__=='__main__':main()
