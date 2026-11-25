#!/usr/bin/env python3
"""Recover the true integer univariate outer projections, with exact degree bounds.
Use SymPy's exact subresultant routine only for univariate integer arithmetic.
An independent fixed-size Bareiss implementation checks sample fibers and
the archived complete mod-1009 coefficient vector verifies every coefficient there.
"""
from pathlib import Path
import json,sys
from math import gcd
from functools import reduce
from sympy.polys.euclidtools import dup_resultant
from sympy.polys.domains import ZZ
sys.path.insert(0,sys.argv[1])
from check_pencil_projection import trim,ev,interp,res,CIS,F,J,cubic_pair,quartic_forms,gcd_mod
def fixed(f,g,m,n):
 f=trim(f);g=trim(g);df=len(f)-1;dg=len(g)-1
 if df<m and dg<n:return 0
 if not f or not g:
    return res(f,g,m,n)
 scale=(f[-1]**(n-dg) if df==m else ((-1)**n*g[-1])**(m-df))
 # Always supply the higher degree first and restore the ordered Sylvester sign.
 if df<dg: f,g=g,f;scale*=(-1)**(df*dg)
 return int(dup_resultant(f[::-1],g[::-1],ZZ))*scale
def inn(t,z):
 ft=ev(F,t);jt=ev(J,t);H=[t**k*(J[k]*ft-F[k]*jt) for k in range(7)]
 P=[12*z-15*z*z,60*z*z-24*z-18,-10*(5*z*z+4*z-6),15*(4*z-3)]
 return res(H,P,6,3)
def bi(n,m,val):
 rows=[interp([val(t,z) for t in range(n+1)]) for z in range(m+1)]
 return [interp([row[i] if i<len(row) else 0 for row in rows]) for i in range(n+1)]
def coeffs(d):
 cubic=d['name']=='cubic'
 if cubic:
    btab=bi(33,12,inn)
    def pair(z):return (cubic_pair(z)[0],[ev(a,z) for a in btab])
    m,n,q=5,33,258
 else:
    atab=bi(9,4,lambda t,z:quartic_forms(t,z)[0]);btab=bi(14,9,lambda t,z:quartic_forms(t,z)[2])
    def pair(z):return [ev(a,z) for a in atab],[ev(a,z) for a in btab]
    m,n,q=9,14,137
 vals=[fixed(*pair(z),m,n) for z in range(q+1)]; T=interp(vals)
 for z in (-2,-1,2,3,9):
    f,g=pair(z)
    assert ev(T,z)==res(f,g,m,n)
 for z in [q+1,q+2,q+10]:assert ev(T,z)==fixed(*pair(z),m,n)
 assert trim([c%1009 for c in T])==d['Tmod']
 cont=reduce(gcd,(abs(a) for a in T));T0=[c//cont for c in T]
 R=d['R'];rc=R[-1];zero=next(i for i,c in enumerate(T0) if c)
 Tp=T0[zero:]
 print(d['name'], 'deg',len(T)-1,'content bits',cont.bit_length(),'origin',zero,'primitive max bits',max(abs(c).bit_length() for c in Tp),flush=True)
 return {'name':d['name'],'T':T,'T_content':cont,'T_origin':zero,'positive_primitive':Tp,'R':R}
if __name__=='__main__':
 data=json.loads((Path(sys.argv[1])/'projection_data.json').read_text())
 dst=Path(sys.argv[2])
 for d in data:
    q=coeffs(d)
    (dst/('exact_'+q['name']+'_outer.json')).write_text(json.dumps(q,separators=(',',':'))+'\n')
    U=q['positive_primitive'];R=q['R'];N=fixed(R,U,len(R)-1,len(U)-1)
    raw=N*q['T_content']**(len(R)-1)*(((-1)**(len(R)-1))*R[0])**q['T_origin']
    (dst/('index_'+q['name']+'.json')).write_text(json.dumps({'primitive_hex':hex(N),'raw_hex':hex(raw),'R_lc':R[-1],'T_origin':q['T_origin'],'T_content':q['T_content']},separators=(',',':'))+'\n')
