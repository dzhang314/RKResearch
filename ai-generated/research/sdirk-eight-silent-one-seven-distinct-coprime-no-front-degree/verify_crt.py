"""Independent coefficient-scale and degree checks for the exact CRT output."""
from exact_crt import *
from infinity_certificate import run
from reduced_projection import reduced
from shared_silent8_projection import red_e

def check(f,i,A):
 data,sc=packed(f,i)
 R,Phi,J,dp,dj=inputs(f,i);m,n=len(J)-1,len(Phi)-1;D=3*m+27
 dr,dp,dj=sc
 scale=dr**D * dp**(5*m) * dj**(5*n)
 h,k,l,e=run(f,i,1)
 c=R[-1].lc()**D*k/(l**e)
 assert A.lc()==scale*c
 assert A.degree()==h+R[-1].degree()*D
 p,t=1103,161
 assert red_e(A,p,t)==reduced(f,i,p,t)*(scale%p)
 print('exact CRT degree/coefficient cross-check:',f,i,A.degree(),flush=True)
 return True

if __name__=='__main__':
 for f,i in ((True,1),(False,0),(False,1)):
  A=rec(f,i)
  assert check(f,i,A)
