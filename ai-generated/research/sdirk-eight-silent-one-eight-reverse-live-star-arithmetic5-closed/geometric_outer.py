"""Pinned optional arithmetic backend; pure resultants remain fallback."""
from pathlib import Path
from tempfile import TemporaryDirectory
from functools import lru_cache
import ctypes,flint,os,subprocess
from shutil import which

@lru_cache(None)
def compiler():
    if os.environ.get('RK_DISABLE_FAST_CRT')=='1':return None
    if str(flint.__FLINT_VERSION__)!='3.6.0' or ctypes.sizeof(ctypes.c_ulong)!=8:
        return None
    so=list((Path(flint.__file__).resolve().parent.parent/'python_flint.libs').glob('libflint-*.so.*'))
    if not which('cc') or len(so)!=1:return None
    lib=so[0];tmp=TemporaryDirectory(prefix='rk-geometric-')
    out=Path(tmp.name)/'rk_geometric.so'
    src=Path(__file__).with_name('geometric_outer.c')
    try:
        subprocess.run(['cc','-std=c11','-O3','-fPIC','-shared',str(src),str(lib),
                        '-Wl,-rpath,'+str(lib.parent),'-o',str(out)],check=True)
        F=ctypes.CDLL(str(out)).interpolate_geometric
    except (subprocess.CalledProcessError,OSError,AttributeError):
        tmp.cleanup()
        return None
    z,P,L=ctypes.c_ulong,ctypes.POINTER(ctypes.c_ulong),ctypes.c_long
    F.argtypes=[z,P,L,L,P,L,L,P,z]
    F.restype=ctypes.c_int
    return F,tmp

def img(A,B,p,mode=3):
    R=compiler()
    if R is None:return None
    f,_=R;n=ctypes.c_ulong
    xs=[]
    G,S=A.degrees();H,T=B.degrees()
    for P,D,E in [(A,G,S),(B,H,T)]:
        Z=(n*((D+1)*(E+1)))()
        for (i,j),c in P.to_dict().items():Z[j*(D+1)+i]=int(c)%p
        if not any(Z[E*(D+1)+i] for i in range(D+1)):return None
        xs.append(Z)
    U=(n*(G*T+H*S+1))()
    if f(p,xs[0],G,S,xs[1],H,T,U,mode):return None
    return list(U)
