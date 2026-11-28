"""Optional LP64 native multipoint finite-field Sylvester evaluation."""
from pathlib import Path
from functools import lru_cache
from tempfile import TemporaryDirectory
import ctypes
import flint
import os
import subprocess
from shutil import which

@lru_cache(None)
def get_compiler():
    if os.environ.get('RK_DISABLE_FAST_CRT')=='1':return None
    parent=Path(flint.__file__).resolve().parent.parent
    libs=list((parent/'python_flint.libs').glob('libflint-*.so.*'))
    if len(libs)!=1 or not which('cc') or ctypes.sizeof(ctypes.c_ulong)!=8:
        return None
    lib=libs[0]
    tmp=TemporaryDirectory(prefix='rk-native-outer-')
    obj=Path(tmp.name)/'rk_outer.so'
    code=Path(__file__).with_name('fast_outer_interpolate.c')
    try:
        subprocess.run(['cc','-std=c11','-O3','-fPIC','-shared',str(code),str(lib),
                    '-Wl,-rpath,'+str(lib.parent),'-o',str(obj)],check=True)
        L=ctypes.CDLL(str(obj))
    except (subprocess.CalledProcessError,OSError):
        tmp.cleanup()
        return None
    sz,block=ctypes.c_long,ctypes.POINTER(ctypes.c_ulong)
    r=L.interpolate_outer
    r.argtypes=[ctypes.c_ulong,block,sz,sz,block,sz,sz,block]
    r.restype=ctypes.c_int
    return r,tmp

def fast_mod_images(U,V,p,z,dimensions):
    item=get_compiler()
    if item is None:return None
    fn,_=item
    g0,s0,g1,s1=dimensions
    cap=g0*s1+g1*s0
    # Preserve both original s-degrees over each split field.
    out=[]
    word=ctypes.c_ulong
    for sg in (z,p-z):
        X=[]
        for (A,B),d,e in zip((U,V),(g0,g1),(s0,s1)):
            arr=(word*((d+1)*(e+1)))()
            for i,j in A.keys()|B.keys():
                assert i<=d and j<=e
                arr[j*(d+1)+i]=(A.get((i,j),0)+sg*B.get((i,j),0))%p
            if not any(arr[e*(d+1)+i] for i in range(d+1)):return None
            X.append(arr)
        R=(word*(cap+1))()
        code=fn(p,X[0],g0,s0,X[1],g1,s1,R)
        assert code==0,code
        out.append(list(R))
    u=pow(2,-1,p);v=pow(2*z,-1,p)
    return [[(a+b)*u%p for a,b in zip(*out)],[(a-b)*v%p for a,b in zip(*out)]]
