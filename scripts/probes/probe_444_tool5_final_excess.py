import sys; sys.path.insert(0,'/tmp/tool5')
import depth_fft_graded as dff, char0_baseline as c0
import sympy, time

def excess_profile(n,p,pr,twor):
    cp=dff.depth_profile_distinct_fast(n,p,pr,twor)
    c =c0.char0_zero_sum_ordered(n,twor)
    alld=sorted(set(cp)|set(c))
    eb={dd: cp.get(dd,0)-c.get(dd,0) for dd in alld}
    nz={k:v for k,v in eb.items() if v!=0}
    return nz, sum(cp.values()), sum(c.values()), cp, c

def run(n, p, pr, label, rmax):
    print(f"==== n={n} {label} p={p} ====", flush=True)
    print(f"{'r':>2} {'maxDepth':>8} {'D_engaged':>9} {'totExc':>16}  excess-by-distinct-value-depth", flush=True)
    for twor in range(4, 2*rmax+1, 2):
        r=twor//2; t=time.time()
        nz,ecp,ec0,_,_=excess_profile(n,p,pr,twor)
        engaged=sorted(nz.keys())
        md = max(engaged) if engaged else 0
        print(f"{r:>2} {md:>8} {len(engaged):>9} {ecp-ec0:>16}  {nz}   (t={time.time()-t:.1f}s)", flush=True)

if __name__=="__main__":
    # n=16 Fermat full
    n=16;p=65537;pr=int(sympy.primitive_root(p))
    run(n,p,pr,"FERMAT(v2=16)",7)
    # n=32 structured + generic
    n=32
    for p in [1146881, 929057]:
        v=p-1;v2=0
        while v%2==0: v//=2;v2+=1
        pr=int(sympy.primitive_root(p))
        run(n,p,pr,f"v2={v2}",6)
