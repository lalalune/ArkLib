import sys, itertools, math
import os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from probe_407_excess_lll_setup import is_prime, primitive_nth_root
from probe_407_excess_lll_bruteforce import is_C_trivial
from collections import defaultdict

def pr(*a):
    print(*a, flush=True)

def primes_band(n, lo, count):
    out = []; k = max(1,(lo-1)//n); k0=k
    while len(out)<count and k-k0<5_000_000:
        p=1+k*n
        if is_prime(p): out.append(p)
        k+=1
    return out

def has_balanced_depth(n, p, h, r):
    """exists balanced depth-r relation (r +, r -, all distinct, sum+ = sum- mod p, not C-trivial)?"""
    pows=[pow(h,c,p) for c in range(n)]
    table=defaultdict(list)
    for combo in itertools.combinations(range(n), r):
        s=0
        for c in combo: s+=pows[c]
        table[s%p].append(combo)
    for s, combos in table.items():
        if len(combos)<2: continue
        for i in range(len(combos)):
            for j in range(i+1,len(combos)):
                A,B=combos[i],combos[j]
                if set(A).isdisjoint(B):
                    idxs=list(A)+list(B); signs=[1]*r+[-1]*r
                    if not is_C_trivial(idxs,signs,n):
                        return (idxs,signs)
    return None

if __name__=="__main__":
    pr("=== BALANCED depth-r existence (prize-relevant E_r excess), per prime ===")
    # n: (rmax_balanced) memory-safe: C(n,r) table
    plan=[(16,5),(32,5),(64,4),(128,3),(256,3)]
    for (n,rmax) in plan:
        primes=primes_band(n,n**4,4)+primes_band(n,n**5,2)
        pr(f"\n#### n={n}  (balanced depth searched r=2..{rmax}, i.e. weight up to {2*rmax})")
        for p in primes:
            h=primitive_nth_root(p,n); m=(p-1)//n; log2m=math.ceil(math.log2(m))
            rstar=None; wit=None
            for r in range(2,rmax+1):
                res=has_balanced_depth(n,p,h,r)
                if res is not None:
                    rstar=r; wit=res; break
            if rstar is None:
                pr(f"  p={p} m={m} (ceil log2 m={log2m}): NO balanced excess up to depth {rmax} (weight {2*rmax}). floor needs depth>{log2m}")
            else:
                w=2*rstar
                pr(f"  p={p} m={m} (ceil log2 m={log2m}): MIN BALANCED depth r*={rstar} (weight {w}); "
                   f"floor-refuted(need depth>{log2m})? {rstar<=log2m}; witness={sorted(zip(wit[0],wit[1]))}")
