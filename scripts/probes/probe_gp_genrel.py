# Characterize F_p-genuine cyclotomic relations for mu_8 (Z[zeta_8], zeta^4=-1).
# alpha = sum x - sum y, x,y in mu_8^r. vector v[e]=(#e in x)-(#e in y), e=0..7.
# char-0 alpha=0  <=>  reduced w[j]=v[j]-v[j+4]=0 for j=0..3.
# F_p relation     <=>  sum_e v[e]*z^e ≡ 0 mod p.
# genuine          <=>  F_p relation AND w != 0.
import itertools, collections
def setup(n,p):
    # generator of mu_n
    e=(p-1)//n
    for a in range(2,p):
        z=pow(a,e,p)
        if pow(z,n//2,p)!=1: return z
def run(n,p,r):
    z=setup(n,p); zp=[pow(z,i,p) for i in range(n)]
    # enumerate multisets of size r from exponents 0..n-1 (sums), group by F_p sum value AND by Z-vector
    from itertools import combinations_with_replacement as cwr
    # sum-side: list of (Fp_sum, counter) for all r-multisets
    sums=[]
    for combo in cwr(range(n), r):
        fp=sum(zp[e] for e in combo)%p
        cnt=collections.Counter(combo)
        sums.append((fp,tuple(cnt[e] for e in range(n))))
    # group by fp value
    byfp=collections.defaultdict(list)
    for fp,vec in sums: byfp[fp].append(vec)
    genuine=0; char0=0; gen_examples=[]
    import math
    for fp,vecs in byfp.items():
        for vx in vecs:
            for vy in vecs:
                v=tuple(vx[e]-vy[e] for e in range(n))
                w=tuple(v[j]-v[j+n//2] for j in range(n//2))  # reduce zeta^{n/2}=-1
                if all(c==0 for c in w): char0+=1
                else:
                    genuine+=1
                    if len(gen_examples)<5: gen_examples.append((v,w))
    return char0,genuine,gen_examples,len(sums)
for (n,p,r) in [(8,97,3),(8,97,4),(8,193,4),(8,769,4)]:
    c0,g,ex,N=run(n,p,r)
    print(f"n={n} p={p} r={r}: total_r-multisets={N}  char0_pairs={c0} genuine_pairs={g}  ratio g/c0={g/max(c0,1):.3f}",flush=True)
    if g>0:
        print(f"   sample genuine reduced-w (should be nonzero, ≡0 mod p): {[e[1] for e in ex[:3]]}",flush=True)
