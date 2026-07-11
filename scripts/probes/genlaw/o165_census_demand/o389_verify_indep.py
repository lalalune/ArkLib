from math import comb
# Independent recompute of all claimed identities/forms vs the 9 COMPUTED points.

# COMPUTED data points (from O171/O172, to be confirmed by kernel):
data = {
 (16,3):97, (16,4):145, (16,5):89, (16,6):113, (16,7):225, (16,8):104,
 (32,3):897, (32,4):3105, (32,5):1441,
}

def K(n,r): return (2**r)*comb(n//2, r)

print("=== Part A: r=3 exact form #bad = n*C(n/4,2)+1 = n^2(n-4)/32+1 ===")
for n in [16,32,64,128]:
    f1 = n*comb(n//4,2)+1
    f2 = n*n*(n-4)//32 + 1
    print(f"n={n}: nC(n/4,2)+1={f1}  n^2(n-4)/32+1={f2}  match={f1==f2}", end="")
    if (n,3) in data: print(f"  vs COMPUTED {data[(n,3)]}: {'OK' if f1==data[(n,3)] else 'MISMATCH'}")
    else: print()

print("\n=== Part A: K-#bad = (h-2)h(13h-16)/12 - 1 > 0, h=n/2 ===")
for n in [16,32,64,128,256]:
    h = n//2
    bad = n*comb(n//4,2)+1
    Kv = K(n,3)
    lhs = Kv - bad
    rhs = (h-2)*h*(13*h-16)//12 - 1
    print(f"n={n} h={h}: K={Kv} #bad={bad} K-#bad={lhs}  identity (h-2)h(13h-16)/12-1={rhs}  match={lhs==rhs}  >0={rhs>0}  ratio K/#bad={Kv/bad:.3f}")
print("asymptotic K/#bad ->", "K~8*(h^3/6)=4h^3/3 ; #bad~n^3/32=(2h)^3/32=h^3/4 ; ratio->(4/3)/(1/4)=16/3=",16/3)

print("\n=== Part B: #bad <= K/2 = 2^(r-1)*C(n/2,r) at all 9 points ===")
worst_ratio=0; worst_pt=None
for (n,r),bad in sorted(data.items()):
    Kv=K(n,r); half=Kv//2
    ratio=bad/Kv
    leqK = bad<=Kv; leqHalf = bad<=Kv/2; leqQ = bad<=Kv/4; leqT = bad<=Kv/3
    if ratio>worst_ratio: worst_ratio=ratio; worst_pt=(n,r)
    print(f"n={n} r={r}: #bad={bad} K={Kv} K/2={Kv/2:.0f} ratio={ratio:.4f}  <=K:{leqK} <=K/2:{leqHalf} <=K/3:{leqT} <=K/4:{leqQ}")
print(f"WORST ratio #bad/K = {worst_ratio:.4f} at {worst_pt}  (K/2 bound holds iff <0.5)")

print("\n=== REFUTED candidate forms (verify they fail) ===")
print("naive n*C(n/4,r-1)+1 vs actual at n=16 r=4..7:")
for r in [4,5,6,7]:
    n=16; cand=n*comb(n//4,r-1)+1
    print(f"  r={r}: n*C(n/4,{r-1})+1={cand}  actual={data[(n,r)]}  {'match' if cand==data[(n,r)] else 'FAILS'}")
print("2^(r-1)*C(n/2,r-1) vs actual at n=16 r=3,4:")
for r in [3,4]:
    n=16; cand=2**(r-1)*comb(n//2,r-1)
    print(f"  r={r}: 2^{r-1}*C(8,{r-1})={cand}  actual={data[(n,r)]}  {'match' if cand==data[(n,r)] else 'FAILS'}")
print("n-scaling ratios (16->32):")
for r in [3,4,5]:
    print(f"  r={r}: {data[(32,r)]}/{data[(16,r)]} = {data[(32,r)]/data[(16,r)]:.2f}  (n^2 would be 4.0)")
