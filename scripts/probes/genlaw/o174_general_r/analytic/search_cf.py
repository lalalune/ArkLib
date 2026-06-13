import math
n=16; h=8; q4=4
lad={3:97,4:145,5:89,6:113,7:225,8:104}
def K(n,r): return 2**r*math.comb(n//2,r)
# Candidate families that must satisfy lad[r] <= cand(r) <= K(n,r) for ALL r in 3..8 (n=16).
cands = {
 "K/2 (ceil)": lambda r: (K(n,r)+1)//2,
 "2^(r-1)C(h,r)+1": lambda r: 2**(r-1)*math.comb(h,r)+1,
 "2^(r-1)C(h,r)+n": lambda r: 2**(r-1)*math.comb(h,r)+n,
 "2^r C(h,r)/2 = K/2": lambda r: 2**r*math.comb(h,r)//2,
 "r*2^(r-1)C(h-1,r-1)+1": lambda r: r*2**(r-1)*math.comb(h-1,r-1)+1,
 "n*2^(r-2)C(h-1,r-1)/r+1": lambda r: n*2**(r-2)*math.comb(h-1,r-1)//max(r,1)+1,
}
for name,f in cands.items():
    ok=True; row=[]
    for r in range(3,9):
        v=f(r); row.append(v)
        if not (lad[r]<=v<=K(n,r)): ok=False
    print(f"{'VALID' if ok else 'FAIL ':5} {name:28} ->", row, " (lad:",list(lad.values()),")")
print()
print("K values:", [K(n,r) for r in range(3,9)])
