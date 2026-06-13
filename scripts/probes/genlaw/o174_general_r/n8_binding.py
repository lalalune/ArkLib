from math import comb
def K(n,r): return (2**r)*comb(n//2,r)
# n=8 full deep band
n8 = {2:5,3:9,4:8}
print("n=8 deep band:")
for r,bad in n8.items():
    Kv=K(8,r); print(f"  r={r}: #bad={bad} K={Kv} #bad/K={bad/Kv:.4f}  <=K/2? {bad<=Kv/2}  {'<<-- EQUALS K/2' if bad==Kv//2 else ''}")
# r=3 form at n=8
print(f"\nr=3 form at n=8: n*C(n/4,2)+1 = 8*C(2,2)+1 = {8*comb(2,2)+1}  vs computed 9: {8*comb(2,2)+1==9}")
print("\nBINDING-BAND TREND (r=n/2):")
print(f"  n=8  r=4: #bad/K = 8/16   = {8/16:.4f}  (EXACTLY 0.5 = K/2, SATURATED)")
print(f"  n=16 r=8: #bad/K = 104/256= {104/256:.4f}")
print("  => the K/2 bound is TIGHT at n=8 (equality), 0.406 at n=16. Ratio DECREASING 0.50->0.41.")
print("     This is FAVORABLE evidence for K/2 (margin grows with n at the binding band),")
print("     but n=8 saturating means K/c for any c>2 is FALSE even asymptotically-from-below.")
print("     K/2 is the UNIQUE tightest clean bound: tight at n=8, slack at n=16.")
