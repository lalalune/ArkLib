from math import comb
# Verify which clean fractions K/c hold at EVERY one of the 9 points, and identify the binding band.
data = {(16,3):97,(16,4):145,(16,5):89,(16,6):113,(16,7):225,(16,8):104,(32,3):897,(32,4):3105,(32,5):1441}
def K(n,r): return (2**r)*comb(n//2,r)
print("Binding band = max #bad/K:")
ratios = sorted(((bad/K(n,r),n,r,bad,K(n,r)) for (n,r),bad in data.items()), reverse=True)
for rt,n,r,bad,Kv in ratios:
    print(f"  n={n} r={r}: #bad/K={rt:.4f}  (#bad={bad}, K={Kv})")
print()
for c in [1,2,3,4]:
    allok = all(bad <= K(n,r)/c for (n,r),bad in data.items())
    # find first failure
    fail = [(n,r,bad,K(n,r)/c) for (n,r),bad in data.items() if bad > K(n,r)/c]
    print(f"#bad <= K/{c}: {'HOLDS all 9' if allok else 'FAILS at '+str(fail)}")
print()
print("At binding n=16 r=8: K=256, K/2=128, K/3=85.33, K/4=64; #bad=104")
print(f"  104<=128? {104<=128}  104<=85.33? {104<=85.33}  104<=64? {104<=64}")
print("=> K/2 is the tightest clean power-of-2 fraction that survives. Defensible.")
