from math import comb

# Full data: (n,r,#bad, #align where known)
# from r5_n32_sweep + cf.md + this pass
DATA = [
 # n,  r, bad,  align(if known)
 (16,3, 97,  None),
 (16,4, 145, None),
 (16,5, 89,  None),
 (16,6, 113, None),
 (16,7, 225, None),
 (16,8, 104, None),
 (32,3, 897, None),
 (32,5, 1441, 23760),  # maximizer (17,31)
]

print("Testing candidate UPPER bounds (must hold AND be <=K, ideally clean):")
print(f"{'n':>3}{'r':>3}{'bad':>6}{'K':>9} | candidates...")
hdr = ["K/2", "C(n/2,r)", "2*C(n/2,r)", "n*C(n/4,2)+1", "C(n,r)", "n^2*(n-4)/32+1"]
print(" "*22 + "  ".join(f"{h:>14}" for h in hdr))
for n,r,bad,al in DATA:
    K = (2**r)*comb(n//2,r)
    cands = {
      "K/2": K//2,
      "C(n/2,r)": comb(n//2,r),
      "2*C(n/2,r)": 2*comb(n//2,r),
      "n*C(n/4,2)+1": n*comb(n//4,2)+1,
      "C(n,r)": comb(n,r),
      "n^2*(n-4)/32+1": n*n*(n-4)//32+1,
    }
    line=f"{n:>3}{r:>3}{bad:>6}{K:>9} |"
    for h in hdr:
        v=cands[h]
        ok = "<=" if bad<=v else "X "
        line += f"  {ok}{v:>12}"
    print(line)

print("\n=== Does #bad <= n*C(n/4,2)+1 (the r=3 form) hold for ALL r? ===")
print("This is the KEY testable bound: the r=3 closed form as a UNIVERSAL bound.")
for n,r,bad,al in DATA:
    r3form = n*comb(n//4,2)+1
    print(f"  n={n} r={r}: #bad={bad}  vs n*C(n/4,2)+1={r3form}  {'HOLDS' if bad<=r3form else 'FAILS by '+str(bad-r3form)}")
