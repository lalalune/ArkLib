import math
# K = 2^r * C(n/2, r). Verify against published ladder.
ladder16={3:97,4:145,5:89,6:113,7:225,8:104}
print("n=16:  r  #bad      K        K/#bad")
for r,b in ladder16.items():
    K=(2**r)*math.comb(8,r)
    print(f"       {r}  {b:>4}   {K:>6}   {K/b:.3f}")
print()
# n=32 r=3 proven: 897; r=4 from task '33x'
for n in [32,64]:
    print(f"n={n}:")
    for r in [3,4,5]:
        K=(2**r)*math.comb(n//2,r)
        if r==3:
            bad=n*math.comb(n//4,2)+1
            print(f"   r={r}: #bad(closed)={bad}  K={K}  K/#bad={K/bad:.3f}")
        else:
            print(f"   r={r}: K={K}")
