import math
def log_double_fact(m):  # ln((2r-1)!!) accumulate
    s=0.0
    while m>1: s+=math.log(m); m-=2
    return s

n = 2**30
ln_n = 30*math.log(2)
for beta in [4,5]:
    ln_q = beta*ln_n
    print(f"\n=== n=2^30, q=2^{int(beta*30)}, beta={beta} (ln q={ln_q:.1f}, r*~{ln_q:.0f}) ===")
    best_r=None; best_lnM=1e99
    sing=[1,2,3,4,5,10,20,40,int(ln_q),120]
    for r in range(1,200):
        # ln(M_r) = 0.5 * (1/r) * (ln q + ln((2r-1)!!) + r*ln n)
        ln_Mrsq = (ln_q + log_double_fact(2*r-1) + r*ln_n)/r
        ln_Mr = 0.5*ln_Mrsq
        if ln_Mr<best_lnM: best_lnM=ln_Mr; best_r=r
        if r in sing:
            over_n = ln_Mr - ln_n         # ln(M_r/n)
            over_sq = ln_Mr - 0.5*ln_n    # ln(M_r/sqrt n)
            tag=" <n" if over_n<0 else "  (>=n, useless)"
            print(f"   r={r:3d}: M_r/n=2^{over_n/math.log(2):8.3f}   M_r/sqrt(n)={math.exp(over_sq):10.2f}*sqrt(n){tag}")
    print(f"  >>> optimum r*={best_r}: M/sqrt(n)={math.exp(best_lnM-0.5*ln_n):.3f}*sqrt(n)")
    # target sqrt(2 n ln q)/sqrt(n) = sqrt(2 ln q)
    print(f"  >>> target sqrt(2 ln q) = {math.sqrt(2*ln_q):.3f}*sqrt(n)  (Ramanujan ~2)")
