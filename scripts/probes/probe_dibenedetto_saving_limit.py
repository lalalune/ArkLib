import math
# realised exponents and saving for the dyadic subgroup mu_n
def E2(n): return 3*n*n - 3*n
def E3(n): return 15*n**3 - 45*n*n + 40*n
def t(E, n): return math.log(E)/math.log(n)
def saving(t2, t3): return (10 - 2*t3 - t2/2)/72

print("n, t2, t3, saving, gap=1/24-saving, gap*log(n)")
prev = None
mono = True
for a in range(2, 60):  # n = 2^2 .. 2^59
    n = 2**a
    t2 = t(E2(n), n); t3 = t(E3(n), n)
    s = saving(t2, t3)
    gap = 1/24 - s
    glog = gap*math.log(n)
    if a <= 8 or a % 10 == 0 or a >= 58:
        print(f"2^{a:2d}: t2={t2:.6f} t3={t3:.6f} saving={s:.8f} gap={gap:.3e} gap*ln(n)={glog:.5f}")
    if prev is not None and not (s > prev - 1e-15):
        mono = False
    prev = s
print("\n--- limit checks ---")
print(f"saving(2,3) = {saving(2,3):.10f} (should be 1/24 = {1/24:.10f})")
print(f"monotone increasing in n: {mono}")
n=2**55; t2=t(E2(n),n); t3=t(E3(n),n)
gap=1/24-saving(t2,t3)
print(f"at n=2^55: gap={gap:.3e}, gap*ln(n)={gap*math.log(n):.5f}  (const => gap=Theta(1/log n))")
