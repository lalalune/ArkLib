import math
# gap = 1/24 - saving. saving = (10 - 2 t3 - t2/2)/72, 1/24 = (10 - 6 - 1)/72 = 3/72.
# gap = (2(t3-3) + (t2-2)/2)/72.
# t2 - 2 = log(3 - 3/n)/log n -> log3/log n ; t3 - 3 = log(15 - 45/n + 40/n^2)/log n -> log15/log n
# => gap*log n -> (2 log15 + (log3)/2)/72
pred = (2*math.log(15) + math.log(3)/2)/72
print("predicted lim (gap*ln n) = (2 ln15 + (ln3)/2)/72 =", pred)
def E2(n): return 3*n*n-3*n
def E3(n): return 15*n**3-45*n*n+40*n
def t(E,n): return math.log(E)/math.log(n)
def saving(t2,t3): return (10-2*t3-t2/2)/72
for a in [10,20,30,40,50,60,80,100]:
    n=2**a
    g=(1/24-saving(t(E2(n),n),t(E3(n),n)))
    print(f"2^{a}: gap*ln n = {g*math.log(n):.8f}   (pred {pred:.8f}, diff {g*math.log(n)-pred:.2e})")
