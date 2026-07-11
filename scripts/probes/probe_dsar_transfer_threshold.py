# ATTACK the char-0 -> char-p transfer DIRECTLY (the sole open content).
# Wick bound (char-0, PROVEN): E_r(mu_n) <= (2r-1)!!*n^r. char-p: E_r^{(p)} = char-0 + spurious mod-p.
# Prize needs E_r^{(p)} <= (2r-1)!!*n^r at depth r~log q, prize q~n^4. Two questions:
#  (Q1) does the char-p Wick bound HOLD at the prize-needed depth r=ceil(log q) for prize-shaped q?
#  (Q2) how does the FAILURE threshold scale -- smallest "bad" prime where E_r^{(p)} > Wick, vs n?
import cmath, math, sympy
def musub(n,p):
    g=sympy.primitive_root(p); h=pow(g,(p-1)//n,p); return [pow(h,j,p) for j in range(n)]
def periods(n,p):
    G=musub(n,p); w=2*math.pi/p
    return [abs(sum(cmath.exp(1j*w*((b*x)%p)) for x in G)) for b in range(1,p)]
def dfact(r):
    v=1
    for i in range(1,2*r,2): v*=i
    return v
def Er_charp(n,p,r):  # E_r^{(p)} = (1/p) sum_{b in F} |eta_b|^{2r}, includes b=0 (=n^{2r}/p... )
    # char-p additive energy = #{(x_1..x_r,y_1..y_r) in mu_n: sum x = sum y mod p} = (1/p) sum_b |eta_b|^{2r}
    A=[abs(v) for v in [sum(cmath.exp(2j*math.pi*((b*x)%p)/p) for x in musub(n,p)) for b in range(p)]]
    return sum(a**(2*r) for a in A)/p
print("(Q1) char-p Wick bound at PRIZE-NEEDED depth r=ceil(log_2 q) [n<=16 feasible], prize-shaped q>=n^4:")
print(f"{'n':>4}{'q':>9}{'beta':>5}{'r=ceil(lg q)':>13}{'E_r^p':>12}{'Wick=(2r-1)!!n^r':>18}{'E_r/Wick':>9}{'HOLDS?':>7}")
for (n,q) in [(8,4129),(8,32801),(16,65537),(16,1048609)]:
    if (q-1)%n: 
        q=n*((q-1)//n)+1
        while not sympy.isprime(q): q+=n
    r=math.ceil(math.log2(q))
    # cap r for feasibility of the sum (r up to ~20 ok since it's just powering p reals)
    Er=Er_charp(n,q,r); W=dfact(r)*n**r
    print(f"{n:>4}{q:>9}{math.log(q)/math.log(n):>5.1f}{r:>13}{Er:>12.3e}{W:>18.3e}{Er/W:>9.3f}{'YES' if Er<=W else 'NO':>7}")
print()
print("(Q2) failure-threshold scaling: smallest prime p=1 mod n where E_r^p > Wick, at fixed deep r=6:")
for n in [8,16,32]:
    r=6; W=dfact(r)*n**r; bad=None; m=1; cnt=0
    while cnt<60:
        p=n*m+1; m+=1
        if not sympy.isprime(p): continue
        cnt+=1
        if Er_charp(n,p,r)>W: bad=p; break
    print(f"  n={n} r={r}: smallest bad prime = {bad if bad else '>60th prime (none small)'}; (prize q~n^4={n**4})")
