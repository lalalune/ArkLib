import cmath, math
# Probe: does the L2-doubling cap the count of SAME-SIGN (doubling) frequencies per level?
# Recursion f_{i+1}(b)=f_i(b)+f_i(zeta b). L2: sum_b |f_{i+1}|^2 = 2 sum_b |f_i|^2 (PROVEN).
# Expand: |f_{i+1}(b)|^2 = |f_i(b)|^2 + |f_i(zeta b)|^2 + 2 Re(f_i(b) conj f_i(zeta b)).
# Reality (i>=1): = f_i(b)^2 + f_i(zeta b)^2 + 2 f_i(b) f_i(zeta b)  (all real).
# Sum over b of cross term 2 f_i(b) f_i(zeta b) must be ZERO (since sum|f_{i+1}|^2 = sum f_i(b)^2 + sum f_i(zeta b)^2 = 2 sum f_i^2).
# So: SUM over b of [f_i(b)*f_i(zeta b)] = 0  EXACTLY. That's a clean SIGN-BALANCE identity!
# => the signed cross-products cancel in aggregate: same-sign (+) freqs are balanced by opposite-sign (-) freqs, WEIGHTED by |f||f|.
def primfind(n, lo):
    q=max(n+1,lo)
    while True:
        if (q-1)%n==0 and all(q%p for p in range(2,int(q**.5)+1)):
            for g in range(2,q):
                if pow(g,q-1,q)==1 and all(pow(g,(q-1)//pp,q)!=1 for pp in set(f for f in range(2,q) if (q-1)%f==0)):
                    return q,g
        q+=1
def eta(b,G,p):
    return sum(cmath.exp(2j*math.pi*((b*x)%p)/p) for x in G)
print("check the EXACT sign-balance identity: sum_b f_i(b)*f_i(zeta b) == 0  (i>=1, real)", flush=True)
for n in [16,32]:
    p,g=primfind(n,3000)
    z=pow(g,(p-1)//n,p)
    a=int(math.log2(n))
    for i in range(1,a):
        m=2**i
        zz=pow(z,n//m,p)
        Gi=[pow(zz,j,p) for j in range(m)]
        zeta=pow(z,n//(2*m),p)   # primitive 2^{i+1}-th root
        cross=0.0
        pos=0; neg=0; zero=0
        for b in range(p):
            fb=eta(b,Gi,p).real
            fzb=eta((b*zeta)%p,Gi,p).real
            prod=fb*fzb
            cross+=prod
            if prod>1e-9: pos+=1
            elif prod<-1e-9: neg+=1
            else: zero+=1
        print(f"n={n} i={i}->{i+1}: sum_b f(b)f(zeta b)={cross:+.3e}  (#+={pos} #-={neg} #0={zero})", flush=True)
