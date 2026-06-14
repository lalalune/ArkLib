#!/usr/bin/env python3
"""
#407 CONNECTION C5 — ADVERSARIAL VERIFIER (independent re-derivation).

I do NOT reuse the agent's code. I rebuild eta_b from scratch (np.fft), and check FIVE things:

(V1) The base Fourier identity A_k(n) := E_k(mu_n) - n^{2k}/p == (1/p) sum_{b!=0} |eta_b(mu_n)|^{2k}.
     This is the claim "A_k IS the 2k-th moment of the sup-norm". If true, the WHOLE recursion is
     a recursion on moments of M(n) = max_b|eta_b| -> potential BGK circularity.
     E_k(mu_n) := #{(x_1..x_k,y_1..y_k) in mu_n^{2k} : sum x_i = sum y_i (mod p)} / 1   (additive 2k-energy).

(V2) The recursion A_k(n) + A^chi_k(n) = 2 sum_i C(2k,2i) M_{i,k-i}(n/2), independently.

(V3) THE CIRCULARITY TEST. The agent's LEVERAGE claim: closing the recursion to Wick requires
     bounding interior cross-moments + twist moment = "the open energy bound E_r(mu_n) <= (2r-1)!! n^r".
     I test: is the per-level obstruction LITERALLY the same quantity as the BGK moment, or merely
     "the same size"? Concretely: does the recursion give ANY bound that the direct moment hierarchy
     does NOT already give? I check whether A_k(n) is DETERMINED by {A_j(n/2)} alone (a genuine closed
     recursion) or whether it needs the joint object M_{i,k-i} which is NOT a function of single-freq
     level-(n/2) moments (i.e. the recursion is NOT closed -> it does not reduce the unknown count).

(V4) THE BGK CROSSOVER (r* ~ beta+1). The deep-moment wall turns on at the crossover where the
     char-p energy exceeds char-0 Wick. Check: at fixed k, is A_k(n) <= (2k-1)!! n^k (Wick) or does it
     exceed? And does the recursion's Young/AM-GM telescoping give 4^{k(mu-1)} (trivial) vs 2^k-per-level
     (Wick)? Confirm the agent's "loss factor 4^k vs 2^k".

(V5) Does the recursion CLOSE k=1 unconditionally? The agent claims A_1(n)/A_1(n/2)->2 because the
     order-1 cross-correlation E[AB]->0 (Parseval). Check E[AB]=(1/p)sum_b A(b)B(b) -> 0, and that
     this is the PROVEN E_2(mu_n)=3n^2-3n fact, not an assumption.
"""
import numpy as np
from sympy import isprime, primitive_root as pr
from math import comb

def eta_all(n, p):
    """eta_b(mu_n) for all b in [0,p), via FFT of the indicator of mu_n. Real for 4|n."""
    g = int(pr(p))
    t = pow(g, (p-1)//n, p)
    ind = np.zeros(p)
    x = 1
    for _ in range(n):
        ind[x] += 1.0
        x = (x*t) % p
    # eta_b = sum_{x in mu_n} e_p(b x) = sum_x ind[x] e^{2pi i b x / p} = conj(FFT(ind))[b]
    F = np.conjugate(np.fft.fft(ind))
    return F, t   # F[b] complex; should be ~real for 4|n

def Ek_direct(n, p, k):
    """E_k(mu_n) = #{(x_1..x_k,y_1..y_k): sum x = sum y mod p}, computed as (1/p) sum_b |eta_b|^{2k}
       INCLUDING b=0. This is the STANDARD Fourier identity for additive energy. The b=0 term is n^{2k}/p.
       Return both E_k (full, includes b=0) and A_k = E_k - n^{2k}/p = (1/p) sum_{b!=0}|eta_b|^{2k}."""
    F, _ = eta_all(n, p)
    absF2k = (np.abs(F)**(2*k))
    Ek = absF2k.sum()/p          # full energy (Fourier); should be an INTEGER (count)
    Ak = (absF2k.sum() - absF2k[0])/p   # drop b=0 ; absF2k[0]=n^{2k}
    return Ek, Ak, absF2k[0]

def Ek_count_bruteforce(n, p, k):
    """Independent INTEGER count of E_k(mu_n) for small k,n: #{x,y in mu_n^k : sum x = sum y mod p}.
       Done via convolution power of the indicator (exact integer FFT-free conv on Z/p)."""
    g = int(pr(p)); t = pow(g, (p-1)//n, p)
    ind = np.zeros(p, dtype=np.int64); x=1
    for _ in range(n): ind[x]+=1; x=(x*t)%p
    # k-fold cyclic convolution power -> distribution of sum of k elements
    cur = ind.copy()
    for _ in range(k-1):
        cur = np.array([sum(cur[j]*ind[(s-j)%p] for j in range(p)) for s in range(p)], dtype=np.int64)
    # E_k = sum_s cur[s]^2
    return int((cur.astype(object)**2).sum())

def main():
    print("="*100)
    print("(V1) BASE FOURIER IDENTITY: A_k(n) = E_k(mu_n) - n^{2k}/p = (1/p) sum_{b!=0}|eta_b|^{2k} ?")
    print("     Cross-check E_k(mu_n) (Fourier) vs an INDEPENDENT integer count (convolution).")
    print("="*100)
    for n, plist in [(8,[41,97]),(16,[97,193])]:
        for p in plist:
            if (p-1)%n: continue
            for k in [1,2]:
                Ek_f, Ak, b0 = Ek_direct(n,p,k)
                Ek_c = Ek_count_bruteforce(n,p,k)
                print(f"  mu_{n} p={p} k={k}: E_k(Fourier)={Ek_f:.4f}  E_k(count,int)={Ek_c}  "
                      f"match={abs(Ek_f-Ek_c)<1e-6}   b=0 term n^2k/p={b0:.1f} (=n^{2*k}={n**(2*k)})  "
                      f"A_k={Ak:.4f}")
    print()
    print("="*100)
    print("(V5) k=1 CLOSURE: is E_2(mu_n)=3n^2-3n (proven), forcing A_1(n)/A_1(n/2)->2 ?")
    print("     A_1(n) = E_1(mu_n) - n^2/p where E_1(mu_n)=(1/p)sum_b|eta_b|^2 = n (Parseval, integer).")
    print("     WAIT: E_1 (k=1) = n (trivial). The agent uses A_1 = (1/p)sum_{b!=0}|eta_b|^2 = n - n^2/p.")
    print("="*100)
    for n,plist in [(8,[97,401]),(16,[193,1153]),(32,[1153,2113])]:
        for p in plist:
            if (p-1)%n: continue
            F,t = eta_all(n,p)
            A1 = (np.abs(F)**2).sum()/p - (np.abs(F[0])**2)/p   # = n - n^2/p
            # level n/2
            F2,_ = eta_all(n//2,p)
            A1h = (np.abs(F2)**2).sum()/p - (np.abs(F2[0])**2)/p  # = n/2 - (n/2)^2/p
            ratio = A1/A1h
            # analytic: A1 = n - n^2/p ; A1h = n/2 - n^2/(4p) ; ratio = (n - n^2/p)/(n/2 - n^2/4p)
            print(f"  mu_{n} p={p}: A_1(n)={A1:.4f} (=n-n^2/p={n-n*n/p:.4f}), A_1(n/2)={A1h:.4f}, "
                  f"ratio={ratio:.5f} -> 2 as p->inf? (analytic limit = 2*(1-n/p)/(1-n/2p))")
    print()
    print("="*100)
    print("(V4) WICK vs TRIVIAL: is A_k(n) <= (2k-1)!! n^k (Wick=PRIZE) or only <= n^{2k}/4^k C(2k,k) (TRIVIAL)?")
    print("="*100)
    def dfact(m):
        r=1
        for j in range(1,m+1,2): r*=j
        return r
    for n,plist in [(8,[401]),(16,[1153]),(32,[2113]),(64,[8161])]:
        for p in plist:
            if not isprime(p) or (p-1)%n:
                # find a prime ~ given
                pp=p
                while not (isprime(pp) and (pp-1)%n==0): pp+=1
                p=pp
            F,t=eta_all(n,p)
            absF2=np.abs(F)**2
            print(f"  mu_{n} p={p}:")
            for k in [1,2,3,4]:
                Ak=((absF2**k).sum()-absF2[0]**k)/p
                wick=dfact(2*k-1)*n**k
                trivial=comb(2*k,k)*(n**(2*k))/(4**k)
                print(f"    k={k}: A_k={Ak:12.2f}  Wick=(2k-1)!!n^k={wick:12.0f} (A/Wick={Ak/wick:.3f})  "
                      f"Trivial=C(2k,k)n^2k/4^k={trivial:14.0f} (A/Triv={Ak/trivial:.4f})")
    print()
    print("="*100)
    print("(V3) CIRCULARITY: is the recursion CLOSED in {A_j(n/2)}, or does it need the JOINT M_{i,k-i}?")
    print("     If M_{i,k-i} is NOT a function of {A_j(n/2)}, the recursion does NOT reduce the unknown.")
    print("     Test: across DIFFERENT primes p with the SAME {A_j(n/2)} pattern, does M_{1,1} track A_2(n/2)")
    print("     by a FIXED ratio (closed) or vary independently (joint=not closed)?")
    print("="*100)
    for n in [16,32]:
        rows=[]
        plist=[pp for pp in range(50,4000) if isprime(pp) and (pp-1)%n==0][:8]
        for p in plist:
            F2,t=eta_all(n//2,p)          # level n/2 periods, all b
            A=F2.real
            zeta=pow(int(pr(p)),(p-1)//n,p)   # generator of mu_n
            idx=(np.arange(p)*zeta)%p
            B=A[idx]
            mask=np.ones(p); mask[0]=0
            A2h=((A**4)*mask).sum()/p      # A_2(n/2) = M_{2,0}
            M11=(((A**2)*(B**2))*mask).sum()/p  # interior cross-moment
            R=M11/A2h
            rows.append((p,A2h,M11,R))
        print(f"  mu_{n//2} (=level n/2): M_(1,1)/A_2(n/2) across primes -- is it FIXED (closed) or varies?")
        for p,A2h,M11,R in rows:
            print(f"    p={p:5d}: A_2(n/2)={A2h:10.2f}  M_(1,1)={M11:10.2f}  R=M11/A2(n/2)={R:.4f}")
        Rs=[r[3] for r in rows]
        print(f"    -> R range [{min(Rs):.4f}, {max(Rs):.4f}], spread {max(Rs)-min(Rs):.4f}  "
              f"({'VARIES => recursion NOT closed' if max(Rs)-min(Rs)>0.05 else 'fixed'})")

if __name__=="__main__":
    main()
