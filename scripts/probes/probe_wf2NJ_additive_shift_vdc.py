#!/usr/bin/env python3
"""
LANE wf-NJ (#407) part 2 — the GENUINE Polymath8 / FKM q-vdC ADDITIVE-SHIFT step
(distinct from the multiplicative shift-by-2 in part 1, which was BGK-circular).

The true van-der-Corput / FKM autocorrelation for a sum sum_x K(x) over a SET is:
  |sum_{x in A} f(x)|^2 <= |A| sum_{x} 1_A(x) |f(x)|^2   (CS, trivial here, |f|=1)
NO -- the FKM gain is from completing the A-sum and shifting K ADDITIVELY:
  S(b)=sum_{x in F_p} 1_{mu_n}(x) e_p(bx). 1_{mu_n}(x)=(n/(p-1)) sum_{chi: chi^n... } NO,
  1_{mu_n}(x)= (n/p?) ... use 1_{mu_n}(x)= (1/m) sum_{j=0}^{m-1} chi_0^{... }. Cleanest:
  1_{mu_n}(x) = (n/(p-1)) sum_{psi^n=1} psi(x)  (sum over the n mult. characters trivial on mu_n? )
  Actually mu_n = {x: x^n=1}; 1_{mu_n}(x)=(1/m) sum_{d|... } -- use the indicator via the
  m=(p-1)/n characters chi with chi=phi^{n} powers: 1_{mu_n}(x) = (1/m) sum_{k=0}^{m-1} (phi^{n})^k? NO.

We instead test the FKM mechanism EMPIRICALLY in the form that would give a gain:
the ADDITIVE-correlation sheaf. The Polymath8 Type-I/II estimate bounds, for K=trace fn,
  sum_h |sum_x K(x) conj K(x+h)|  with power saving when the shifted sheaf [x->K(x)K(x+h)]
is geometrically irreducible & bounded-conductor for most h. Our K = 1_{mu_n} * e_p(bx).
The additive autocorrelation is
  R(h) = sum_x 1_{mu_n}(x) 1_{mu_n}(x+h) e_p(b h)  -> the bracket counts |mu_n cap (mu_n - h)|.
This is the ADDITIVE-ENERGY structure of mu_n, which the section-6 no-go list flags as
'additive-energy/L2/Parseval ... reduce-to-wall'. SO this part must HONESTLY check
whether the FKM framing gives anything the additive-energy framing did not.

WHAT IS GENUINELY TESTABLE & NEW: the FKM 'conductor of the product sheaf'
c(h) = conductor of the sheaf L_psi(bx) tensor [x -> 1_{mu_n}(x)1_{mu_n}(x+h)].
For a BOUNDED-conductor family FKM gives sqrt(p) * c. We measure the EFFECTIVE conductor:
  c_eff(b) := |S(b)| / sqrt(p)   (= BGK ratio) and the SHIFTED-SHEAF count
  N(h) := |mu_n cap (mu_n - h)|  (additive correlation), and ask whether the
  distribution of N(h) (the conductor proxy) is BOUNDED (O(1), FKM-applicable) or GROWS.
If sup_h N(h) is O(1) for h != 0, the mu_n indicator behaves like a bounded-conductor
'Kloosterman-type' set and FKM could in principle give M(n) = O(sqrt(p) log) -- which in
the prize (sqrt(p)=n^{2..2.5}) is WORSE than trivial n. If sup_h N(h) grows, even that fails.
EITHER WAY this pins the conductor-aspect lens for the prime-modulus prize.
"""
import math

def is_prime(m):
    if m<2:return False
    if m%2==0:return m==2
    d=m-1;s=0
    while d%2==0:d//=2;s+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        if a%m==0:continue
        x=pow(a,d,m);ok=(x==1)
        for _ in range(s):
            if x==m-1:ok=True;break
            x=x*x%m
        if not ok:return False
    return True

def find_prime(n,target):
    base=target-(target%n)+1
    for d in range(0,200*n,n):
        if is_prime(base+d):return base+d
    return None

def subgroup(p,n):
    for g0 in range(2,500):
        g=pow(g0,(p-1)//n,p)
        H=set();x=1
        for _ in range(n):H.add(x);x=x*g%p
        if len(H)==n:return sorted(H)
    raise RuntimeError

print("="*92)
print("wf-NJ part 2: additive-shift / conductor-of-product-sheaf test (FKM applicability)")
print("="*92)
print(f"{'n':>4} {'p':>10} {'beta':>5} | {'sup_{h!=0} N(h)':>15} {'#h with N>0':>12} {'meanN(h>0)':>11} | {'FKM-bound sqrtp*supN':>20} {'vs trivial n':>12}")
for n,beta in [(8,4),(16,4),(16,5),(32,4),(64,4),(128,4)]:
    p=find_prime(n,int(round(n**beta)))
    if p is None or p>80_000_000:
        print(f"{n:>4} skip");continue
    H=set(subgroup(p,n))
    # N(h)=|mu_n cap (mu_n - h)| for h!=0
    Hl=sorted(H)
    cnt={}
    # additive correlation: for each pair x,y in H, h=x-y gives x in H and x-h=y in H => x in (H) cap (H+h)?
    # define N(h)=#{x in H: x+h in H} = #{(x,y) in HxH: y-x=h}. so:
    for x in Hl:
        for y in Hl:
            h=(y-x)%p
            if h!=0:
                cnt[h]=cnt.get(h,0)+1
    if cnt:
        supN=max(cnt.values());npos=len(cnt);meanN=sum(cnt.values())/npos
    else:
        supN=0;npos=0;meanN=0
    fkm=math.sqrt(p)*supN
    print(f"{n:>4} {p:>10} {beta:>5} | {supN:>15} {npos:>12} {meanN:>11.3f} | {fkm:>20.1f} {'n='+str(n):>12}")

print("""
INTERPRETATION:
  N(h) = additive correlation (Sidon-type) count of mu_n. sup_h N(h) is the conductor
  proxy of the FKM product sheaf [x->1_{mu_n}(x)1_{mu_n}(x+h)].
  * If sup_h N(h) is O(1): mu_n is near-Sidon, the product sheaf is bounded-conductor, and
    FKM would give M(n) <= sqrt(p) * O(1) * log -- but in the PRIZE sqrt(p)=n^{beta/2}>=n^2,
    so even the BEST FKM bound is n^2 >> trivial n. The conductor aspect is OFF THE WALL
    (wrong direction) for a PRIME modulus, exactly like the Weil/completion no-go (L3):
    there is no large modulus/level to be in the 'conductor aspect' of.
  * If sup_h N(h) grows with n: the set is NOT bounded-conductor and FKM fails at the
    sheaf level too.
  Either way: FKM/conductor-aspect needs the modulus (or form level) -> infinity with
  BOUNDED conductor. The prize fixes the modulus = the prime p and the 'sheaf' (mu_n) has
  conductor tied to n; there is NO conductor aspect to exploit. PIN.
""")
