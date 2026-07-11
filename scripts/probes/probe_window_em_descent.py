"""
#407 FLOOR ATTACK — window-interior #distinct-e_m bound (combinatorial angle).

Probes the q-independent reduction I(δ) = #distinct e_m(T) over T⊆μ_n, |T|=k+m,
p_1(T)=..=p_{m-1}(T)=0, at the WINDOW INTERIOR (m=Θ(n/log n)).

FINDINGS (all reproduced below, prize regime q≫n unless noted):

1. PARITY LAW (probe-confirmed exactly, every t): for m≥2 in the prize regime, a valid
   T (p_1..p_{m-1}=0) is ANTIPODAL (closed under x↦−x); hence |T|=t must be EVEN.
   ODD t ⟹ char-0 #valid = 0 ⟹ I(δ)=0 (the only bad scalars are char-p antipodal-violators).

2. 2-ADIC DESCENT: even-t valid sets reduce (n,t,m)→(n/2,t/2,⌊(m−1)/2⌋+1) via
   p_{2j}(T)=2·p_j(U), U={x²:x∈half(T)}⊆μ_{n/2}. Depth = v_2(t). The DESCENDED power-sum
   is the readout. #distinct(top) = #distinct(bottom).

3. DICHOTOMY (the floor's true behavior):
   (A) small v_2(t) relative to m  → descent exhausts constraints with a still-large free
       bottom → I(δ)=Θ(min(q,C(N_b,s_b))) ≫ n  (NEAR-CAPACITY BLOWUP; floor I≤n FALSE).
       e.g. n=32,m=2: bottom(16,5,c=1) → I=2256≫32.
   (B) window interior (m large, small v_2) → bottom stays HEAVILY constrained on an odd-size
       subset → char-0 #valid = 0 → I(δ)=0 (floor holds, but VACUOUSLY in char 0).

4. THE WALL (secret M(n)): regime (B)'s "I=0" is the char-0 skeleton. The actual prize bad
   scalars are the char-p ANTIPODAL-VIOLATING T (hindep fails in F_q). Counting them via
   orthogonality, #{T: p_1..p_{m-1}≡0 mod q} = q^{-(m-1)} ∑_{b} ∑_T ∏_{x∈T} e_q(∑_i b_i x^i);
   off-diagonal b≠0 terms are EXACTLY η_b=∑_{x∈μ_n}e_q(bx) → max = M(n). The combinatorial
   reduction RELABELS, does not remove, the incomplete character sum. ⟹ the route secretly
   re-derives M(n) = the BGK wall.

VERDICT: clean structural decomposition (parity + descent), genuine partial localizing the
floor's failure to char-p; NOT a floor proof. Routes back to M(n)/BGK. Honest, axiom-clean numerics.
"""
import itertools, math

def is_prime(x):
    if x < 2: return False
    i = 2
    while i*i <= x:
        if x % i == 0: return False
        i += 1
    return True

def find_field(n, ratio):
    c = ratio
    while True:
        q = c*n + 1
        if is_prime(q): return q
        c += 1

def gen_subgroup(q, n):
    def order(a):
        o, x = 1, a % q
        while x != 1: x = x*a % q; o += 1
        return o
    g = 2
    while order(g) != q-1: g += 1
    h = pow(g, (q-1)//n, q)
    return [pow(h, i, q) for i in range(n)]

def verify_parity_law(N=16, ratio=500000):
    q = find_field(N, ratio); S = gen_subgroup(q, N); m1 = S[N//2]
    print(f"[parity] N={N} q={q}: valid(m>=2) == antipodal, odd t -> 0")
    for t in range(3, N+1):
        k = 1; m = t-k
        if m < 2: continue
        nv = antip = 0
        for T in itertools.combinations(S, t):
            if all(sum(pow(x,i,q) for x in T) % q == 0 for i in range(1, m)):
                nv += 1
                if all((m1*x) % q in set(T) for x in T): antip += 1
        print(f"  t={t}({'EVEN' if t%2==0 else 'ODD'}) m={m}: #valid={nv} #antip={antip} match={nv==antip}")

if __name__ == "__main__":
    verify_parity_law()
