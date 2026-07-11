#!/usr/bin/env python3
"""
#407 — THE DECISIVE CHAR-0 EXPERIMENT.

For the HUGE prize field (q ~ n*2^128) the F_q-random excess of the vanishing-power-sum variety
is negligible (relation-free, verified), so the bad-scalar count is dominated by the CHAR-0
members: S ⊆ μ_n with e_1(S)=...=e_{t-1}(S)=0 EXACTLY in ℂ (as algebraic integers in ℤ[ζ_n]).

Question: is the char-0 image L_0 = #{distinct e_t(S) : char-0-vanishing S} small (≤ ~n, O(1)
cosets)?  If YES, the floor reduces to a CHAR-0 rigidity (Lam-Leung territory) + the verified
relation-free transfer — NEITHER of which is the F_q Paley/BGK character-sum wall. That would be a
genuine path around the wall.

Also tests the TOWER RIGIDITY: is every char-0-vanishing S a union of μ_{2^j}-cosets?

Exact ℤ[ζ_n] arithmetic: element = length-(n/2) integer vector (coeffs of 1,ζ,...,ζ^{n/2-1}),
ζ^{n/2} = -1.  μ_n = {ζ^0,...,ζ^{n-1}}, indices 0..n-1.
"""
import itertools, math

def mul_zeta(v, i, half):
    """v * ζ^i  in ℤ[ζ_n], n=2*half, ζ^half=-1.  v is length-half int list."""
    out=[0]*half
    n=2*half
    for s in range(half):
        if v[s]==0: continue
        m=(s+i)%n
        if m<half: out[m]+=v[s]
        else: out[m-half]-=v[s]
    return out

def esyms_char0(S, tmax, half):
    """e_0..e_tmax of {ζ^i : i in S} as ℤ[ζ_n] vectors (tuples)."""
    e=[[0]*half for _ in range(tmax+1)]
    e[0][0]=1
    for i in S:
        for j in range(min(tmax,len(e)-1),0,-1):
            term=mul_zeta(e[j-1], i, half)
            for r in range(half): e[j][r]+=term[r]
    return e

def is_zero(vec): return all(x==0 for x in vec)

def is_coset_union(S, n):
    """Is S a union of μ_{2^j}-cosets for some j>=1?  (μ_{2^j} = <g^{n/2^j}> in index terms =
    arithmetic progression step n/2^j.)  Check largest j with S closed under +n/2^j shifts."""
    Sset=set(S)
    for j in range(1, int(math.log2(n))+1):
        step=n//(2**j)
        # S is union of cosets of subgroup {0,step,2step,...} iff closed under +step
        if all(((x+step)%n in Sset) for x in Sset) and len(Sset)%(2**j)==0:
            return 2**j
    return 1  # only trivial

print("="*84)
print("CHAR-0 vanishing-power-sum variety: count, image L_0, tower-rigidity (coset structure)")
print("="*84)
for n in (8,16):
    half=n//2
    for rho in (0.25, 0.5):
        k=int(round(rho*n))
        print(f"\n n={n} rho={rho} k={k}  (Johnson 1-√ρ={1-rho**0.5:.3f}, cap {1-rho:.3f})")
        print(f"   {'t':>2} {'a=k+t':>5} {'δ':>6} | {'#char0-var':>10} {'L_0=#img':>9} {'L_0<=n?':>8} "
              f"{'all-coset?':>10} {'min-coset':>9}")
        for t in range(1, n-k+1):
            a=k+t
            if math.comb(n,a) > 2_000_000: continue
            cnt=0; img=set(); allcoset=True; mincoset=n
            for S in itertools.combinations(range(n), a):
                e=esyms_char0(S, t, half)
                if all(is_zero(e[j]) for j in range(1,t)):
                    cnt+=1
                    img.add(tuple(e[t]))
                    cu=is_coset_union(S,n)
                    if cu==1: allcoset=False
                    mincoset=min(mincoset,cu)
            L0=len(img)
            if cnt==0:
                print(f"   {t:>2} {a:>5} {1-a/n:>6.3f} | {0:>10} {0:>9} {'(empty)':>8} {'-':>10} {'-':>9}")
                continue
            print(f"   {t:>2} {a:>5} {1-a/n:>6.3f} | {cnt:>10} {L0:>9} {str(L0<=n):>8} "
                  f"{str(allcoset):>10} {mincoset:>9}")
print()
print("KEY: if L_0 <= n (and = O(1) cosets) for window-interior t, the floor's char-0 part is")
print("controlled WITHOUT F_q character sums.  'all-coset?'=True confirms the Lam-Leung tower")
print("rigidity (char-0 vanishing ⟹ μ_{2^j}-coset union).")
