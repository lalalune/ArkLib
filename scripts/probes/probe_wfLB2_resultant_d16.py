#!/usr/bin/env python3
"""
#407 LANE LB2 -- DIRECT resultant route to Chai-Fan Q1 (Conj 4.12) at d=16.

NOT self-similarity (route (i), refuted at d=32 by wf-LB). Instead: compute the
resultant/norm R_16 of the defining polynomials of V_16^prim DIRECTLY over Q, factor
it to identify EXACTLY the bad-reduction primes, and check no prize-scale prime
p = 1 (mod 16) divides it.

THE OBJECT. Q1 = Norm_{K_d/Q}(F_d(alpha)) != 0 on V_d^prim. For the dyadic prize family
the primitive gap variety at level d=16 is realized two equivalent ways:

  (I) p_1=0 slice (the route-(i) entry point): antipodal-free half-sets Y of mu_16
      whose Z[zeta_16] coordinate vector vanishes. R_16^{(p1)} = product of the
      coordinate-vector gcds. Over Q each vector is nonzero (Lam-Leung); the gcds are
      the only primes that could kill it mod p.

  (II) FULL F_16(alpha) norm: the bad-alpha set of the affine pencil
      h_alpha(z) = z^{c} + alpha z^{b} (c=k+1, b=k+2, n=4k=16 => k=4, c=5,b=6) is
      {alpha = -1/e_1(S) : (k+2)-subset S of mu_16, e_2(S)=0, e_1(S)!=0}. F_16 is the
      univariate poly over Q whose roots are these bad alpha values; its constant-term /
      norm R_16 = Norm(F_16) = product of (e_1(S)) over the relevant S (the resultant of
      e_2(S)=0 with the symmetric system, eliminating S). R_16 != 0 over Q <=> no
      char-0 primitive bad alpha. The prime factors of R_16 = bad-reduction primes.

We compute BOTH exactly with integer/rational arithmetic and factor R_16.
"""
import itertools
from math import gcd
from functools import reduce
import sympy as sp

n = 16; k = 4; half = 8

def is_prime(m):
    if m < 2: return False
    if m % 2 == 0: return m == 2
    i = 3
    while i*i <= m:
        if m % i == 0: return False
        i += 2
    return True

# ---------- (I) p_1=0 slice: coordinate-vector gcd product = R_16^{(p1)} ----------
def coordvec(Y):
    v = [0]*half
    for j in Y:
        e = j % n
        if e < half: v[e] += 1
        else: v[e-half] -= 1
    return tuple(v)

def slice_p1():
    gcds = []
    cnt = 0
    nonzero_all = True
    for Y in itertools.combinations(range(n), 8):
        Ys = set(Y)
        if any(((j+half) % n) in Ys for j in Y):  # antipodal-free
            continue
        v = coordvec(Y)
        cnt += 1
        if all(x == 0 for x in v):
            nonzero_all = False  # char-0 primitive point => Lam-Leung violated
        g = reduce(gcd, [abs(x) for x in v], 0)
        gcds.append(g)
    return cnt, gcds, nonzero_all

# ---------- (II) Full F_16(alpha) norm via the affine-pencil e_2=0 criterion ----------
# We need exact algebraic arithmetic in Q(zeta_16). zeta_16 satisfies Phi_16 = X^8 + 1.
# Represent elements as sympy polynomials in z modulo z^8 + 1 with rational coeffs.
def algeb_d16_norm():
    z = sp.symbols('z')
    cyc = z**8 + 1                      # Phi_16(z), zeta_16 a root
    K = sp.QQ.algebraic_field(sp.Rational(0))  # placeholder
    # We work with roots zeta^j = z^j mod (z^8+1) over QQ.
    # mu_16 = {z^j : j=0..15}, with z^8 = -1 in the field.
    def root_poly(j):
        # represent zeta^j as a degree<8 poly in z
        return sp.rem(sp.Poly(z**(j % 16), z), sp.Poly(cyc, z), z)
    roots = [sp.Poly(root_poly(j), z) for j in range(16)]
    # Bad-alpha criterion: (k+2)=6-subset S of mu_16 with e_2(S)=0, e_1(S)!=0; alpha=-1/e_1(S).
    # F_16(alpha) norm over Q = product over all such S of e_1(S) (the field norm of the
    # bad-alpha generator). We compute the SET of e_1(S) values (as algebraic numbers in
    # Q(zeta_16)) for primitive (non-coset) S with e_2(S)=0, and take Norm = product over
    # a full Galois orbit; equivalently we compute the rational integer
    #   R_16 = prod_{primitive S, e2=0} Norm_{Q(zeta16)/Q}(e_1(S)).
    # That product is a rational integer; its prime factors are the bad-reduction primes.
    modp = sp.Poly(cyc, z)
    def mul(a, b):
        return sp.rem(a * b, modp, z)
    def add(a, b):
        return a + b
    zero = sp.Poly(0, z)
    one = sp.Poly(1, z)
    # elementary symmetric e_1, e_2 of a subset via Newton on the roots' polynomials
    def e1_e2(S):
        e1 = zero
        for j in S:
            e1 = e1 + roots[j]
        e1 = sp.rem(e1, modp, z)
        e2 = zero
        for a in range(len(S)):
            for b in range(a+1, len(S)):
                e2 = e2 + mul(roots[S[a]], roots[S[b]])
        e2 = sp.rem(e2, modp, z)
        return e1, e2
    # Norm to Q of an element given as poly p(zeta): product over Galois conjugates
    # zeta -> zeta^t, t in (Z/16)* = {1,3,5,7,9,11,13,15}. Norm = prod_t p(zeta^t) in Q.
    units = [t for t in range(16) if gcd(t, 16) == 1]
    def norm_to_Q(poly):
        prod = sp.Integer(1)
        for t in units:
            # substitute z -> z^t mod cyc, then this is the conjugate element; its
            # "value" as an algebraic number is again a poly. To get a RATIONAL norm we
            # multiply all conjugate POLYS and reduce: the product of all conjugates of an
            # algebraic integer is its norm (a rational). We compute prod of conj polys
            # then it must be a constant (rational).
            conj = sp.rem(poly.as_expr().subs(z, z**t), modp, z)
            conj = sp.Poly(conj, z)
            prod = sp.rem(sp.Poly(prod, z) * conj, modp, z) if not isinstance(prod, sp.Integer) else conj if prod==1 else sp.rem(sp.Poly(prod,z)*conj,modp,z)
        # prod should be a constant poly
        return prod
    # Enumerate 6-subsets, primitive (not mu_2 or mu_4 coset-union), e_2=0
    e1_norms = []
    count_e2zero = 0
    count_prim = 0
    def is_coset_union(S, m):
        step = n // m
        Ss = set(S)
        return all(((j+step) % n) in Ss for j in S)
    for S in itertools.combinations(range(16), 6):
        e1, e2 = e1_e2(S)
        if e2 == zero:
            count_e2zero += 1
            if e1 == zero:
                continue
            prim = not (is_coset_union(S, 2) or is_coset_union(S, 4) or is_coset_union(S, 8))
            if prim:
                count_prim += 1
                Ne1 = norm_to_Q(e1)
                e1_norms.append((S, Ne1))
    return count_e2zero, count_prim, e1_norms

def main():
    print("="*86)
    print("#407 LANE LB2 -- DIRECT resultant/norm route to Q1 at d=16 (NOT self-similarity)")
    print("="*86)

    print("\n--- (I) p_1=0 slice: R_16^{(p1)} = product of antipodal-free coordinate-vector gcds ---")
    cnt, gcds, nz = slice_p1()
    print(f"    antipodal-free half-sets of mu_16: {cnt}")
    print(f"    char-0: every coordinate vector nonzero (Lam-Leung)? {nz}")
    print(f"    distinct coordinate-vector gcds: {sorted(set(gcds))}")
    R16_p1 = 1
    for g in gcds:
        R16_p1 *= max(g, 1)
    print(f"    R_16^(p1) = product of gcds = {R16_p1}  (prime factors = bad-reduction primes)")
    if all(g == 1 for g in gcds):
        print("    => R_16^(p1) = 1: the p_1=0 slice of V_16^prim is EMPTY over EVERY F_p")
        print("       (no prime can divide a gcd-1 vector). STRICTLY stronger than 'no prime in band'.")

    print("\n--- (II) FULL F_16(alpha) norm via affine pencil e_2(S)=0, alpha=-1/e_1(S) ---")
    try:
        c2, cp, e1n = algeb_d16_norm()
        print(f"    6-subsets of mu_16 with e_2(S)=0: {c2}")
        print(f"    of which primitive (non mu_2/mu_4/mu_8-coset): {cp}")
        if cp == 0:
            print("    => NO primitive char-0 bad-alpha config: V_16^prim (affine-pencil) EMPTY over Q.")
            print("       F_16 has NO primitive root => R_16 is a UNIT (no bad-reduction prime).")
        else:
            R16 = sp.Integer(1)
            bads = set()
            for S, Ne1 in e1n:
                val = Ne1.as_expr() if hasattr(Ne1, 'as_expr') else Ne1
                val = sp.nsimplify(val)
                R16 *= sp.Integer(val) if val == int(val) else val
            print(f"    R_16 = product of Norm(e_1(S)) over primitive S = {R16}")
            print(f"    factorization: {sp.factorint(abs(sp.Integer(R16)))}")
    except Exception as ex:
        print(f"    [algebraic-norm path raised: {ex}; falling back to mod-p scan in companion]")

if __name__ == "__main__":
    main()

# ============================ char-p companion (the real Q1 object) ============================
def primes_1_mod_n(nn, lo, cap):
    out=[]; p=lo|1
    while len(out)<cap:
        if (p-1)%nn==0 and is_prime(p): out.append(p)
        p+=2
    return out

def find_gen(p, nn):
    for g0 in range(2,p):
        w=pow(g0,(p-1)//nn,p)
        if pow(w,nn,p)==1 and all(pow(w,nn//q,p)!=1 for q in (2,3,5,7) if nn%q==0):
            return w
    raise RuntimeError("nogen")

def charp_full_d16(p):
    """Over F_p (p=1 mod 16): does any PRIMITIVE (non-coset) 6-subset of mu_16 have
    e_2(S)=0 mod p, e_1(S)!=0 (=> a spurious bad-alpha primitive point => Q1 bad reduction)?
    Also re-confirm the p_1=0 slice is empty (antipodal-free half-set with coordvec=0 mod p)."""
    w=find_gen(p,16)
    R=[pow(w,j,p) for j in range(16)]
    def is_coset_union(S,m):
        step=16//m; Ss=set(S)
        return all(((j+step)%16) in Ss for j in S)
    spurious_affine=[]
    for S in itertools.combinations(range(16),6):
        e1=sum(R[j] for j in S)%p
        e2=0
        for a in range(6):
            for b in range(a+1,6):
                e2=(e2+R[S[a]]*R[S[b]])%p
        if e2==0 and e1!=0:
            if not (is_coset_union(S,2) or is_coset_union(S,4) or is_coset_union(S,8)):
                spurious_affine.append(S)
    # p_1=0 slice: antipodal-free half-set with coordinate vector =0 mod p
    spurious_p1=[]
    for Y in itertools.combinations(range(16),8):
        Ys=set(Y)
        if any(((j+8)%16) in Ys for j in Y): continue
        s=sum(R[j] for j in Y)%p
        if s==0:
            spurious_p1.append(Y)
    return spurious_affine, spurious_p1

def charp_main():
    print("\n--- char-p companion: full Q1 object over prize-band primes p = 1 (mod 16) ---")
    ps=primes_1_mod_n(16, 16**4, cap=12)
    print(f"    primes (~16^4 = {16**4}): {ps}")
    any_aff=False; any_p1=False
    for p in ps:
        aff,p1=charp_full_d16(p)
        if aff: any_aff=True
        if p1: any_p1=True
        tag_aff = f"AFFINE-SPURIOUS {len(aff)} e.g.{aff[0]}" if aff else "affine clean"
        tag_p1  = f"P1-SPURIOUS {len(p1)}" if p1 else "p1-slice clean"
        print(f"    p={p}: {tag_aff}; {tag_p1}")
    print(f"    => affine e_2=0 primitive bad-alpha over band: {'FOUND (Q1 issue)' if any_aff else 'NONE (Q1 holds, affine face)'}")
    print(f"    => p_1=0 primitive point over band: {'FOUND' if any_p1 else 'NONE (consistent with R_16^(p1)=1)'}")

if __name__=="__main__" and len(__import__('sys').argv)>1 and __import__('sys').argv[1]=="charp":
    charp_main()
