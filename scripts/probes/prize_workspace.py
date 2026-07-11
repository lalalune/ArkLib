"""
prize_workspace.py — UNIFIED guess-and-check harness for the Proximity Prize open core (#407).

Every "wall" (BGK char-sum M, BCHKS subgroup subset-sum spread, Schur/higher-order-MDS minors,
Gauss-period spectrum, additive energy E_r, worst-case RS list = the floor) is the SAME family of
computable objects over (n, p, k, r). A conjecture is a Python predicate `f(W) -> bool` on a
Workspace W (all quantities precomputed/cached). `refute(name, f, grid)` runs it across a parameter
grid and returns the FIRST counterexample (with the offending W and the values) or None (survives).

Goal: state many reasonable theorems relating these quantities, refute fast, keep the survivors.
Then attack survivors deeply to UNIFY the walls and pin delta*.

Usage:
    from prize_workspace import Workspace, refute, grid_default, REFERENCE_CONJECTURES
    W = Workspace(n=16, p=4129)            # mu_16 in F_4129
    W.M, W.Er(3), W.cumulant(3), W.subset_sum_card(3), W.worst_list(k=4, delta=0.5)
    refute("M_le_2sqrt", lambda W: W.M <= 2*(W.n*math.log(W.p))**0.5, grid_default())

Run `python prize_workspace.py` for self-tests + the reference conjecture sweep.
"""
import math, itertools, functools
import numpy as np

# ----------------------------------------------------------------------------- number theory
def isprime(m):
    if m < 2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37):
        if m % q == 0: return m == q
    d = m-1; s=0
    while d % 2 == 0: d//=2; s+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x = pow(a, d, m)
        if x in (1, m-1): continue
        for _ in range(s-1):
            x = x*x % m
            if x == m-1: break
        else: return False
    return True

def prime_factors(m):
    s=set(); d=2
    while d*d<=m:
        while m%d==0: s.add(d); m//=d
        d+=1
    if m>1: s.add(m)
    return s

def find_prime(n, target_index, hi=None):
    """smallest prime p = n*m+1 with m >= target_index (so mu_n exists, index ~ m)."""
    hi = hi or target_index*20
    for m in range(target_index, hi):
        p = n*m+1
        if isprime(p): return p
    return None

def subgroup(p, n):
    """the order-n multiplicative subgroup mu_n of F_p (n | p-1), as a sorted list."""
    assert (p-1) % n == 0, f"{n} does not divide {p}-1"
    e = (p-1)//n; pf = prime_factors(n)
    for c in range(2, p):
        h = pow(c, e, p)
        if pow(h, n, p) != 1: continue
        if any(pow(h, n//q, p) == 1 for q in pf): continue
        S=set(); x=1
        for _ in range(n): x = x*h % p; S.add(x)
        if len(S) == n: return sorted(S)
    raise RuntimeError(f"no order-{n} subgroup in F_{p}")

# ----------------------------------------------------------------------------- the Workspace
class Workspace:
    """All prize quantities for fixed (n, p), lazily computed and cached."""
    def __init__(self, n, p):
        self.n = n; self.p = p
        self.S = subgroup(p, n)                 # mu_n
        self.rho_default = None
        self._eta = None                        # Gauss-period spectrum (complex, length p)
        self._mag2 = None                       # |eta_b|^2
        self._ss = {1: set(self.S)}             # subset-sum sets cache

    # --- Gauss periods / character sums (the BGK face) ---
    @property
    def eta(self):
        if self._eta is None:
            ind = np.zeros(self.p, dtype=float)
            for x in self.S: ind[x] = 1.0
            self._eta = np.fft.fft(ind)         # eta_b = sum_{x in mu_n} e_p(b*x)
            self._mag2 = np.abs(self._eta)**2
        return self._eta
    @property
    def mag2(self):
        if self._mag2 is None: _ = self.eta
        return self._mag2
    @property
    def M(self):
        """worst-case incomplete char sum M = max_{b!=0} |eta_b|  (the BGK/Paley object)."""
        return float(np.sqrt(self.mag2[1:].max()))
    @property
    def M_over_sqrt_n(self): return self.M / math.sqrt(self.n)

    # --- additive energy / cumulant (the moment face) ---
    @functools.lru_cache(maxsize=None)
    def Er(self, r):
        """r-fold additive energy E_r(mu_n) = #{sum x = sum y, x,y in mu_n^r} = (1/p) sum_b |eta_b|^{2r}."""
        return float((self.mag2 ** r).sum() / self.p)
    @functools.lru_cache(maxsize=None)
    def cumulant(self, r):
        """C_r = sum_{b!=0} |eta_b|^{2r} = p*E_r - n^{2r}  (the connected/prize part)."""
        return float(self.mag2[1:].__pow__(r).sum())
    def excess(self, r):
        """E_r - n^{2r}/p = C_r/p  (excess over equidistribution baseline)."""
        return self.cumulant(r)/self.p
    @staticmethod
    def wick(r, n):
        """the char-0 Wick value (2r-1)!! n^r."""
        df = 1
        for j in range(1, 2*r, 2): df *= j
        return df * n**r

    # --- subgroup subset-sums (the BCHKS face) ---
    @functools.lru_cache(maxsize=None)
    def subset_sum_card(self, r):
        """|mu_n^{(+r)}| = #distinct r-fold sums x_1+...+x_r mod p, x_i in mu_n (BCHKS spreading).
        numpy sumset via boolean membership vector; early-stops at saturation (=p)."""
        Sarr = np.array(self.S, dtype=np.int64)
        vec = np.zeros(self.p, dtype=bool); vec[Sarr] = True   # membership of current sumset
        for _ in range(r-1):
            cur = np.nonzero(vec)[0]
            new = (cur[:, None] + Sarr[None, :]).ravel() % self.p
            nv = np.zeros(self.p, dtype=bool); nv[new] = True
            if nv.sum() == self.p: return self.p                # saturated, can't grow
            vec = nv
        return int(vec.sum())

    # --- worst-case list / generalized-Singleton (the floor / higher-order-MDS face) ---
    MAX_CODEWORDS = 2_000_000   # the list/MDS face enumerates p^k; only feasible for SMALL p
    def codewords(self, k):
        if self.p ** k > self.MAX_CODEWORDS:
            raise ValueError(f"p^k={self.p}^{k} too large to enumerate; use a small-p workspace "
                             f"(e.g. get_W(8,17)) for the list/MDS face")
        Cs = np.array(list(itertools.product(range(self.p), repeat=k)), dtype=np.int64)
        Xp = np.array([[pow(x, j, self.p) for j in range(k)] for x in self.S], dtype=np.int64)
        return (Cs @ Xp.T) % self.p             # (p^k, n)
    def worst_list(self, k, delta, nsamp=8000, seed=0):
        """worst-case RS[mu_n,k] list size at radius delta (sampled centers: codewords+random+merges).
        NOTE: needs a SMALL-p workspace (enumerates p^k codewords)."""
        r = int(delta * self.n)
        C = self.codewords(k); rng = np.random.default_rng(seed); m = len(C)
        rand = rng.integers(0, self.p, size=(nsamp, self.n))
        idx = rng.integers(0, m, size=(nsamp, 2)); msk = rng.random((nsamp, self.n)) < 0.5
        mer = np.where(msk, C[idx[:,0]], C[idx[:,1]])
        Wd = np.unique(np.concatenate([C, rand, mer], axis=0), axis=0)
        best = 0
        for i in range(0, len(Wd), 400):
            d = (Wd[i:i+400][:,None,:] != C[None,:,:]).sum(2)
            best = max(best, int((d <= r).sum(1).max()))
        return best

    # --- regime constants ---
    def johnson(self, k): return 1 - math.sqrt(k/self.n)
    def capacity(self, k): return 1 - k/self.n
    def window_edge(self, k, budget=None):
        """1 - rho - H(rho)/log2(budget); budget defaults to n (prize q*eps*~n)."""
        rho = k/self.n; budget = budget or self.n
        H = -rho*math.log2(rho) - (1-rho)*math.log2(1-rho) if 0<rho<1 else 0.0
        return 1 - rho - H/math.log2(max(budget,2))

    def __repr__(self): return f"W(n={self.n},p={self.p},M/sqrtn={self.M_over_sqrt_n:.2f})"

# cache workspaces (subgroup + FFT are the expensive bits)
@functools.lru_cache(maxsize=256)
def get_W(n, p): return Workspace(n, p)

# ----------------------------------------------------------------------------- refutation driver
def grid_default(ns=(8,16,32,64,128), indices=(16,64,256,1024), require_odd_part=False, pmax=300000):
    """list of (n,p) workspace params spanning generic + structured primes."""
    out=[]
    for n in ns:
        for idx in indices:
            p = find_prime(n, idx)
            if p is None or p > pmax: continue
            out.append((n, p))
    return out

def refute(name, conj, grid=None, rs=(1,2,3,4,5), ks=None, verbose=False):
    """Run conjecture `conj(W, **ctx)` over grid; return first counterexample dict or None (survives).
    `conj` may take (W,) or (W, r) or (W, k) or (W, r, k) — introspected by arg count via try."""
    grid = grid or grid_default()
    import inspect
    sig = inspect.signature(conj); nargs = len(sig.parameters)
    for (n, p) in grid:
        try: W = get_W(n, p)
        except Exception: continue
        combos = [()]
        if nargs >= 2: combos = [(r,) for r in rs]
        if ks is not None and nargs >= 3: combos = [(r,k) for r in rs for k in (ks if isinstance(ks,(list,tuple)) else [ks])]
        for c in combos:
            try:
                ok = conj(W, *c)
            except Exception as e:
                if verbose: print(f"  [{name}] error at n={n},p={p},c={c}: {e}")
                continue
            if not ok:
                return {"name":name, "n":n, "p":p, "args":c, "W":repr(W)}
    return None

# ----------------------------------------------------------------------------- reference conjectures
# (name, predicate, status) — the KNOWN ones, as sanity checks + templates for agents.
REFERENCE_CONJECTURES = [
    # BGK face: the prize target. C=2 should SURVIVE (refutation-tested in-tree); C=sqrt2 should REFUTE.
    ("M_le_2_sqrt_nlogp",  lambda W: W.M <= 2*math.sqrt(W.n*math.log(W.p)),                 "expect SURVIVE (C=2 in-tree)"),
    ("M_le_sqrt2_sqrt_nlogp", lambda W: W.M <= math.sqrt(2*W.n*math.log(W.p)),              "expect REFUTE (C=sqrt2 refuted)"),
    # cumulant sub-Wick: SURVIVES generically, REFUTES at structured (Fermat-like) primes.
    ("cumulant_sub_wick",  lambda W,r: W.excess(r) <= Workspace.wick(r, W.n),               "expect REFUTE (structured primes)"),
    # energy Wick bound at fixed r (char-0 value): should hold for large p.
    ("Er_le_wick",         lambda W,r: W.Er(r) <= Workspace.wick(r, W.n) + W.n**(2*r)/W.p,  "expect SURVIVE (random+diag)"),
    # moment method can't beat trivial n: (p*E_r)^{1/2r} >= ~n  (NO-GO, should SURVIVE).
    ("moment_ge_n",        lambda W,r: (W.p*W.Er(r))**(1/(2*r)) >= 0.9*W.n,                  "expect SURVIVE (moment no-go)"),
    # BCHKS subset-sum spreads: |mu_n^{(+r)}| grows (anti-floor); at r=3 should already be large.
    ("subset_sum_small",   lambda W,r: W.subset_sum_card(r) <= W.n,                          "expect REFUTE (subset-sums spread)"),
]

if __name__ == "__main__":
    import sys
    print("=== prize_workspace self-test ===")
    W = get_W(16, find_prime(16, 64))           # large p: char-sum/energy/subset-sum face
    print(f"  {W}  E2={W.Er(2):.0f} (3n^2-3n={3*16*16-3*16}) M/sqrtn={W.M_over_sqrt_n:.2f}")
    print(f"  cumulant(3)/wick(3) = {W.excess(3)/Workspace.wick(3,16):.3f}  subset_sum_card(3)={W.subset_sum_card(3)} (n={W.n}, p={W.p})")
    Wsmall = get_W(8, 17)                        # small p: list/MDS face
    print(f"  small-p {Wsmall}: worst_list(k=2,delta=0.625)={Wsmall.worst_list(2,0.625)}  "
          f"johnson={Wsmall.johnson(2):.3f} window_edge={Wsmall.window_edge(2):.3f}")
    print("\n=== reference conjecture sweep ===")
    g = grid_default()
    for name, conj, status in REFERENCE_CONJECTURES:
        cx = refute(name, conj, g)
        verdict = "SURVIVES" if cx is None else f"REFUTED at n={cx['n']},p={cx['p']},args={cx['args']}"
        print(f"  {name:28} -> {verdict:42} [{status}]")
