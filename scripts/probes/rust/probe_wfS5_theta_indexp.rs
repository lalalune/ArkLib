// wf-S5: THETA-SERIES short-vector count of the index-p sublattice L_P of the 2-power
// cyclotomic lattice, at PRIZE SCALE (p ~ n^beta, p == 1 mod n).
//
// SETUP (power basis -- the HONEST embedding, no trivial antipodal weight-2 vectors).
//   K = Q(zeta_n), n = 2^mu.  O_K = Z[zeta], rank d = phi(n) = n/2, power basis 1,zeta,..,zeta^{d-1}
//   with the single relation zeta^d = -1 (Phi_n = x^d + 1).  A cyclotomic integer is c in Z^d.
//   p == 1 mod n is FULLY SPLIT; fix a degree-1 prime P|p via zeta -> g, g primitive n-th root in F_p.
//   Reduction c |-> sum_j c_j g^j (mod p).  L_P := { c in Z^d : sum c_j g^j == 0 mod p } is an
//   INDEX-p sublattice of Z^d.  covol(L_P)=p, so Minkowski lambda_1 ~ sqrt(d)*p^{1/d} = O(sqrt d):
//   SHORT VECTORS EXIST regardless of p -> the COUNT is the question (the lane's thesis).
//
// SPUR CONFIGS as short vectors.  A spurious config sigma_T = sum_{i in T} eps_i zeta^i, |T|<=2r,
// eps in {+-1}, with sigma_T == 0 mod p, != 0 over Z.  In the power basis zeta^i = (+/-) e_{i mod d}
// (since zeta^d=-1), so a weight-w signed-root config is c in Z^d with L1 weight ||c||_1 <= w.
//
// We compute EXACTLY the L1-theta of L_P:  N_w(p) := #{ c in Z^d : ||c||_1 = w, sum c_j g^j == 0
// mod p, c != 0 }.  Headline: GIRTH gamma = min such w, and cumulative C_<=2r vs Wick (2r-1)!!,
// to test whether the short-vector count stays K^r-bounded or inflates at structured prize primes.
//
// METHOD: exact meet-in-the-middle over the d generators (split into two halves). For each half
// enumerate every coefficient vector of L1 weight <= cap, record (weight,residue)->count, then
// merge halves requiring residues to sum to 0 mod p. Exact integer counts, no floating point.

use std::collections::HashMap;

fn mpow(a: u64, mut e: u64, p: u64) -> u64 {
    let mut r: u128 = 1; let mut a2 = a as u128; let pp = p as u128;
    while e > 0 { if e & 1 == 1 { r = r * a2 % pp; } a2 = a2 * a2 % pp; e >>= 1; }
    r as u64
}
fn isp(n: u64) -> bool { if n < 2 { return false } let mut d = 2; while d * d <= n { if n % d == 0 { return false } d += 1 } true }
fn fp(n: u64, lo: u64) -> u64 {
    let mut p = lo + ((n + 1 - lo % n) % n);
    if p % n != 1 { p += (n + 1 - p % n) % n; }
    loop { if p % n == 1 && p > 2 && isp(p) { return p } p += n; }
}
fn proot(p: u64) -> u64 {
    let mut m = p - 1; let mut fs = vec![]; let mut d = 2;
    while d * d <= m { if m % d == 0 { fs.push(d); while m % d == 0 { m /= d } } d += 1 }
    if m > 1 { fs.push(m) }
    let mut g = 2u64;
    loop { if fs.iter().all(|&f| mpow(g, (p - 1) / f, p) != 1) { return g } g += 1 }
}
fn power_basis(p: u64, n: u64) -> Vec<u64> {
    let g0 = proot(p);
    let h = mpow(g0, (p - 1) / n, p);
    let d = (n / 2) as usize;
    (0..d).map(|j| mpow(h, j as u64, p)).collect()
}

// Enumerate all coefficient vectors over `gens` with total L1 weight <= cap.
// Returns tables[w] : residue -> count of vectors with L1 weight EXACTLY w.
// (Includes the zero vector at w=0.)
fn half_tables(gens: &[u64], p: u64, cap: usize) -> Vec<HashMap<u64, u64>> {
    let mut tables: Vec<HashMap<u64, u64>> = (0..=cap).map(|_| HashMap::new()).collect();
    tables[0].insert(0u64, 1u64);
    // current frontier: HashMap<residue, count> at each weight, built generator by generator.
    // dp[(w, res)] = #vectors over processed generators. Process incrementally.
    let mut dp: Vec<HashMap<u64, u64>> = (0..=cap).map(|_| HashMap::new()).collect();
    dp[0].insert(0u64, 1u64);
    for &g in gens {
        let mut ndp: Vec<HashMap<u64, u64>> = (0..=cap).map(|_| HashMap::new()).collect();
        for w in 0..=cap {
            for (&res, &cnt) in &dp[w] {
                // c_j = 0
                *ndp[w].entry(res).or_insert(0) += cnt;
                // c_j = +k / -k, k>=1, w+k<=cap
                let mut add = 0u64;
                for k in 1..=(cap - w) {
                    add = (add + g) % p;
                    let rp = (res + add) % p;
                    let rm = (res + p - add) % p;
                    *ndp[w + k].entry(rp).or_insert(0) += cnt;
                    *ndp[w + k].entry(rm).or_insert(0) += cnt;
                }
            }
        }
        dp = ndp;
    }
    for w in 0..=cap { tables[w] = std::mem::take(&mut dp[w]); }
    tables
}

fn dfact(r: usize) -> f64 { let mut v = 1.0; for j in 1..=r { v *= (2 * j - 1) as f64 } v }
fn lnfact(d: usize) -> f64 { let mut s = 0.0; for j in 2..=d { s += (j as f64).ln() } s }

fn run(n: u64, p: u64, cap: usize) {
    let gens = power_basis(p, n);
    let d = (n / 2) as usize;
    let beta = (p as f64).ln() / (n as f64).ln();
    let half = d / 2;
    let tl = half_tables(&gens[..half], p, cap);
    let tr = half_tables(&gens[half..], p, cap);
    // N_w = #{c : ||c||_1 = w, residue 0} - (zero vector if w=0)
    let mut shells = vec![0u64; cap + 1];
    for w in 1..=cap {
        let mut total: u64 = 0;
        for wl in 0..=w {
            let wr = w - wl;
            for (&rl, &cl) in &tl[wl] {
                let need = (p - rl) % p;
                if let Some(&cr) = tr[wr].get(&need) { total += cl * cr; }
            }
        }
        shells[w] = total;
    }
    // GH/Minkowski L1 first-minimum estimate: smallest w with (2w)^d/d! >= p
    let mut w_gh = 0usize;
    for w in 1..200 {
        let lc = (d as f64) * (2.0 * w as f64).ln() - lnfact(d);
        if lc >= (p as f64).ln() { w_gh = w; break; }
    }
    let girth = (1..=cap).find(|&w| shells[w] > 0).unwrap_or(0);
    println!("== n={} d=phi={} p={} beta={:.2} ==", n, d, p, beta);
    print!("   L1-theta shell N_w (w=1..{}): ", cap);
    for w in 1..=cap { print!("{} ", shells[w]); }
    println!();
    println!("   GIRTH gamma(L_P) = {}   (GH/Minkowski w_GH ~ {})", girth, w_gh);
    println!("   r | 2r | cum N(<=2r) | Wick (2r-1)!! | cum/Wick | K:=(cum)^(1/r)");
    let mut cum: u64 = 0;
    for w in 1..=cap {
        cum += shells[w];
        if w % 2 == 0 {
            let r = w / 2;
            let wick = dfact(r);
            let ratio = if wick > 0.0 { cum as f64 / wick } else { 0.0 };
            let kr = if cum > 0 { (cum as f64).powf(1.0 / r as f64) } else { 0.0 };
            println!("   {} | {} | {} | {:.0} | {:.3} | {:.3}", r, w, cum, wick, ratio, kr);
        }
    }
    println!();
}

fn main() {
    println!("# wf-S5: theta / short-vector count of index-p sublattice L_P, PRIZE SCALE p~n^4");
    println!("# (power basis Z^d, d=n/2; EXACT L1-shell sizes of L_P = ker(zeta->g mod p))\n");
    run(8,  fp(8,  8u64.pow(4)),  10);
    run(16, fp(16, 16u64.pow(4)), 10);
    run(32, fp(32, 32u64.pow(4)), 8);
    println!("# uniformity over prize primes at n=16 (beta~4):");
    let mut lo = 16u64.pow(4);
    for _ in 0..6 { let p = fp(16, lo); run(16, p, 8); lo = p + 1; }

    // ---- wf-S5 FINDINGS (the K-growth dichotomy; deep r, worst primes) ----
    // Worst-case K = (cumN<=2r)^(1/r) measured per shell. KEY RESULT:
    //   n=16: K_worst<=2.70 (Fermat p=65537); ratio cumN/Wick PEAKS r=3 (1.07) then DECAYS
    //         (0.30,0.15,0.017,0.003): Wick (2r-1)!! OVERTAKES geometric shell growth. K BOUNDED.
    //   n=32: K_worst~=4.5 at r=7 (p=1086913); ratio peaks r=3 (2.13) then decays SLOWER
    //         (0.61,0.71,0.49,0.27): still <1 for r>=4 (Wick dominates) but K rose 2.70->4.50.
    // => Energy ratio cumN/Wick is BOUNDED (<1 for r>=4 both n) BUT the normalized rate K is NOT
    //    yet uniform across n (2.70 -> 4.50). DICHOTOMY: structured primes inflate the COUNT but
    //    Wick still dominates per-r. The open question is whether K(n) is bounded as n->2^30.
    println!("\n# wf-S5 DEEP K-vs-r for WORST primes (does Wick overtake? is K bounded across n?):");
    run(16, 65537,   16); // Fermat n=16 worst, deep
    run(32, 1086913, 12); // n=32 worst-K prime from 200-prime scan
    run(32, 1065601, 12);
}
