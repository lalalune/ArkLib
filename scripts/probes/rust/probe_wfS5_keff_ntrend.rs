// wf-S5 EXTENSION: the K(n) / peak-ratio trend of the index-p sublattice L_P theta count,
// pushed to LARGER n (the open question: does the normalized short-vector rate stay bounded
// as n -> 2^30, or does it grow?).  PRIZE SCALE p ~ n^4, p == 1 mod n.
//
// Two drivers of the worst-case energy ratio cumN(<=2r)/Wick(2r-1)!!:
//   (1) GIRTH gamma = first nonzero theta shell (smallest spur weight). Larger girth => later
//       onset => smaller ratio. Char-0 girth is INFINITY (no real spur); char-p girth is finite.
//   (2) the PEAK ratio R*(n) := max_r cumN(<=2r)/Wick. At n=16 R*=1.07 (r=3), n=32 R*=2.13 (r=3).
//       If R*(n) grows polynomially in n the energy bound E_r<=K^r*Wick*n^r FAILS (K unbounded);
//       if R*(n) saturates the lane's geometric-shell law holds at the prize.
//
// We MEET-IN-THE-MIDDLE the EXACT folded L1-theta (no float). For each n we scan a batch of
// prize primes p == 1 mod n, p ~ n^4, and report: girth distribution, the WORST peak-ratio R*,
// and the worst K = (cumN)^{1/r}. d=phi(n)=n/2; half=d/2 generators per side; cap kept small so
// the half enumeration (sum_{w<=cap} 2^w C(half,?) ~ manageable) stays exact and fast.

use std::collections::HashMap;

fn mpow(a: u64, mut e: u64, p: u64) -> u64 {
    let mut r: u128 = 1; let mut a2 = a as u128; let pp = p as u128;
    while e > 0 { if e & 1 == 1 { r = r * a2 % pp; } a2 = a2 * a2 % pp; e >>= 1; }
    r as u64
}
fn isp(n: u64) -> bool { if n < 2 { return false } let mut d = 2u64; while d * d <= n { if n % d == 0 { return false } d += 1 } true }
// next prime >= lo with p == 1 mod n
fn next_prime_1mod(n: u64, mut p: u64) -> u64 {
    if p % n != 1 { p += (n + 1 - p % n) % n; }
    loop { if p > 2 && isp(p) { return p } p += n; }
}
fn proot(p: u64) -> u64 {
    let mut m = p - 1; let mut fs = vec![]; let mut d = 2u64;
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

// tables[w]: residue -> #coeff vectors over `gens` with L1 weight EXACTLY w (incl zero at w=0).
fn half_tables(gens: &[u64], p: u64, cap: usize) -> Vec<HashMap<u64, u64>> {
    let mut dp: Vec<HashMap<u64, u64>> = (0..=cap).map(|_| HashMap::new()).collect();
    dp[0].insert(0u64, 1u64);
    for &g in gens {
        let mut ndp: Vec<HashMap<u64, u64>> = (0..=cap).map(|_| HashMap::new()).collect();
        for w in 0..=cap {
            for (&res, &cnt) in &dp[w] {
                *ndp[w].entry(res).or_insert(0) += cnt;
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
    dp
}

fn dfact(r: usize) -> f64 { let mut v = 1.0; for j in 1..=r { v *= (2 * j - 1) as f64 } v }

// returns (shells[1..=cap], girth)
fn theta_shells(n: u64, p: u64, cap: usize) -> (Vec<u64>, usize) {
    let gens = power_basis(p, n);
    let d = (n / 2) as usize;
    let half = d / 2;
    let tl = half_tables(&gens[..half], p, cap);
    let tr = half_tables(&gens[half..], p, cap);
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
    let girth = (1..=cap).find(|&w| shells[w] > 0).unwrap_or(0);
    (shells, girth)
}

// peak ratio R* = max_r cumN(<=2r)/Wick, worst K = (cumN)^{1/r}, over r with 2r<=cap.
fn metrics(shells: &[u64], cap: usize) -> (f64, usize, f64, usize) {
    let mut cum: u64 = 0;
    let (mut rstar, mut rstar_r) = (0.0f64, 0usize);
    let (mut kworst, mut kworst_r) = (0.0f64, 0usize);
    for w in 1..=cap {
        cum += shells[w];
        if w % 2 == 0 {
            let r = w / 2;
            let wick = dfact(r);
            let ratio = cum as f64 / wick;
            if ratio > rstar { rstar = ratio; rstar_r = r; }
            if cum > 0 {
                let k = (cum as f64).powf(1.0 / r as f64);
                if k > kworst { kworst = k; kworst_r = r; }
            }
        }
    }
    (rstar, rstar_r, kworst, kworst_r)
}

fn scan_n(n: u64, cap: usize, nprimes: usize) {
    let d = n / 2;
    let mut p = next_prime_1mod(n, n.pow(4));
    let beta = (p as f64).ln() / (n as f64).ln();
    let mut worst_rstar = 0.0f64; let mut worst_rstar_p = 0u64; let mut worst_rstar_r = 0usize;
    let mut worst_k = 0.0f64; let mut worst_k_p = 0u64; let mut worst_k_r = 0usize;
    let mut min_girth = usize::MAX; let mut min_girth_p = 0u64;
    let mut girth_hist: HashMap<usize, usize> = HashMap::new();
    for _ in 0..nprimes {
        let (shells, girth) = theta_shells(n, p, cap);
        *girth_hist.entry(girth).or_insert(0) += 1;
        if girth < min_girth { min_girth = girth; min_girth_p = p; }
        let (rstar, rr, k, kr) = metrics(&shells, cap);
        if rstar > worst_rstar { worst_rstar = rstar; worst_rstar_p = p; worst_rstar_r = rr; }
        if k > worst_k { worst_k = k; worst_k_p = p; worst_k_r = kr; }
        p = next_prime_1mod(n, p + 1);
    }
    let mut gh: Vec<(usize,usize)> = girth_hist.into_iter().collect();
    gh.sort();
    println!("n={:>5} d={:>4} beta~{:.2} cap={} primes={}", n, d, beta, cap, nprimes);
    println!("   girth dist (g:count): {:?}   min girth {} @ p={}", gh, min_girth, min_girth_p);
    println!("   PEAK ratio R*(n) = {:.3} (at r={}, p={})", worst_rstar, worst_rstar_r, worst_rstar_p);
    println!("   worst  K(n)     = {:.3} (at r={}, p={})", worst_k, worst_k_r, worst_k_p);
    println!();
}

fn main() {
    println!("# wf-S5 K(n)/peak-ratio TREND — does the short-vector rate stay bounded as n grows?");
    println!("# folded L1-theta of L_P, EXACT meet-in-the-middle, prize p~n^4, p==1 mod n.\n");
    // cap = max L1-weight; r reaches up to cap/2. Keep cap modest so half-enum stays exact.
    scan_n(8,   12, 40);
    scan_n(16,  12, 40);
    scan_n(32,  12, 30);
    scan_n(64,  10, 16);
    scan_n(128,  8, 6);
    scan_n(256,  6, 3);
    println!("# READ: track PEAK ratio R*(n) across n=8,16,32,64,128,256. The ENERGY bound");
    println!("#   E_r <= K^r * Wick * n^r holds iff R*(n) (= max_r cumN/Wick) stays bounded.");
    println!("#   Growth in R*(n) => K unbounded => energy route FALSE at structured primes.");
}
