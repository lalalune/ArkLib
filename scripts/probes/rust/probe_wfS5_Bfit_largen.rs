// wf-S5 DECISIVE B-FIT: extend the EXACT folded-theta short-vector count of the index-p
// sublattice L_P to n=64,128 and fit the per-shell geometric base B from N_w <= A*B^w.
// The lane's reduction (axiom-clean, _wfS5_theta_count_wick.lean) gives K = B^2, so the prize
// energy bound E_r <= K^r (2r-1)!! n^r holds with ABSOLUTE K iff B(n) stays bounded as n->2^30.
//
// We report, per n (worst over a batch of prize primes p == 1 mod n, p ~ n^4):
//   - girth  gamma = min{w>=1 : N_w>0}  (INFINITY-coded as cap+1 when no spur in range)
//   - the per-shell geometric base  B = max_{1<=w<=cap, N_w>0} N_w^{1/w}   (A=1 fit)
//   - the SMOOTHED base over the active window  B_sm = (sum_w N_w)^{1/cap}  (cumulative rate)
//   - the peak energy ratio  R* = max_r cumN(<=2r)/(2r-1)!!  (the actual prize multiplier)
//   - K = B^2 (the lane's energy constant)
//
// DECISIVE: if B(n) and R*(n) saturate -> K bounded -> PROVEN-AT-PRIZE (mod shell-law proof).
//   If they grow polynomially in n -> K unbounded at structured primes -> CONCENTRATION needed.
//
// Memory-bounded meet-in-middle: half-tables keyed by residue, cap kept small at large n.

use std::collections::HashMap;

fn mpow(a: u64, mut e: u64, p: u64) -> u64 {
    let mut r: u128 = 1; let mut a2 = a as u128; let pp = p as u128;
    while e > 0 { if e & 1 == 1 { r = r * a2 % pp; } a2 = a2 * a2 % pp; e >>= 1; }
    r as u64
}
fn isp(n: u64) -> bool { if n < 2 { return false } let mut d = 2u64; while d*d <= n { if n%d==0 {return false} d+=1 } true }
fn next_prime_1mod(n: u64, mut p: u64) -> u64 {
    if p % n != 1 { p += (n + 1 - p % n) % n; }
    loop { if p > 2 && isp(p) { return p } p += n; }
}
fn proot(p: u64) -> u64 {
    let mut m = p - 1; let mut fs = vec![]; let mut d = 2u64;
    while d*d <= m { if m%d==0 { fs.push(d); while m%d==0 {m/=d} } d+=1 }
    if m > 1 { fs.push(m) }
    let mut g = 2u64;
    loop { if fs.iter().all(|&f| mpow(g,(p-1)/f,p)!=1) { return g } g+=1 }
}
// folded power basis: g^0..g^{d-1}, d=phi(n)=n/2 (zeta^d = -1 reduces sign automatically over Z)
fn power_basis(p: u64, n: u64) -> Vec<u64> {
    let g0 = proot(p);
    let h = mpow(g0, (p-1)/n, p);
    let d = (n/2) as usize;
    (0..d).map(|j| mpow(h, j as u64, p)).collect()
}
// tables[w]: residue -> #coeff vectors over gens with L1 weight EXACTLY w (w=0 -> {0:1})
fn half_tables(gens: &[u64], p: u64, cap: usize) -> Vec<HashMap<u64,u64>> {
    let mut dp: Vec<HashMap<u64,u64>> = (0..=cap).map(|_| HashMap::new()).collect();
    dp[0].insert(0u64, 1u64);
    for &g in gens {
        let mut ndp: Vec<HashMap<u64,u64>> = (0..=cap).map(|_| HashMap::new()).collect();
        for w in 0..=cap {
            for (&res,&cnt) in &dp[w] {
                *ndp[w].entry(res).or_insert(0) += cnt;
                let mut add = 0u64;
                for k in 1..=(cap-w) {
                    add = (add + g) % p;
                    let rp = (res + add) % p;
                    let rm = (res + p - add) % p;
                    *ndp[w+k].entry(rp).or_insert(0) += cnt;
                    *ndp[w+k].entry(rm).or_insert(0) += cnt;
                }
            }
        }
        dp = ndp;
    }
    dp
}
fn dfact(r: usize) -> f64 { let mut v=1.0; for j in 1..=r { v *= (2*j-1) as f64 } v }

// EXACT shells[0..=cap]; shells[0] is the zero vector (excluded from girth/B), shells[w>=1] are spur.
fn theta_shells(n: u64, p: u64, cap: usize) -> Vec<u64> {
    let gens = power_basis(p, n);
    let d = (n/2) as usize;
    let half = d/2;
    let tl = half_tables(&gens[..half], p, cap);
    let tr = half_tables(&gens[half..], p, cap);
    let mut shells = vec![0u64; cap+1];
    for w in 0..=cap {
        let mut total: u64 = 0;
        for wl in 0..=w {
            let wr = w-wl;
            for (&rl,&cl) in &tl[wl] {
                let need = (p - rl) % p;
                if let Some(&cr) = tr[wr].get(&need) { total += cl*cr; }
            }
        }
        shells[w] = total;
    }
    // remove the single zero vector counted at w=0
    shells[0] = shells[0].saturating_sub(1);
    shells
}

// (girth, B=max N_w^{1/w}, R*, rstar_r)
fn metrics(shells: &[u64], cap: usize) -> (usize, f64, f64, usize) {
    let girth = (1..=cap).find(|&w| shells[w] > 0).unwrap_or(cap+1);
    let mut bmax = 0.0f64;
    for w in 1..=cap {
        if shells[w] > 0 {
            let b = (shells[w] as f64).powf(1.0/w as f64);
            if b > bmax { bmax = b; }
        }
    }
    let mut cum: u64 = 0;
    let (mut rstar, mut rr) = (0.0f64, 0usize);
    for w in 1..=cap {
        cum += shells[w];
        if w%2==0 {
            let r = w/2;
            let ratio = cum as f64 / dfact(r);
            if ratio > rstar { rstar = ratio; rr = r; }
        }
    }
    (girth, bmax, rstar, rr)
}

fn scan_n(n: u64, cap: usize, nprimes: usize) {
    let d = n/2;
    let mut p = next_prime_1mod(n, n.pow(4));
    let beta = (p as f64).ln()/(n as f64).ln();
    let (mut wg, mut wg_p) = (usize::MAX, 0u64);     // worst (min) girth
    let (mut wb, mut wb_p) = (0.0f64, 0u64);         // worst (max) B
    let (mut wr, mut wr_p, mut wr_r) = (0.0f64, 0u64, 0usize); // worst R*
    let mut nospur = 0usize;
    for _ in 0..nprimes {
        let shells = theta_shells(n, p, cap);
        let (g,b,rs,rr) = metrics(&shells, cap);
        if g == cap+1 { nospur += 1; } else if g < wg { wg = g; wg_p = p; }
        if b > wb { wb = b; wb_p = p; }
        if rs > wr { wr = rs; wr_p = p; wr_r = rr; }
        p = next_prime_1mod(n, p+1);
    }
    let girth_str = if wg==usize::MAX { format!("(all {} primes spur-free in range)", nprimes) }
                    else { format!("{} @ p={} ({} spur-free)", wg, wg_p, nospur) };
    println!("n={:>5} d={:>4} beta~{:.2} cap={} primes={}", n, d, beta, cap, nprimes);
    println!("   worst girth  gamma = {}", girth_str);
    println!("   worst B (shell base) = {:.4} @ p={}   => K=B^2 = {:.4}", wb, wb_p, wb*wb);
    println!("   peak energy ratio R* = {:.4} @ p={} (r={})", wr, wr_p, wr_r);
    println!();
}

fn main() {
    println!("# wf-S5 DECISIVE B-fit: does the index-p theta shell base B(n) stay bounded as n->2^30?");
    println!("# EXACT folded L1-theta, meet-in-middle, prize p~n^4, p==1 mod n. K=B^2 (lane reduction).\n");
    scan_n(8,   14, 60);
    scan_n(16,  14, 60);
    scan_n(32,  12, 40);
    scan_n(64,  10, 20);
    scan_n(128,  8, 8);
    println!("# READ: B(n) and R*(n). Bounded -> K absolute -> PROVEN-AT-PRIZE(mod shell law).");
    println!("# Growing in n -> K unbounded at structured primes -> CONCENTRATION needed.");
}
