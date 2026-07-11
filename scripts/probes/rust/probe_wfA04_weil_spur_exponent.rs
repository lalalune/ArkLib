// #444 LANE A04 (S6 Weil-II): the EXACT Weil exponent of the spurious mass.
//
// spur_r(p) := E_r^charp(mu_n) - E_r^char0(mu_n) >= 0  is the char-p EXTRA additive-2r-energy.
// The S6 reduction (_wfS6_toric_config_betti.lean, axiom-clean) shows:
//   IF  spur_r(p) <= C(2r,r) * p^{r-1}   (SpurToricBounded)  THEN  K=4 absolute => prize via L3.
//
// A04 question: what is the ACTUAL Weil weight? Fit spur_r(p) ~ C_r(n) * p^{alpha_r}.
//   Adolphson-Sperber / Bombieri-Katz: V_r = {x in mu_n^{2r}: sum eps_i x_i = 0} is a
//   hyperplane slice of the 0-dim etale scheme mu_n^{2r}. The total Betti (Newton-polytope
//   monomial count of the linear form) is C(2r,r). Deligne/Weil-II => |#V_r - main| <= Betti * p^{w/2}
//   where w = top weight of the PRIMITIVE part.
//
// PRIZE-DECISIVE measurements (exact big-int, FFT-free histogram over n periods):
//   (1) alpha_r := d log spur / d log p  at fixed (n,r), beta in [3.5, 4.5].
//       If alpha_r <= r-1 AND C_r(n) <= C(2r,r) bounded in n  => SpurToricBounded HOLDS.
//   (2) The error-vs-char0 ratio at PRIZE DEPTH r ~ ln q: spur_r(p) / E_r^char0.
//       Weil route needs this -> 0 (or bounded) at r ~ ln p / ln n for the constant K.
//   (3) Whether spur=0 (faithful transfer) at the generic prize prime vs structured high-v2.
//
// EXACT ARITHMETIC throughout: p = 1 mod n prime, n = 2^a, residues mod p as u64/u128.
// E_r^charp = sum over residue classes of (#ways to write class as r-fold sum of mu_n)^2.
// E_r^char0 = same but counting EXACT complex-equal sums (reduced signed coeff vector, length n/2).

use std::collections::HashMap;

fn mpow(a: u64, mut e: u64, p: u64) -> u64 {
    let mut r: u128 = 1; let mut a2 = a as u128; let pp = p as u128;
    while e > 0 { if e & 1 == 1 { r = r * a2 % pp; } a2 = a2 * a2 % pp; e >>= 1; }
    r as u64
}
fn is_prime(n: u64) -> bool {
    if n < 2 { return false; }
    for &q in &[2u64,3,5,7,11,13,17,19,23,29,31,37] { if n % q == 0 { return n == q; } }
    let mut d = n - 1; let mut s = 0u32; while d & 1 == 0 { d >>= 1; s += 1; }
    'a: for &a in &[2u64,3,5,7,11,13,17,19,23,29,31,37] {
        let mut x = mpow(a, d, n);
        if x == 1 || x == n - 1 { continue; }
        for _ in 0..s-1 { x = ((x as u128 * x as u128) % n as u128) as u64; if x == n-1 { continue 'a; } }
        return false;
    }
    true
}
fn find_prime_cong1(n: u64, lo: u64) -> u64 {
    let mut p = lo + ((1 + n - lo % n) % n);
    if p <= 2 { p += n; }
    loop { if p > 2 && p % n == 1 && is_prime(p) { return p; } p += n; }
}
fn primitive_root(p: u64) -> u64 {
    let mut m = p - 1; let mut fs = vec![]; let mut d = 2;
    while d * d <= m { if m % d == 0 { fs.push(d); while m % d == 0 { m /= d; } } d += 1; }
    if m > 1 { fs.push(m); }
    let mut g = 2u64;
    loop { if fs.iter().all(|&f| mpow(g, (p-1)/f, p) != 1) { return g; } g += 1; }
}
fn v2(mut x: u64) -> u32 { let mut v = 0; while x & 1 == 0 { v += 1; x >>= 1; } v }
fn double_fact(r: usize) -> f64 { let mut v = 1.0f64; for j in 1..=r { v *= (2*j - 1) as f64; } v }
fn comb(n: usize, k: usize) -> f64 {
    if k > n { return 0.0; } let k = k.min(n - k); let mut r = 1.0f64;
    for i in 0..k { r = r * (n - i) as f64 / (i + 1) as f64; } r
}

// EXACT E_r^charp: number of (a,b) in [n]^r x [n]^r with sum_i mu[a_i] = sum_j mu[b_j] mod p.
// = sum over s of (count of r-fold sums hitting residue s)^2.
fn er_charp(mu: &[u64], r: usize, p: u64) -> u128 {
    // build distribution of r-fold sums mod p by repeated convolution
    let mut cur: HashMap<u64, u128> = HashMap::new();
    for &x in mu { *cur.entry(x % p).or_insert(0) += 1; }
    for _ in 1..r {
        let mut nxt: HashMap<u64, u128> = HashMap::with_capacity(cur.len() * mu.len() / 2 + 8);
        for (&s, &c) in &cur {
            for &x in mu {
                let t = ((s as u128 + x as u128) % p as u128) as u64;
                *nxt.entry(t).or_insert(0) += c;
            }
        }
        cur = nxt;
    }
    cur.values().map(|&c| c * c).sum()
}

// EXACT E_r^char0: complex-equal sums of n-th roots of unity, n = 2^a.
// Only Z-relations among n-th roots (n=2^mu): zeta^{k+n/2} = -zeta^k. So a multiset of r roots
// has a reduced signed coefficient vector of length n/2; two sums are equal over C iff vectors agree.
fn er_char0(n: usize, r: usize) -> u128 {
    let half = n / 2;
    // key: signed coeff vector length half, encoded as Vec<i32>
    let mut cur: HashMap<Vec<i32>, u128> = HashMap::new();
    for k in 0..n {
        let idx = k % half; let sgn = if k < half { 1 } else { -1 };
        let mut v = vec![0i32; half]; v[idx] = sgn;
        *cur.entry(v).or_insert(0) += 1;
    }
    for _ in 1..r {
        let mut nxt: HashMap<Vec<i32>, u128> = HashMap::new();
        for (vt, &c) in &cur {
            for k in 0..n {
                let idx = k % half; let sgn = if k < half { 1 } else { -1 };
                let mut w = vt.clone(); w[idx] += sgn;
                *nxt.entry(w).or_insert(0) += c;
            }
        }
        cur = nxt;
    }
    cur.values().map(|&c| c * c).sum()
}

fn order_n_gen(p: u64, n: u64) -> u64 { let g = primitive_root(p); mpow(g, (p-1)/n, p) }

fn main() {
    println!("================================================================================");
    println!("A04 (S6 Weil-II): EXACT Weil exponent of spur_r(p) = E_r^charp - E_r^char0");
    println!("  SpurToricBounded predicts alpha_r <= r-1 and spur/p^(r-1) <= C(2r,r), n-free.");
    println!("================================================================================");

    // (A) exponent fit: at fixed (n,r), sweep many beta-in-band primes, fit log spur ~ alpha log p.
    for &n in &[8usize, 16, 32] {
        let nn = n as u64;
        let rmax = if n <= 8 { 4 } else if n <= 16 { 4 } else { 3 };
        for r in 2..=rmax {
            let c0 = er_char0(n, r);
            let cbin = comb(2*r, r);
            // sweep primes p = 1 mod n with beta = log_n p in [3.4, 4.6]
            let lo = (nn as f64).powf(3.4) as u64;
            let hi = (nn as f64).powf(4.6) as u64;
            let mut p = find_prime_cong1(nn, lo.max(200));
            let mut rows: Vec<(u64, u128, i128, f64, u32)> = vec![];
            let mut tries = 0;
            while p <= hi && rows.len() < 24 && tries < 4000 {
                let mu: Vec<u64> = {
                    let h = order_n_gen(p, nn);
                    (0..n).map(|j| mpow(h, j as u64, p)).collect()
                };
                let echarp = er_charp(&mu, r, p);
                let spur = echarp as i128 - c0 as i128;
                let beta = (p as f64).ln() / (nn as f64).ln();
                rows.push((p, echarp, spur, beta, v2(p-1)));
                p = find_prime_cong1(nn, p + 1);
                tries += 1;
            }
            // fit over spur>0
            let pos: Vec<(f64,f64)> = rows.iter().filter(|r| r.2 > 0)
                .map(|r| ((r.0 as f64).ln(), (r.2 as f64).ln())).collect();
            let (alpha, cfit) = if pos.len() >= 3 {
                let m = pos.len() as f64;
                let sx: f64 = pos.iter().map(|x| x.0).sum();
                let sy: f64 = pos.iter().map(|x| x.1).sum();
                let sxx: f64 = pos.iter().map(|x| x.0*x.0).sum();
                let sxy: f64 = pos.iter().map(|x| x.0*x.1).sum();
                let a = (m*sxy - sx*sy)/(m*sxx - sx*sx);
                let lc = (sy - a*sx)/m;
                (Some(a), Some(lc.exp()))
            } else { (None, None) };
            let nzero = rows.iter().filter(|rw| rw.2 == 0).count();
            let worst_ratio = rows.iter().filter(|rw| rw.2 > 0)
                .map(|rw| (rw.2 as f64) / (rw.0 as f64).powi((r as i32) - 1))
                .fold(0.0f64, f64::max);
            println!("\n[n={} r={}] char0={} C(2r,r)={:.0}", n, r, c0, cbin);
            match alpha {
                Some(a) => println!("  fit: spur ~ {:.3e} * p^{:.3}   (r-1={})  C(2r,r)={:.0}", cfit.unwrap(), a, r-1, cbin),
                None => println!("  fit: <3 positive-spur primes (mostly faithful)"),
            }
            println!("  faithful (spur=0): {}/{}   worst spur/p^(r-1) = {:.4e}  (toric ok iff <= {:.0})",
                     nzero, rows.len(), worst_ratio, cbin);
            // print a few rows
            for (pp, ec, sp, be, vv) in rows.iter().take(8) {
                let rat = if *sp > 0 { (*sp as f64)/(*pp as f64).powi((r as i32)-1) } else { 0.0 };
                println!("    p={:<12} beta={:.3} v2={:<3} E_charp={:<14} spur={:<12} spur/p^(r-1)={:.4e}",
                         pp, be, vv, ec, sp, rat);
            }
        }
    }

    // (B) PRIZE DEPTH: spur_r / E_r^char0 at r ~ ln p / ln n (the depth where the prize lives),
    //     at the SPECIFIC structured prize prime (highest v2(p-1) near beta=4).
    println!("\n================================================================================");
    println!("(B) prize-depth error ratio spur_r/char0 and spur_r/p^(r-1)/C(2r,r) at r up to ~beta");
    println!("================================================================================");
    for &n in &[8usize, 16, 32] {
        let nn = n as u64;
        // structured prize prime: among p=1 mod n in [n^3.8, n^4.2], pick the highest v2(p-1)
        let lo = (nn as f64).powf(3.8) as u64;
        let hi = (nn as f64).powf(4.2) as u64;
        let mut p = find_prime_cong1(nn, lo.max(200));
        let (mut best_p, mut best_v2) = (p, 0u32);
        let mut tries = 0;
        while p <= hi && tries < 4000 {
            let vv = v2(p-1);
            if vv > best_v2 { best_v2 = vv; best_p = p; }
            p = find_prime_cong1(nn, p + 1); tries += 1;
        }
        let p = best_p;
        let mu: Vec<u64> = { let h = order_n_gen(p, nn); (0..n).map(|j| mpow(h, j as u64, p)).collect() };
        let beta = (p as f64).ln() / (nn as f64).ln();
        let rdepth = ((p as f64).ln() / (nn as f64).ln()).ceil() as usize; // ~ beta ~ ln q / ln n
        let rmax = (rdepth + 2).min(if n <= 8 { 6 } else if n <= 16 { 5 } else { 4 });
        println!("\n[n={} p={} beta={:.3} v2={} rdepth~{} ]", n, p, beta, best_v2, rdepth);
        println!("  r |  E_charp        char0          spur         spur/char0    spur/p^(r-1)/C(2r,r)");
        for r in 2..=rmax {
            let c0 = er_char0(n, r);
            let ec = er_charp(&mu, r, p);
            let spur = ec as i128 - c0 as i128;
            let ratio_c0 = (spur as f64) / (c0 as f64);
            let cbin = comb(2*r, r);
            let toric = if spur > 0 { (spur as f64)/(p as f64).powi((r as i32)-1)/cbin } else { 0.0 };
            println!("  {:2}| {:14} {:14} {:13} {:13.4e} {:13.4e}", r, ec, c0, spur, ratio_c0, toric);
        }
    }
    println!("\nDONE. SpurToricBounded holds iff every spur/p^(r-1)/C(2r,r) <= 1 and alpha_r <= r-1.");
}
