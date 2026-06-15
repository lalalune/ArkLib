// Parallel over-determined far-line incidence engine for #407.
// Computes delta* = (n - s*)/n where s* = min s with max over far dirs (b<s) of incidence(a,b;s) <= budget.
// incidence(a,b;s) = # distinct gamma in F_p s.t. x^a + gamma x^b agrees with a deg<k poly on >= s points of mu_n.
// Exact via the divided-difference / over-determined witness condition. Parallelized with rayon.
use rayon::prelude::*;
use std::collections::HashSet;

#[inline]
fn mulmod(a: u64, b: u64, p: u64) -> u64 { ((a as u128 * b as u128) % p as u128) as u64 }
#[inline]
fn addmod(a: u64, b: u64, p: u64) -> u64 { let s = a + b; if s >= p { s - p } else { s } }
#[inline]
fn submod(a: u64, b: u64, p: u64) -> u64 { if a >= b { a - b } else { p - b + a } }
fn powmod(mut b: u64, mut e: u64, p: u64) -> u64 { let mut r = 1u64; b %= p; while e > 0 { if e & 1 == 1 { r = mulmod(r, b, p); } b = mulmod(b, b, p); e >>= 1; } r }
#[inline]
fn invmod(a: u64, p: u64) -> u64 { powmod(a, p - 2, p) }

fn is_prime(x: u64) -> bool {
    if x < 2 { return false; }
    for &q in &[2u64,3,5,7,11,13,17,19,23,29,31,37] { if x % q == 0 { return x == q; } }
    let mut d = x - 1; let mut s = 0; while d % 2 == 0 { d /= 2; s += 1; }
    'a: for &a in &[2u64,3,5,7,11,13,17,19,23,29,31,37] {
        let mut y = powmod(a, d, x);
        if y == 1 || y == x - 1 { continue; }
        for _ in 0..s-1 { y = mulmod(y, y, x); if y == x - 1 { continue 'a; } }
        return false;
    }
    true
}
fn factor(mut x: u64) -> Vec<u64> { let mut f = vec![]; let mut d = 2; while d*d <= x { if x % d == 0 { f.push(d); while x % d == 0 { x /= d; } } d += 1; } if x > 1 { f.push(x); } f }
fn proot(p: u64) -> u64 { let fs = factor(p - 1); for g in 2..p { if fs.iter().all(|&q| powmod(g, (p-1)/q, p) != 1) { return g; } } 0 }
fn big_prime(n: u64) -> u64 { let mut p = n*n*n*n; loop { if p % n == 1 && is_prime(p) { return p; } p += 1; } }

// k-th divided difference of vals over node-INDICES idx[0..k+1] (into mu_n), using precomputed inv-diff table.
#[inline]
fn ddk_idx(vals: &[u64], idx: &[usize], k: usize, p: u64, invd: &[u64], n: usize) -> u64 {
    let mut vs: [u64; 64] = [0u64; 64];
    for t in 0..=k { vs[t] = vals[t]; }
    for j in 1..=k {
        for i in (j..=k).rev() {
            let inv = invd[idx[i] * n + idx[i-j]];
            vs[i] = mulmod(submod(vs[i], vs[i-1], p), inv, p);
        }
    }
    vs[k]
}
// does vals (on node-indices idx) lie on a deg<k poly? all order-k divided diffs over consecutive windows vanish
#[inline]
fn in_rs_idx(vals: &[u64], idx: &[usize], k: usize, p: u64, invd: &[u64], n: usize) -> bool {
    let s = idx.len();
    if s <= k { return true; }
    for st in 0..(s - k) {
        if ddk_idx(&vals[st..st+k+1], &idx[st..st+k+1], k, p, invd, n) != 0 { return false; }
    }
    true
}

// unrank: r-th s-combination of [0,n) in lexicographic order (combinatorial number system)
fn unrank(mut r: u64, n: usize, s: usize, comb: &mut Vec<usize>) {
    comb.clear();
    let mut x = 0usize;
    let mut remaining = s;
    while remaining > 0 {
        // choose next element >= x
        loop {
            let c = nck((n - 1 - x) as u64, (remaining - 1) as u64);
            if r < c { comb.push(x); x += 1; remaining -= 1; break; }
            else { r -= c; x += 1; }
        }
    }
}
fn nck(n: u64, k: u64) -> u64 {
    if k > n { return 0; }
    let k = k.min(n - k);
    let mut r: u128 = 1;
    for i in 0..k { r = r * (n - i) as u128 / (i + 1) as u128; }
    r as u64
}

// incidence for direction (a,b), witness size s. SEQUENTIAL, correct enumeration of all C(n,s) combinations
// via lex next-combination starting from [0,1,..,s-1]. Returns count, or u64::MAX if any witness is heavy.
fn incidence(a: u64, b: u64, n: usize, _mu: &[u64], mua: &[u64], mub: &[u64], k: usize, p: u64, s: usize, invd: &[u64]) -> u64 {
    let _ = (a, b);
    let mut local: HashSet<u64> = HashSet::new();
    let mut comb: Vec<usize> = (0..s).collect();
    let mut u0 = vec![0u64; s]; let mut u1 = vec![0u64; s];
    let mut full = vec![0u64; s];
    loop {
        for (j, &idx) in comb.iter().enumerate() { u0[j] = mua[idx]; u1[j] = mub[idx]; }
        if in_rs_idx(&u1, &comb, k, p, invd, n) {
            if in_rs_idx(&u0, &comb, k, p, invd, n) { return u64::MAX; } // heavy -> saturated
        } else {
            let a0 = ddk_idx(&u0, &comb, k, p, invd, n);
            let a1 = ddk_idx(&u1, &comb, k, p, invd, n);
            if a1 != 0 {
                let gm = mulmod(submod(0, a0, p), invmod(a1, p), p);
                for i in 0..s { full[i] = addmod(u0[i], mulmod(gm, u1[i], p), p); }
                if in_rs_idx(&full, &comb, k, p, invd, n) { local.insert(gm); }
            }
        }
        // next combination in lex order; if none, done
        let mut i = s; let mut advanced = false;
        while i > 0 { i -= 1; if comb[i] != i + n - s { comb[i] += 1; for j in (i+1)..s { comb[j] = comb[j-1] + 1; } advanced = true; break; } }
        if !advanced { break; }
    }
    local.len() as u64
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    // usage: pg n k   (sweeps s to find s*, fixed prize-scale prime)
    let n: usize = args[1].parse().unwrap();
    let k: usize = args[2].parse().unwrap();
    let curve: bool = args.get(3).map(|a| a == "curve").unwrap_or(false);
    // single-direction mode: "n k a b" prints I(a,b;s) for all s (per-direction decay curve)
    let single: Option<(u64,u64)> = match (args.get(3).and_then(|s| s.parse::<u64>().ok()),
                                           args.get(4).and_then(|s| s.parse::<u64>().ok())) {
        (Some(a), Some(b)) => Some((a, b)),
        _ => None,
    };
    let p = big_prime(n as u64);
    let g = proot(p);
    let h = powmod(g, (p - 1) / n as u64, p);
    let mu: Vec<u64> = (0..n).map(|i| powmod(h, i as u64, p)).collect();
    // precompute inv-diff table: invd[a*n+b] = 1/(mu[a]-mu[b]) for a!=b (0 on diagonal)
    let mut invd = vec![0u64; n * n];
    for a in 0..n { for b in 0..n { if a != b { invd[a*n+b] = invmod(submod(mu[a], mu[b], p), p); } } }
    let budget = n as u64;
    let rho = k as f64 / n as f64;
    let john = 1.0 - rho.sqrt(); let cap = 1.0 - rho;
    if let Some((a, b)) = single {
        let mua: Vec<u64> = (0..n).map(|i| powmod(mu[i], a, p)).collect();
        let mub: Vec<u64> = (0..n).map(|i| powmod(mu[i], b, p)).collect();
        println!("SINGLE dir (a={},b={}) n={} k={}: I(s) per-direction decay", a, b, n, k);
        for s in (k+2)..(n-1) {
            if nck(n as u64, s as u64) > 300_000_000 { break; }
            let inc = incidence(a, b, n, &mu, &mua, &mub, k, p, s, &invd);
            let isz = if inc == u64::MAX { "HEAVY".to_string() } else { inc.to_string() };
            println!("  s={} (s-k={}): I={}", s, s-k, isz);
        }
        return;
    }
    println!("n={} k={} rho={:.4} p={}(~n^4) Johnson={:.4} cap={:.4} budget={}", n, k, rho, p, john, cap, budget);
    let mut sstar = 0usize;
    for s in (k+2)..n {
        let csz = nck(n as u64, s as u64);
        if csz > 200_000_000 { println!("  s={} C={} too big, stop", s, csz); break; }
        // max over far directions b in [k, s), a in [k, n), a!=b. Parallelize over directions.
        let dirs: Vec<(u64,u64)> = ((k as u64)..(s as u64)).flat_map(|b| ((k as u64)..(n as u64)).filter(move |&a| a != b).map(move |a| (a,b))).collect();
        let (mx, arg) = dirs.par_iter().map(|&(a,b)| {
            let mua: Vec<u64> = (0..n).map(|i| powmod(mu[i], a, p)).collect();
            let mub: Vec<u64> = (0..n).map(|i| powmod(mu[i], b, p)).collect();
            let inc = incidence(a, b, n, &mu, &mua, &mub, k, p, s, &invd);
            if inc == u64::MAX { (0u64, (a,b)) } else { (inc, (a,b)) }
        }).reduce(|| (0u64,(0u64,0u64)), |x, y| if y.0 > x.0 { y } else { x });
        let good = mx <= budget;
        println!("  s={} (s-k={}): maxI={} at {:?}  {}", s, s-k, mx, arg, if good {"GOOD"} else {"bad"});
        if good && sstar == 0 { sstar = s; if !curve { break; } }
        if curve && s >= n/2 + 1 { break; }
    }
    if sstar > 0 {
        let ds = (n - sstar) as f64 / n as f64;
        println!("  => s*={}, s*-k={}, delta*={:.4}, defect(s*-k)/n={:.4}  [Johnson {:.4}, cap {:.4}]",
                 sstar, sstar - k, ds, (sstar - k) as f64 / n as f64, john, cap);
    }
}
