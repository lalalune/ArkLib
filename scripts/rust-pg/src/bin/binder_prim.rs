// binder_prim: report the BINDING direction (a,b) at s* and its primitivity gcd(b-a,n),
// for the dyadic-tower binder-primitivity-flip probe (#444 E3/E5 face).
// Usage: binder_prim n k [pidx]   (pidx selects the pidx-th prime p==1 mod n, p>=n^4; default 0)
// Saturated ("heavy") directions are treated as carrying 0 over-det far-line info.
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
fn gcd(mut a: u64, mut b: u64) -> u64 { while b != 0 { let t = a % b; a = b; b = t; } a }

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
fn nth_prime(n: u64, idx: usize) -> u64 { let mut p = n*n*n*n; let mut cnt = 0; loop { if p % n == 1 && is_prime(p) { if cnt == idx { return p; } cnt += 1; } p += 1; } }

#[inline]
fn ddk_idx(vals: &[u64], idx: &[usize], k: usize, p: u64, invd: &[u64], n: usize) -> u64 {
    let mut vs: [u64; 64] = [0u64; 64];
    for t in 0..=k { vs[t] = vals[t]; }
    for j in 1..=k { for i in (j..=k).rev() { let inv = invd[idx[i]*n + idx[i-j]]; vs[i] = mulmod(submod(vs[i], vs[i-1], p), inv, p); } }
    vs[k]
}
#[inline]
fn in_rs_idx(vals: &[u64], idx: &[usize], k: usize, p: u64, invd: &[u64], n: usize) -> bool {
    let s = idx.len();
    if s <= k { return true; }
    for st in 0..(s - k) { if ddk_idx(&vals[st..st+k+1], &idx[st..st+k+1], k, p, invd, n) != 0 { return false; } }
    true
}
fn incidence(n: usize, mua: &[u64], mub: &[u64], k: usize, p: u64, s: usize, invd: &[u64]) -> u64 {
    let mut local: HashSet<u64> = HashSet::new();
    let mut comb: Vec<usize> = (0..s).collect();
    let mut u0 = vec![0u64; s]; let mut u1 = vec![0u64; s]; let mut full = vec![0u64; s];
    loop {
        for (j, &idx) in comb.iter().enumerate() { u0[j] = mua[idx]; u1[j] = mub[idx]; }
        if in_rs_idx(&u1, &comb, k, p, invd, n) {
            if in_rs_idx(&u0, &comb, k, p, invd, n) { return u64::MAX; }
        } else {
            let a0 = ddk_idx(&u0, &comb, k, p, invd, n);
            let a1 = ddk_idx(&u1, &comb, k, p, invd, n);
            if a1 != 0 {
                let gm = mulmod(submod(0, a0, p), invmod(a1, p), p);
                for i in 0..s { full[i] = addmod(u0[i], mulmod(gm, u1[i], p), p); }
                if in_rs_idx(&full, &comb, k, p, invd, n) { local.insert(gm); }
            }
        }
        let mut i = s; let mut advanced = false;
        while i > 0 { i -= 1; if comb[i] != i + n - s { comb[i] += 1; for j in (i+1)..s { comb[j] = comb[j-1] + 1; } advanced = true; break; } }
        if !advanced { break; }
    }
    local.len() as u64
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let n: usize = args[1].parse().unwrap();
    let k: usize = args[2].parse().unwrap();
    let pidx: usize = args.get(3).and_then(|s| s.parse().ok()).unwrap_or(0);
    let p = nth_prime(n as u64, pidx);
    let g = proot(p);
    let h = powmod(g, (p - 1) / n as u64, p);
    let mu: Vec<u64> = (0..n).map(|i| powmod(h, i as u64, p)).collect();
    let mut invd = vec![0u64; n * n];
    for a in 0..n { for b in 0..n { if a != b { invd[a*n+b] = invmod(submod(mu[a], mu[b], p), p); } } }
    let budget = n as u64;
    let mut sstar = 0usize; let mut binder = (0u64, 0u64); let mut bmax = 0u64;
    for s in (k+2)..n {
        let dirs: Vec<(u64,u64)> = ((k as u64)..(s as u64)).flat_map(|b| ((k as u64)..(n as u64)).filter(move |&a| a != b).map(move |a| (a,b))).collect();
        let (mx, arg) = dirs.par_iter().map(|&(a,b)| {
            let mua: Vec<u64> = (0..n).map(|i| powmod(mu[i], a, p)).collect();
            let mub: Vec<u64> = (0..n).map(|i| powmod(mu[i], b, p)).collect();
            let inc = incidence(n, &mua, &mub, k, p, s, &invd);
            if inc == u64::MAX { (0u64, (a,b)) } else { (inc, (a,b)) }
        }).reduce(|| (0u64,(0u64,0u64)), |x, y| if y.0 > x.0 { y } else { x });
        if mx <= budget { sstar = s; binder = arg; bmax = mx; break; }
    }
    let d = ((binder.1 + n as u64 - binder.0 % n as u64) % n as u64);
    let gg = gcd(d, n as u64);
    let verdict = if gg == 1 { "PRIMITIVE" } else { "IMPRIMITIVE" };
    println!("n={} k={} pidx={} p={} : s*={} binder=({},{}) b-a={} gcd(b-a,n)={} maxI={} => {}",
             n, k, pidx, p, sstar, binder.0, binder.1, d, gg, bmax, verdict);
}
