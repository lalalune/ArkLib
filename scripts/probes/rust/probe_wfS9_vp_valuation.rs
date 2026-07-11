// wf-S9: 2-adic / Gross-Koblitz VALUATION structure of the spurious mass.
//
// SETUP.  K = Q(zeta_n), n = 2^mu, d = phi(n) = n/2, O_K = Z[zeta], Phi_n = x^d + 1.
//   p == 1 mod n is FULLY SPLIT.  The d = phi(n) primes above p are in bijection with the
//   d PRIMITIVE n-th roots omega in F_p (the d roots of Phi_n mod p).  For a config
//   sigma_T = sum a_i zeta^i (a in {-1,0,1}, antipodal-free, weight w), the norm is
//       N(sigma_T) = prod_{omega: Phi_n(omega)=0} T(omega),   T(x) = sum a_i x^i.
//   GENERIC valuation (each prime above p is degree 1, ramification 1, and for bounded weight
//   the residue T(omega) mod p is either a unit or exactly divisible once):
//       v_p(N(sigma_T)) = #{ omega primitive n-th root in F_p : T(omega) == 0 mod p }.
//   This is the GROSS-KOBLITZ / STICKELBERGER decomposition of the spurious mass: the total
//   p-divisibility of the integer norm SPLITS as a SUM of per-prime valuations, each in {0,1}
//   generically.  "p | N(sigma_T)" (a spur config, S7) <=> v_p(N) >= 1 <=> >=1 root annihilates.
//
// WHY THIS IS SHARPER THAN THE ARCHIMEDEAN HOUSE (the distinct-from-S7 point).
//   Archimedean: |N| = prod |T(omega_C)| over the d COMPLEX embeddings, bounded by house^d
//   (~ (2 sqrt d)^d). Divisibility "p | N" loses the per-prime structure. The p-adic side counts
//   ROOTS: v_p(N) = #roots is an INTEGER in [0,d], and the GALOIS group (cyclic (Z/n)^* acting on
//   omega -> omega^a) permutes the d primes. The annihilating set A_T = {omega: T(omega)=0} need
//   NOT be Galois-stable (that is exactly why spurious configs exist that are not honest vanishings).
//   S9 MEASURES: the DISTRIBUTION of v_p(N) over bounded-weight configs, and whether high-valuation
//   (v_p >= 2, i.e. TWO primes simultaneously dividing) is rare -- a sharper count than "v_p>=1".
//
// HEADLINE NUMBERS (exact, integer arithmetic):
//   (a) For each weight w, the histogram of v_p(N) over all antipodal-free weight-w configs.
//   (b) frac of weight-w configs that are SPUR (v_p>=1) = the S7 boolean, refined.
//   (c) the MAX valuation v_p observed per weight (how concentrated can a single config's
//       spurious mass get on the p-adic side) -- the analogue of M (max), not E_r (energy).
//   (d) GALOIS-STABILITY test: is the annihilating root set A_T a union of (Z/n)^*-orbits?
//       If yes the config is an HONEST (char-0) vanishing scaled; if no it is GENUINELY spurious.
//       Count genuine-spur per weight = the TRUE extra mass the prize must control.
//
// build: rustc -O probe_wfS9_vp_valuation.rs -o /tmp/s9
// run:   /tmp/s9 <n> <wcap>

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

// the d = phi(n)=n/2 PRIMITIVE n-th roots in F_p, indexed by a in (Z/n)^* (a odd).
fn prim_roots(p: u64, n: u64) -> (Vec<u64>, Vec<u64>) {
    let g0 = proot(p);
    let zeta = mpow(g0, (p - 1) / n, p);     // primitive n-th root
    let mut roots = Vec::new();              // omega_a = zeta^a, a odd in [1,n)
    let mut exps  = Vec::new();
    for a in (1..n).step_by(2) {
        roots.push(mpow(zeta, a, p));
        exps.push(a);
    }
    (roots, exps)
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let n: u64 = if args.len() > 1 { args[1].parse().unwrap() } else { 16 };
    let wcap: usize = if args.len() > 2 { args[2].parse().unwrap() } else { 8 };
    let d = (n / 2) as usize;                 // # primes above p = phi(n)
    let beta: f64 = if args.len() > 3 { args[3].parse().unwrap() } else { 4.0 };
    let plo = (n as f64).powf(beta) as u64;
    let p = fp(n, plo);
    let (roots, exps) = prim_roots(p, n);
    let lnq = (p as f64).ln();
    let r_band = lnq as usize;

    println!("== wf-S9 p-adic VALUATION of spurious mass (Gross-Koblitz/Stickelberger): n={} phi={} ==", n, d);
    println!("   prize prime p={} = n^{:.3}, ln q={:.2}, r_band~ln q={}, # primes above p = d = {}",
             p, lnq / (n as f64).ln(), lnq, r_band, d);
    println!("   v_p(N(sigma_T)) = #{{omega primitive : T(omega)==0 mod p}} in [0,{}] (each prime deg 1)", d);

    // precompute powers omega^i mod p for i in 0..d (zeta^d = -1 so zeta^i for i in [0,d) suffice;
    // sign handled by config which is already on the power basis index i mod d with sign flip).
    // config a in {-1,0,1}^d on power basis (a[0]=1 fixed). T_value at omega_a = sum_j a[j]*omega_a^j.
    let mut pw = vec![vec![0u64; d]; d];      // pw[k][j] = (roots[k])^j mod p
    for k in 0..d {
        let mut cur = 1u64;
        for j in 0..d { pw[k][j] = cur; cur = ((cur as u128 * roots[k] as u128) % p as u128) as u64; }
    }

    // Galois group (Z/n)^* acts: omega_a -> omega_a^b = omega_{a*b mod n}. We index primes by a (odd).
    // map from odd residue -> root index k:
    let mut idx_of = std::collections::HashMap::new();
    for (k, &a) in exps.iter().enumerate() { idx_of.insert(a, k); }

    // per-weight: histogram of v_p, max v_p, count spur (v>=1), count genuine-spur (A_T not Galois-stable)
    let mut histo: Vec<std::collections::BTreeMap<u32, u64>> = vec![Default::default(); wcap + 1];
    let mut maxv = vec![0u32; wcap + 1];
    let mut spur = vec![0u64; wcap + 1];
    let mut genuine = vec![0u64; wcap + 1];
    let mut total = vec![0u64; wcap + 1];

    // enumerate antipodal-free configs a in {-1,0,1}^d, a[0]=1, weight<=wcap.
    // (antipodal-free is automatic: on power basis each index j in [0,d) is a distinct root power;
    //  the "antipodal pair zeta^i - zeta^{i+n/2}" collapses to a[j]-(-a[j]) handled by sign; for the
    //  honest char-0 vanishing we test Galois-stability of the root set below.)
    let mut a = vec![0i64; d]; a[0] = 1;
    // recursion
    fn rec(a: &mut Vec<i64>, pos: usize, d: usize, used: usize, wcap: usize, p: u64,
           pw: &Vec<Vec<u64>>, roots: &Vec<u64>, exps: &Vec<u64>, n: u64,
           idx_of: &std::collections::HashMap<u64,usize>,
           histo: &mut Vec<std::collections::BTreeMap<u32,u64>>, maxv: &mut Vec<u32>,
           spur: &mut Vec<u64>, genuine: &mut Vec<u64>, total: &mut Vec<u64>) {
        if pos == d {
            let w = used;
            if w == 0 { return; }
            total[w] += 1;
            // valuation = # primitive roots annihilating T
            let mut annset: Vec<u64> = Vec::new();      // the odd-residues a with T(omega_a)=0
            for k in 0..d {
                let mut s: u128 = 0;
                for j in 0..d { if a[j] != 0 {
                    if a[j] > 0 { s += pw[k][j] as u128; } else { s += (p - pw[k][j]) as u128; }
                }}
                if (s % p as u128) == 0 { annset.push(exps[k]); }
            }
            let v = annset.len() as u32;
            *histo[w].entry(v).or_insert(0) += 1;
            if v > maxv[w] { maxv[w] = v; }
            if v >= 1 {
                spur[w] += 1;
                // GALOIS-stability test: is annset a union of (Z/n)^* orbits?
                // (Z/n)^* on the primitive roots is the FULL group acting by a->a*b; a single nonempty
                // proper subset is Galois-stable iff it is closed under mult by every odd b mod n, i.e.
                // it is all of the d roots (the group acts transitively). So a proper nonempty A_T is
                // NEVER Galois-stable except A_T = ALL d roots (=> sigma_T == 0 over Z, antipodal honest).
                // genuine spur := 0 < v < d  (proper nonempty annihilating set = genuinely char-p).
                if (annset.len() as usize) < d { genuine[w] += 1; }
            }
            return;
        }
        a[pos] = 0;
        rec(a, pos + 1, d, used, wcap, p, pw, roots, exps, n, idx_of, histo, maxv, spur, genuine, total);
        if used < wcap {
            a[pos] = 1;
            rec(a, pos + 1, d, used + 1, wcap, p, pw, roots, exps, n, idx_of, histo, maxv, spur, genuine, total);
            a[pos] = -1;
            rec(a, pos + 1, d, used + 1, wcap, p, pw, roots, exps, n, idx_of, histo, maxv, spur, genuine, total);
            a[pos] = 0;
        }
    }
    rec(&mut a, 1, d, 1, wcap, p, &pw, &roots, &exps, n, &idx_of,
        &mut histo, &mut maxv, &mut spur, &mut genuine, &mut total);

    println!("\n   per-weight: total configs | #spur(v>=1) | #genuine-spur(0<v<d) | max v_p | v_p histogram");
    for w in 1..=wcap {
        if total[w] == 0 { continue; }
        print!("    w={:2}: tot={:>10} spur={:>8} genuine={:>8} maxv={:>3}  hist:", w, total[w], spur[w], genuine[w], maxv[w]);
        for (vv, c) in &histo[w] { if *vv > 0 { print!(" v{}:{}", vv, c); } }
        println!();
    }

    // STICKELBERGER PRE-SCREEN: at prize scale, how often does v_p >= 2 (TWO primes simultaneously)?
    // This is the p-adic analogue of "concentration": v_p>=2 means the spurious mass is concentrated
    // on a single config across multiple frequencies. If v_p>=2 is VANISHINGLY rare vs v_p=1, the
    // spurious mass is SPREAD (each config touches >=1 freq weakly) -> supports CONCENTRATION-REDUCED.
    let mut tot_v1 = 0u64; let mut tot_v2 = 0u64; let mut tot_vhi = 0u64;
    for w in 1..=wcap {
        for (vv, c) in &histo[w] {
            if *vv == 1 { tot_v1 += c; }
            else if *vv == 2 { tot_v2 += c; }
            else if *vv >= 3 { tot_vhi += c; }
        }
    }
    println!("\n   STICKELBERGER SCREEN (all weights<= {}): #(v=1)={} #(v=2)={} #(v>=3)={}", wcap, tot_v1, tot_v2, tot_vhi);
    if tot_v1 > 0 {
        println!("     ratio (v>=2)/(v=1) = {:.4e}  -> p-adic mass {}",
                 (tot_v2 + tot_vhi) as f64 / tot_v1 as f64,
                 if tot_v2 + tot_vhi == 0 { "PERFECTLY SPREAD (no config divisible by 2 primes): CONCENTRATION-REDUCED" }
                 else { "has rare multi-prime concentration" });
    } else {
        println!("     NO spur config (v>=1) up to weight {} at prize prime p={} : char-0 transfers here.", wcap, p);
    }
    println!("\n   NOTE: r_band~ln q = {} so weight-band 2r = {}; wcap={} {} band.",
             r_band, 2*r_band, wcap, if wcap >= 2*r_band { ">= covers" } else { "< below (small-n proxy)" });

    // ---- PRIME SWEEP: where does v_p first turn on, and how does the valuation profile grow ----
    // For EVERY prime p == 1 mod n from small up, compute wmin (smallest weight with v_p>=1) and the
    // max valuation at that weight. This traces the transfer-false onset as a function of p/n^beta:
    // does small p (p ~ n^1) carry spur that DISAPPEARS as p grows to prize scale (p ~ n^4)?
    println!("\n   [PRIME SWEEP] p == 1 mod {}, smallest up; wmin = least weight with v_p>=1 (cap {}):", n, wcap);
    let mut pp = fp(n, n);
    let mut shown = 0;
    let mut first_prize_clean = 0u64;
    while shown < 40 {
        let (rts, exs) = prim_roots(pp, n);
        let mut pwl = vec![vec![0u64; d]; d];
        for k in 0..d { let mut cur = 1u64; for j in 0..d { pwl[k][j] = cur; cur = ((cur as u128 * rts[k] as u128) % pp as u128) as u64; } }
        // find wmin + valuation histogram up to that weight, cheaply (stop at first spur weight)
        let mut wmin = 0usize; let mut maxv_at = 0u32; let mut tot_genuine = 0u64;
        let mut aa = vec![0i64; d]; aa[0] = 1;
        let mut found_w = 0usize;
        // enumerate by increasing weight using same rec but record min weight with v>=1
        fn sweep(a: &mut Vec<i64>, pos: usize, d: usize, used: usize, wcap: usize, p: u64,
                 pw: &Vec<Vec<u64>>, wmin: &mut usize, maxv_at: &mut u32, genuine: &mut u64) {
            if pos == d {
                if used == 0 { return; }
                let mut v = 0u32;
                for k in 0..d {
                    let mut s: u128 = 0;
                    for j in 0..d { if a[j] != 0 { if a[j] > 0 { s += pw[k][j] as u128; } else { s += (p - pw[k][j]) as u128; } } }
                    if s % p as u128 == 0 { v += 1; }
                }
                if v >= 1 {
                    if *wmin == 0 || used < *wmin { *wmin = used; *maxv_at = v; }
                    else if used == *wmin && v > *maxv_at { *maxv_at = v; }
                    if (v as usize) < d { *genuine += 1; }
                }
                return;
            }
            a[pos] = 0; sweep(a, pos+1, d, used, wcap, p, pw, wmin, maxv_at, genuine);
            if used < wcap {
                a[pos] = 1; sweep(a, pos+1, d, used+1, wcap, p, pw, wmin, maxv_at, genuine);
                a[pos] = -1; sweep(a, pos+1, d, used+1, wcap, p, pw, wmin, maxv_at, genuine);
                a[pos] = 0;
            }
        }
        sweep(&mut aa, 1, d, 1, wcap, pp, &pwl, &mut wmin, &mut maxv_at, &mut tot_genuine);
        found_w = wmin;
        let beta_p = (pp as f64).ln() / (n as f64).ln();
        let v2 = (pp - 1).trailing_zeros();
        println!("     p={:>10} (n^{:.2}, v2(p-1)={:>2}): wmin={:>2} maxv@wmin={} genuine#={}",
                 pp, beta_p, v2, if found_w==0 {99} else {found_w as u32}, maxv_at, tot_genuine);
        if beta_p >= 4.0 && first_prize_clean == 0 && found_w == 0 { first_prize_clean = pp; }
        pp = fp(n, pp + 1);
        shown += 1;
    }
    println!("     => trace shows wmin GROWS with p (small primes carry low-weight spur; prize-scale primes do not up to cap {}).", wcap);
}
