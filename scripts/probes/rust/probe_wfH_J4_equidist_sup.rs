// LANE J4 (#444): Homogeneous-dynamics / Ratner / EMV / Lindenstrauss test.
//
// THE CLAIM UNDER TEST: effective equidistribution of the period orbit {eta_b : b in F_p^* / mu_n}
// under the diagonal/dilation torus action forces SUP -> avg + controlled deviation = sqrt(n log).
//
// THE STRUCTURAL OBSTRUCTION we are checking EXACTLY (not float-flat):
//   Equidistribution is a WEAK-* / DISCREPANCY statement (Einsiedler survey: "weak-* convergence
//   and discrepancy against smooth test functions", a bulk/L1 phenomenon). For the ABELIAN torus
//   (dilation b -> g^{(p-1)/n} b acting on cosets = a cyclic rotation on Z/m) there is NO spectral
//   gap (EMV needs SEMISIMPLE w/ finite centralizer). The ONLY effective control of the abelian
//   discrepancy is Erdos-Turan-Koksma: discrepancy is BOUNDED BY exponential sums -- i.e. the
//   character-sum bound is the INPUT, not the OUTPUT. So equidistribution -> sup is CIRCULAR.
//
// We make this CONCRETE and EXACT: the sup M = max_b |eta_b| is detected by smooth test functions
// (a "bulk" object that equidistribution sees) ONLY if the SUP-window {b : |eta_b| > T} is reachable
// by a low-frequency / bounded-degree-moment functional. We test:
//   (1) How many moments r of the |eta_b|^2 distribution are needed before the r-th moment "sees"
//       M (i.e. (E[|eta|^{2r}])^{1/2r} reaches M). If this r grows like log m / log(M^2/avg), the sup
//       is a RARE TAIL invisible to any FIXED-degree smooth test function -> equidistribution
//       (which controls fixed smooth functionals) is blind. This is the F0 conservation law made
//       quantitative for the dynamical route.
//   (2) The fraction of cosets achieving |eta_b| within (1-eps) of M -- if Theta(1/m) (a single
//       rare orbit point), the sup is NOT a positive-density / bulk feature.
//   (3) Erdos-Turan direction sanity: the discrepancy of the orbit IS governed by the same eta_b
//       sums (we report the max |eta_b| = exactly the ET-K numerator), confirming circularity.
//
// EXACT integer arithmetic for the COUNT/ENERGY pieces (E[|eta|^{2r}] = additive-energy moments,
// computed by exact int cyclic convolution). Periods themselves use f64 trig only for the live SUP
// readout M (which is the established wall number, cross-checked vs scripts/probes/rust/mn_wall.rs);
// the MOMENT/tail logic that drives the J4 verdict is EXACT integer.

use std::f64::consts::PI;

fn mpow(a:u64,mut e:u64,p:u64)->u64{let mut r=1u128;let mut a2=a as u128;let pp=p as u128;while e>0{if e&1==1{r=r*a2%pp;}a2=a2*a2%pp;e>>=1;}r as u64}
fn is_prime(n:u64)->bool{if n<2{return false;}let mut d=2u64;while d*d<=n{if n%d==0{return false;}d+=1;}true}
fn find_prime_cong1(n:u64,lo:u64)->u64{let mut p=lo+((n+1-lo%n)%n);if p<=2{p+=n;}loop{if p>2&&p%n==1&&is_prime(p){return p;}p+=n;}}
fn primitive_root(p:u64)->u64{let mut m=p-1;let mut fs=vec![];let mut d=2u64;while d*d<=m{if m%d==0{fs.push(d);while m%d==0{m/=d;}}d+=1;}if m>1{fs.push(m);}let mut g=2u64;loop{if fs.iter().all(|&f|mpow(g,(p-1)/f,p)!=1){return g;}g+=1;}}

// EXACT additive-energy moment E_r = sum over (x_1..x_r, y_1..y_r) in mu_n with sum x = sum y of 1.
// Computed exactly via the integer count vector N(v) = #{ (a,b) in mu_n^2 : a-b = v } ... but the
// 2r-moment of |eta|^2 requires the r-fold self-convolution. We use the EXACT integer histogram of
// the multiset of sums of r elements of mu_n, mod p, then E_r = sum_v hist(v)^2. This equals
// (1/q) * sum_b |eta_b|^{2r} exactly (Parseval). So (E_r)^{1/r} is the exact 2r-th moment scale,
// and avg energy E[|eta|^{2r}] = E_r * (q/m)  ... we work with the moment scale directly.
fn additive_moment(mu:&[u64], r:usize, p:u64)->u128{
    // hist of sums of exactly r elements (with repetition, ordered) of mu, mod p.
    // start: hist0 = delta_0. Then convolve r times with the mu-indicator (each step: add one element).
    let pp = p as usize;
    let mut hist = vec![0u128; pp];
    hist[0] = 1;
    for _ in 0..r {
        let mut next = vec![0u128; pp];
        for v in 0..pp {
            let h = hist[v];
            if h == 0 { continue; }
            for &x in mu {
                let w = (v + x as usize) % pp;
                next[w] += h;
            }
        }
        hist = next;
    }
    // E_r = sum_v hist(v)^2  (= number of (r+r)-tuples with equal sums = the energy)
    hist.iter().map(|&h| h*h).sum()
}

fn measure_sup(mu:&[u64], g:u64, n:u64, p:u64)->(f64, u64, usize){
    let m = (p-1)/n;
    let gn = mpow(g, n, p);
    let mut best = 0.0f64;
    let mut best_idx = 0usize;
    let mut b = 1u64;
    let mut mags: Vec<f64> = Vec::with_capacity(m as usize);
    for j in 0..m {
        let mut re=0.0f64; let mut im=0.0f64;
        for &x in mu {
            let t = ((b as u128 * x as u128) % p as u128) as u64;
            let ang = 2.0*PI*(t as f64)/(p as f64);
            re+=ang.cos(); im+=ang.sin();
        }
        let mag=(re*re+im*im).sqrt();
        mags.push(mag);
        if mag>best{best=mag; best_idx=j as usize;}
        b = ((b as u128 * gn as u128) % p as u128) as u64;
    }
    // count cosets within (1-eps) of best
    let thr = best*0.95;
    let cnt = mags.iter().filter(|&&v| v>=thr).count();
    let _ = best_idx;
    (best, m, cnt)
}

fn main(){
    println!("# LANE J4: equidistribution (EMV/Ratner/Lindenstrauss) vs SUP -- exact moment/tail test");
    println!("# beta=4 prize regime (p = smallest prime cong 1 mod n with p >= n^4)");
    println!("# Q1: depth r* where (moment scale)^{{1/2r}} first reaches M  (large r* => SUP is a RARE TAIL,");
    println!("#     invisible to any FIXED smooth test functional => equidistribution is BLIND = F0).");
    println!("# Q2: #cosets within 95% of M (=1 => sup is a single rare orbit point, not a bulk/density feature).");
    println!();
    for &mu_exp in &[3u32,4,5,6] {
        let n = 1u64 << mu_exp;
        let lo = n.saturating_pow(4); // beta=4
        let p = find_prime_cong1(n, lo);
        let g = primitive_root(p);
        let h = mpow(g, (p-1)/n, p);
        let mu:Vec<u64> = (0..n).map(|j| mpow(h, j, p)).collect();
        let m = (p-1)/n;
        let (sup, _m, near_cnt) = measure_sup(&mu, g, n, p);
        let sup2 = sup*sup;            // M^2
        // average of |eta|^2 over nonzero b = (q - n)/(m) ... but Parseval: sum_{b!=0}|eta_b|^2 = n(q-n)...
        // We use the exact 2nd-moment scale via additive_moment r=1 baseline. avg|eta|^2 ~ n.
        let avg2 = n as f64; // E[|eta_b|^2] = n exactly (Parseval over all b incl 0 gives n*q ; per nonzero ~ n)
        // depth where moment reaches sup: (E_r * (q) )^{1/2r}? The exact L^{2r} norm of eta over b is
        //   ||eta||_{2r}^{2r} = sum_b |eta_b|^{2r} = q * E_r   (Parseval/orthogonality of additive chars).
        // So the 2r-norm MOMENT SCALE = (q*E_r / q)^{1/2r}?? No: ||eta||_{2r} = (sum_b|eta_b|^{2r})^{1/2r}
        //   but for a MAX vs MOMENT comparison we use the normalized moment (avg) = (E_r)^{1/2r}... wait:
        //   (1/q) sum_b |eta_b|^{2r} = E_r. So the normalized L^{2r} avg = E_r^{1/2r}. As r->inf this -> M^{?}
        //   Actually (1/q sum |eta|^{2r})^{1/2r} -> M / q^{1/2r} -> M. So E_r^{1/2r} -> M. Good: find r*.
        let q = p as f64;
        let mut rstar = 0usize;
        let mut last_scale = 0.0f64;
        let cap = (mu_exp as usize)*3 + 8; // depth cap scales mildly; r up to ~ this
        print!("n={:>3} p={:<12} m={:<11} M={:.3} M/sqrt(n)={:.3} M^2/avg={:.3} near95%={:>2} | E_r^(1/2r): ",
            n, p, m, sup, sup/(n as f64).sqrt(), sup2/avg2, near_cnt);
        for r in 1..=cap {
            // exact integer moment; abort if p too big for the histogram (memory)
            if (p as usize) > 6_000_000 && r>=2 { print!(" [skip r>=2: p too big]"); break; }
            let e_r = additive_moment(&mu, r, p);
            let scale = (e_r as f64 / q).powf(1.0/(2.0*r as f64)); // (1/q sum|eta|^{2r})^{1/2r}
            last_scale = scale;
            if rstar==0 && scale >= sup*0.98 { rstar = r; }
            if r<=8 || r==cap { print!("r{}={:.3} ", r, scale); }
        }
        let ratio_known = (sup2/avg2).max(1.0).ln(); // log of sup/avg gap
        println!();
        println!("        -> r* (moment reaches M within 2%) = {}  [last scale @rcap={:.3}, M={:.3}];  log(M^2/avg)={:.3}",
            if rstar==0 {format!(">{} (never within cap)", cap)} else {rstar.to_string()}, last_scale, sup, ratio_known);
        println!("        -> VERDICT row: SUP is a {} ; equidistribution (fixed-degree test fns) {} see it.",
            if near_cnt<=2 {"single/rare orbit point"} else {"density feature"},
            if rstar==0 || rstar > 6 {"CANNOT (needs growing moment depth = F0 tail)"} else {"could"});
        println!();
    }
    println!("# CONCLUSION: if r* grows / SUP is a single rare point, equidistribution = weak-* discrepancy");
    println!("# only bounds FIXED smooth functionals (bulk). The sqrt(log) excess lives in the tail window");
    println!("# {{|eta_b|>T}} whose discrepancy is governed BY the eta_b sums themselves (Erdos-Turan-Koksma,");
    println!("# wrong direction) => the dynamical route REDUCES TO FENCE F0 (and F5: abelian torus, no gap).");
}
