// wf-A06: prize-scale extrapolation of the effective-Chebotarev bad-prime bound (#444).
//
// The exact enumeration (probe_wfA06_chebotarev_density.rs) caps at n<=64, small w. This probe
// computes the ANALYTIC prize-scale numbers (n=2^30, beta=4, r ~ ln q) for the three quantities
// that decide the A06 verdict, all in log2:
//
//   W(n,beta)  = window supply  ~ (n^{beta+1}-n^beta)/(phi(n) ln(n^beta))   (PNT in AP, TZ24 input)
//   UCfg(n,r)  = effective-Chebotarev UNION upper bound on bad primes
//              = #configs * avg_omega ,  #configs = C(phi(n), 2r) * 2^{2r},  avg_omega ~ phi(n)*c/ln(p)
//   r*         = depth at which the UNION bound crosses W (effective-Chebotarev fails above this)
//
// All exact integer/float in log2; no enumeration. The point: show UCfg/W -> +infinity already at
// r = O(1), so the effective-Chebotarev (Lagarias-Odlyzko / Bach-Sorenson-GRH) union count CANNOT
// certify the prize prime good at depth r ~ ln q. The real density is much smaller (measured 0.0025
// at n=32 w=8) but is INACCESSIBLE to effective Chebotarev -- accessing it = resolving per-prime norm
// structure = the BGK wall.
//
// build: rustc -O probe_wfA06_prize_extrapolation.rs -o /tmp/wfA06x

fn log2choose(n: f64, k: f64) -> f64 {
    // log2 C(n,k) via lgamma
    fn lgamma(x: f64) -> f64 { // Lanczos
        let g = 7.0;
        let c = [0.99999999999980993,676.5203681218851,-1259.1392167224028,
                 771.32342877765313,-176.61502916214059,12.507343278686905,
                 -0.13857109526572012,9.9843695780195716e-6,1.5056327351493116e-7];
        if x < 0.5 {
            std::f64::consts::PI / ((std::f64::consts::PI*x).sin() * (1.0 - x).exp().ln().exp())
                ; // unused branch (we only call x>=1)
        }
        let x = x - 1.0;
        let mut a = c[0];
        let t = x + g + 0.5;
        for i in 1..9 { a += c[i]/(x + i as f64); }
        0.5*(2.0*std::f64::consts::PI).ln() + (x+0.5)*t.ln() - t + a.ln()
    }
    (lgamma(n+1.0) - lgamma(k+1.0) - lgamma(n-k+1.0)) / std::f64::consts::LN_2
}

fn main(){
    let mu: f64 = 30.0;          // n = 2^mu = 2^30  (prize scale)
    let beta: f64 = 4.0;
    for &mu in &[10.0_f64, 20.0, 30.0] {
        let n = (2.0_f64).powf(mu);
        let phi = n/2.0;                          // phi(2^mu) = 2^{mu-1}
        let logp = beta*mu;                       // log2 p, p ~ n^beta = 2^{beta*mu}
        let lnp = logp*std::f64::consts::LN_2;    // ln p
        // window supply W (log2): primes ==1 mod n in [n^beta, n^{beta+1}] ~ n^{beta+1}/(phi * ln(n^{beta+1}))
        // dominant term: count ~ (n^{beta+1})/(phi(n) * ln(n^{beta+1}))
        let logW = (beta+1.0)*mu - (mu-1.0) - ((beta+1.0)*mu*std::f64::consts::LN_2).log2();
        // depth r ~ ln q = ln p (the deep depth that bounds M via the moment method min over r~ln q)
        let r_deep = lnp; // r ~ ln p
        println!("== n=2^{} (phi=2^{}), beta={}, log2 p={:.0}, r_deep~ln p={:.1} ==", mu as u32, (mu-1.0) as u32, beta, logp, r_deep);
        println!("   log2 W (window supply)            = {:.2}   (~ n^{:.0}/log)", logW, beta-1.0);
        println!("   r    2r    log2(#configs)     log2(avg_omega)   log2(UCfg union-UB)   log2(UCfg/W)");
        for &r in &[1.0_f64, 2.0, 4.0, 8.0, r_deep.round()] {
            let w = 2.0*r;
            if w > phi { continue; }
            let logcfg = log2choose(phi, w) + w; // C(phi,2r)*2^{2r}
            // avg omega(|N|) <= log2|N| ~ phi*c_w (c_w in (0,1], ~1 for large w). Use c=1 (generous to Chebotarev).
            // but only band-prime factors count; a norm of size 2^{phi*c} has at most logp/... primes in [n^4,n^5].
            // #band-prime-factors per norm <= log2|N| / log2(n^beta) = phi*c / (beta*mu). Use c=1.
            let bandfac_per_norm = (phi*1.0)/(beta*mu);
            let logavgomega = bandfac_per_norm.max(1.0).log2();
            let logUC = logcfg + logavgomega;
            println!("   {:>2}   {:>3}   {:>14.2}     {:>14.2}     {:>17.2}     {:>+12.2}",
                     r as i64, w as i64, logcfg, logavgomega, logUC, logUC - logW);
        }
        println!();
    }
    let _=mu;

    // Effective-Chebotarev crossover: the smallest r with UCfg >= W. Since log2 C(phi,2r) >= 2r*log2(phi/(2r)),
    // already log2(#configs) > logW once 2r*log2(phi/(2r)) > logW ~ (beta-2)*mu. Solve for r.
    println!("== Effective-Chebotarev UNION bound crossover r* (UCfg crosses W) ==");
    for &mu in &[10.0_f64,20.0,30.0,40.0] {
        let n=(2.0_f64).powf(mu); let phi=n/2.0;
        let logW = (beta+1.0)*mu - (mu-1.0) - ((beta+1.0)*mu*std::f64::consts::LN_2).log2();
        let mut rstar=0i64;
        for r in 1..=200 {
            let w=2.0*(r as f64); if w>phi {break;}
            let bandfac=((phi)/(beta*mu)).max(1.0).log2();
            let logUC=log2choose(phi,w)+w+bandfac;
            if logUC>=logW { rstar=r; break; }
        }
        println!("   n=2^{}: log2 W={:.1}, union-UB crosses W at r*={}  (deep depth r~ln p={:.0}) => {}",
                 mu as u32, logW, rstar, beta*mu*std::f64::consts::LN_2,
                 if (rstar as f64) < beta*mu*std::f64::consts::LN_2 {"UNION BOUND USELESS at deep depth"} else {"ok"});
    }
}
