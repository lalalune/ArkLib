// wf-F1: SUB-GAUSSIAN / HYPERCONTRACTIVITY structure of the nonprincipal period vector.
//
// The nonprincipal periods eta_b (b!=0, real, negation-closed) are conjectured sub-Gaussian
// with variance proxy ~ c*n.  A random variable X with E[X^{2r}] <= (2r-1)!! sigma^{2r} for all r
// is sub-Gaussian with psi_2 norm ~ sigma.  Here X = eta_b drawn uniformly over the m cosets
// (b!=0), and the moment route NEEDS E_r' = E_X[eta^{2r}]*(m/q?) ... let's be exact:
//   E_r' := (1/q) sum_{b!=0} eta_b^{2r}.  With m = (p-1)/n cosets each of size n, and eta const
//   on cosets, sum_{b!=0} eta_b^{2r} = n * sum_{cosets} eta^{2r}.  So
//   E_r' = (n/q) * sum_{c} eta_c^{2r} = ((p-1)/q) * AVG_c[eta^{2r}] ~ AVG_c[eta_c^{2r}].
// Thus E_r' ~ M_{2r} := (1/m) sum_c eta_c^{2r}  (the raw 2r-moment of the coset period vector).
// Sub-char-0  <=>  M_{2r} <= (2r-1)!! n^r  <=>  eta is sub-Gaussian with sigma^2 = n.
//
// MEASURE:
//  (1) the empirical psi_2 (sub-Gaussian) Orlicz norm of {eta_c/sqrt(n)}:
//      ||X||_psi2 = inf{ t>0 : (1/m) sum exp((eta/t)^2 / n) <= 2 }   (variance-proxy form / sqrt n)
//      Equivalently report K_psi2 = sup_r ( M_{2r} / [(2r-1)!! n^r] )^{1/r}  (the moment psi_2 const).
//  (2) the moment-growth constant K_eff(r) = (M_{2r}/[(2r-1)!! n^r])^{1/r}  vs r  (does it stay O(1)?).
//  (3) the MGF / exponential moment: log E[exp(lambda eta)] <= lambda^2 (c n)/2  => Gaussian tail.
//      Fit c = sup_lambda 2 log E[exp(lambda eta)] / (lambda^2 n).  c = sub-Gaussian variance proxy / n.
//  (4) n-scaling of all three constants (n=16..512) -> extrapolate to n=2^30.
//
// If psi_2 norm / sqrt(n) is BOUNDED (O(1)) as n grows, the moment route closes with C ~ that const.

use std::f64::consts::PI;
fn mpow(mut a:u64,mut e:u64,p:u64)->u64{let _=&mut a;let mut r=1u128;let mut a2=a as u128;let pp=p as u128;while e>0{if e&1==1{r=r*a2%pp;}a2=a2*a2%pp;e>>=1;}r as u64}
fn isp(n:u64)->bool{if n<2{return false}let mut d=2;while d*d<=n{if n%d==0{return false}d+=1}true}
fn fp(n:u64,lo:u64)->u64{let mut p=lo+((1+n-lo%n)%n);if p<=2{p+=n}loop{if p>2&&p%n==1&&isp(p){return p}p+=n}}
fn proot(p:u64)->u64{let mut m=p-1;let mut fs=vec![];let mut d=2;while d*d<=m{if m%d==0{fs.push(d);while m%d==0{m/=d}}d+=1}if m>1{fs.push(m)}let mut g=2;loop{if fs.iter().all(|&f|mpow(g,(p-1)/f,p)!=1){return g}g+=1}}
fn dfact(r:usize)->f64{let mut v=1.0;for j in 1..=r{v*=(2*j-1)as f64}v}

fn periods(n:u64,p:u64)->Vec<f64>{
    let g=proot(p);let h=mpow(g,(p-1)/n,p);
    let mu:Vec<u64>=(0..n).map(|j|mpow(h,j,p)).collect();
    let m=(p-1)/n; let gn=mpow(g,n,p);
    let mut eta=Vec::with_capacity(m as usize); let mut b=1u64;
    for _ in 0..m { let mut re=0.0; for &x in &mu{let t=((b as u128*x as u128)%p as u128)as u64;re+=(2.0*PI*(t as f64)/p as f64).cos();} eta.push(re); b=((b as u128*gn as u128)%p as u128)as u64; }
    eta
}

fn run(n:u64,p:u64,rmax:usize){
    let eta=periods(n,p);
    let m=eta.len() as f64;
    let lnq=(p as f64).ln();
    let beta=(p as f64).ln()/(n as f64).ln();
    let sqn=(n as f64).sqrt();

    // (1)+(2) moment psi_2 constant: K_eff(r) = (M_{2r}/[(2r-1)!! n^r])^{1/r}, K_psi2 = sup_r K_eff
    let mut kpsi2=0.0f64; let mut kpsi2_r=0usize;
    let mut keffs=vec![];
    for r in 1..=rmax {
        let mut s=0.0; for &e in &eta { s+=e.powi(2*r as i32); }
        let m2r = s/m;
        let c0 = dfact(r)*(n as f64).powi(r as i32);
        let ratio = m2r/c0;
        let keff = ratio.powf(1.0/r as f64);
        keffs.push((r,ratio,keff));
        if keff>kpsi2 { kpsi2=keff; kpsi2_r=r; }
    }

    // (3) MGF / exponential moment: c = sup_lambda  2 ln( (1/m) sum exp(lambda eta) ) / (lambda^2 n)
    // scan lambda in units of 1/sqrt(n) (natural scale). eta ~ O(sqrt(n log)).
    let mut cmgf=0.0f64; let mut cmgf_l=0.0;
    let mut lam=0.05/sqn;
    while lam < 6.0/sqn {
        // symmetric vector (negation closed) => use cosh form for stability
        let mut acc=0.0f64; for &e in &eta { acc += (lam*e).cosh(); } // E[exp(lam eta)] = E[cosh] by symmetry
        let logmgf = (acc/m).ln();
        let c = 2.0*logmgf/(lam*lam*(n as f64));
        if c>cmgf { cmgf=c; cmgf_l=lam*sqn; }
        lam *= 1.15;
    }

    // (1') Orlicz psi_2 norm directly:  ||X||_psi2 = inf{t: (1/m) sum exp((eta/t)^2) <= 2}, report /sqrt(n)
    // bisect t
    let f = |t:f64| { let mut acc=0.0f64; for &e in &eta { acc += ((e/t).powi(2)).exp(); } acc/m - 2.0 };
    let (mut lo, mut hi) = (1e-3, 1e6);
    // ensure f(lo)>0, f(hi)<0
    for _ in 0..200 { let mid=0.5*(lo+hi); if f(mid)>0.0 { lo=mid; } else { hi=mid; } }
    let psi2 = 0.5*(lo+hi);
    let psi2_norm = psi2/sqn;

    // max period / sqrt(n log(p/n)) (ground truth)
    let prize = ((n as f64)*((p as f64/n as f64).ln())).sqrt();
    let maxeta = eta.iter().cloned().fold(0.0f64,|a,b|a.max(b.abs()));

    println!("== n={} p={} m={} beta={:.2} lnq={:.1} sqrt(n)={:.2} ==",n,p,m as u64,beta,lnq,sqn);
    println!("   (1/2) K_psi2 = sup_r (M_2r/char0)^(1/r) = {:.4}  at r={}", kpsi2, kpsi2_r);
    println!("   (3) MGF variance-proxy c = sup_lam 2 ln E[e^{{lam eta}}]/(lam^2 n) = {:.4}  at lam*sqrt(n)={:.2}", cmgf, cmgf_l);
    println!("   (1') Orlicz ||eta||_psi2 / sqrt(n) = {:.4}", psi2_norm);
    println!("   ground truth max|eta|/prize = {:.4}   (prize={:.2})", maxeta/prize, prize);
    // print K_eff drift
    print!("   K_eff(r): ");
    for (r,_ratio,keff) in keffs.iter().step_by((rmax/8).max(1)) { print!("r{}={:.3} ",r,keff); }
    println!();
}

fn main(){
    // p ~ n^4 (beta ~ 4, prize regime). re-run at growing n to flag small-n artifacts.
    run(16,  fp(16,60000), 16);
    run(32,  fp(32,1_000_000), 20);
    run(64,  fp(64,16_000_000), 24);
    run(128, fp(128,260_000_000), 28);
    run(256, fp(256,4_000_000_000), 32);
    run(512, fp(512,68_000_000_000), 36);
}
