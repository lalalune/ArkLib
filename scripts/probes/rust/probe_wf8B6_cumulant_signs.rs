// B6 PRE-SCREEN: cumulants kappa_{2r} of the NONPRINCIPAL period law X=eta_b (b!=0).
// X symmetric (negation-closed): odd moments 0. M_r = E[X^{2r}] over b!=0 (exclude principal eta_0=n).
// kappa_2 = M_1 (=variance, should be ~n). Gaussian: kappa_{2r}=0 for r>=2.
// SUB-GAUSSIAN / negative excess: kappa_{2r} <= 0 for r>=2.
// Also test: m_r=M_r/W_r (W_r=(2r-1)!!n^r) LOG-CONVEX <=> R(r)=m_{r+1}/m_r antitone.
// And the LINK: does kappa_{2r}<=0 force m_r<=1?  And does it force R antitone?
use std::f64::consts::PI;
fn mpow(mut a:u64,mut e:u64,p:u64)->u64{let mut r=1u128;let mut a2=a as u128;let pp=p as u128;while e>0{if e&1==1{r=r*a2%pp;}a2=a2*a2%pp;e>>=1;}r as u64}
fn isp(n:u64)->bool{if n<2{return false}let mut d=2;while d*d<=n{if n%d==0{return false}d+=1}true}
fn fp(n:u64,lo:u64)->u64{let mut p=lo+((1+n-lo%n)%n);if p<=2{p+=n}loop{if p>2&&p%n==1&&isp(p){return p}p+=n}}
fn proot(p:u64)->u64{let mut m=p-1;let mut fs=vec![];let mut d=2;while d*d<=m{if m%d==0{fs.push(d);while m%d==0{m/=d}}d+=1}if m>1{fs.push(m)}let mut g=2;loop{if fs.iter().all(|&f|mpow(g,(p-1)/f,p)!=1){return g}g+=1}}
fn dfact(r:usize)->f64{let mut v=1.0;for j in 1..=r{v*=(2*j-1)as f64}v} // (2r-1)!!

// Full moments mu_k = E[X^k] (k even nonzero, k odd =0 by symmetry). Compute up to k=2*RMAX.
// Cumulants from moments via the recursion: kappa_k = mu_k - sum_{j=1}^{k-1} C(k-1,j-1) kappa_j mu_{k-j}.
fn binom(n:usize,k:usize)->f64{ if k>n{return 0.0} let mut r=1.0; for i in 0..k { r*= (n-i) as f64/(i+1) as f64; } r }
fn cumulants(mu:&[f64])->Vec<f64>{ // mu[0]=1 (mu_0), mu[k]=E[X^k]
    let kmax=mu.len()-1;
    let mut kap=vec![0.0;kmax+1];
    for k in 1..=kmax {
        let mut s=mu[k];
        for j in 1..k { s -= binom(k-1,j-1)*kap[j]*mu[k-j]; }
        kap[k]=s;
    }
    kap
}

fn run(n:u64,p:u64,rmax:usize){
    let g=proot(p);let h=mpow(g,(p-1)/n,p);
    let mu_set:Vec<u64>=(0..n).map(|j|mpow(h,j,p)).collect();
    let m=(p-1)/n;let gn=mpow(g,n,p);
    // periods eta_b for b in nonzero coset reps; exclude principal (b s.t. eta_b ~ n, i.e. b=0 not in list, but the coset of squares gives eta=n? No: b ranges over all nonzero, eta_b = sum cos(2pi b x/p)). Principal is b=0 only.
    // We want X over b!=0. The list b=1,gn,gn^2,... covers one rep per coset; all are b!=0. Good.
    let mut eta=Vec::with_capacity(m as usize);let mut b=1u64;
    for _ in 0..m{let mut re=0.0;for &x in &mu_set{let t=((b as u128*x as u128)%p as u128)as u64;re+=(2.0*PI*(t as f64)/p as f64).cos();}eta.push(re);b=((b as u128*gn as u128)%p as u128)as u64;}
    let mc=m as f64;
    // raw even moments mu_{2r}=E[X^{2r}] over the m periods (each coset rep weighted equally; this is the b!=0 average)
    let kmax=2*rmax;
    let mut momv=vec![0.0;kmax+1];
    momv[0]=1.0;
    for k in 1..=kmax {
        if k%2==1 { // odd: should be ~0 by symmetry; compute to verify
            let mut s=0.0; for &e in &eta { s+= e.powi(k as i32); } momv[k]=s/mc;
        } else {
            let mut s=0.0; for &e in &eta { s+= e.powi(k as i32); } momv[k]=s/mc;
        }
    }
    let kap=cumulants(&momv);
    let beta=(p as f64).ln()/(n as f64).ln();
    println!("== n={} p={} beta={:.2} lnq={:.1} bandDepth r~{:.0} ==", n,p,beta,(p as f64).ln(),(p as f64).ln());
    println!("  kappa_2 (variance) = {:.3}  (n={})  std excess: kappa_2/n={:.4}", kap[2], n, kap[2]/n as f64);
    // print kappa_{2r} and standardized excess kappa_{2r}/kappa_2^r (dimensionless; Gaussian=0 for r>=2)
    println!("   r   M_r=mu_2r        m_r=M_r/W_r   kappa_2r           kap2r/kap2^r(std)  R(r)=m_{{r+1}}/m_r");
    let mut mr=vec![0.0;rmax+2];
    for r in 1..=rmax { mr[r]= momv[2*r]/(dfact(r)*(n as f64).powi(r as i32)); }
    for r in 1..=rmax {
        let std = kap[2*r]/kap[2].powi(r as i32);
        let rr = if r<rmax { mr[r+1]/mr[r] } else { f64::NAN };
        println!("  {:3}  {:14.3}  {:11.5}  {:+16.4}  {:+14.6}     {:.5}", r, momv[2*r], mr[r], kap[2*r], std, rr);
    }
    // antitone check on R, and log-convexity of m_r (m_r^2 <= m_{r-1} m_{r+1})
    let mut antitone=true; let mut worst=f64::NEG_INFINITY;
    for r in 2..rmax { let inc=(mr[r+1]/mr[r])-(mr[r]/mr[r-1]); if inc>worst{worst=inc;} if inc>1e-7{antitone=false;} }
    // negative-excess check r>=2
    let mut allneg=true; let mut worstpos=f64::NEG_INFINITY;
    for r in 2..=rmax { let s=kap[2*r]/kap[2].powi(r as i32); if s>worstpos{worstpos=s;} if s>1e-7{allneg=false;} }
    println!("  --> R antitone(r>=2): {}  worstStepInc={:+.6}", antitone, worst);
    println!("  --> kappa_2r<=0 (r>=2, sub-Gaussian): {}  worstStdExcess={:+.6}", allneg, worstpos);
    println!();
}
fn main(){
    run(8,  fp(8, 4000), 7);
    run(16, fp(16,60000), 8);
    run(32, fp(32,1000000), 9);
    run(64, fp(64,16000000), 10);
    run(128,fp(128,260000000), 11);
    // prize-ish beta sweep at fixed n to test char-p robustness of sign
    println!("### higher-beta (deeper char-p) at n=32 ###");
    run(32, fp(32, (32f64.powf(6.0)) as u64), 9);
    run(32, fp(32, (32f64.powf(8.0)) as u64), 9);
}
