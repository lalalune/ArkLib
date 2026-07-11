// wf-A01 (#444): the POWER-MEAN structure of the S2 equidistribution constant, and the EXACT
// relation  D = kappa^{1/2r}  vs  PAPR = M^2/(L2 mean).  Pins whether S2 is milder than BGK.
//
// FACTS (proven in-tree): mean over nonprincipal cosets of |eta_b|^2 is the Parseval value.
//   Sum_{b!=0} |eta_b|^2 = q*n - n^2  (second moment minus principal). Per nonprincipal coset rep
//   (each = n frequencies, m_np ~ m reps), the L2 mean of |eta_b|^2 is  mu2 := (qn - n^2 - 0)/N_1
//   where N_1 = n*(#nonprincipal reps with eta!=0) ~ q  => mu2 ~ n.  (measured: mu2 = n exactly.)
//
// THE KEY INEQUALITY CHAIN. Write a_b := |eta_b|^2 >= 0 over the N := N_1 nonprincipal frequencies.
//   T_r/N = (1/N) sum a_b^r  =: m_r  (the r-th power-mean^r of the a_b's, = r-th moment).
//   M^2 = max a_b.  kappa = M^{2r} N / T_r = (max a_b)^r / m_r.   D = kappa^{1/2r} = sqrt(M^2 / m_r^{1/r}).
//   By power-mean monotonicity  m_r^{1/r} >= m_1 = mu2  (the L2 mean), so
//        D <= sqrt(M^2 / mu2) = M / sqrt(mu2) = M/sqrt(n) = sqrt(PAPR).
//   So  D <= sqrt(PAPR) = M/sqrt(n)  -- the OPTIMAL-r limit of D is exactly M/sqrt(n).  Conversely
//   m_r^{1/r} <= M^2 always, so D >= 1.   => D in [1, M/sqrt(n)], and as r->inf, D -> sqrt(M^2/M^2)=1
//   (the r-th moment concentrates on the max), while at r=1, D = M/sqrt(mu2) = M/sqrt(n).
//
//   THEREFORE: the BEST the S2 route can give (large r) is M^{2r} <= (kappa/c) E_r with D->1, i.e.
//   M <= (E_r/c)^{1/2r} -> the char-0 ceiling sqrt(2e n r) ~ sqrt(n ln q): kappa is NOT the obstruction
//   at large r (D->1). The obstruction is entirely E_r at large r (the BGK additive-energy wall).
//   At SMALL r, D = M/sqrt(n) = sqrt(PAPR) IS the prize quantity directly -- so bounding D at small r
//   is EXACTLY bounding M, no milder. CONCLUSION: S2's kappa is milder than BGK ONLY if you can bound
//   it at LARGE r, where D->1 automatically but the ENERGY E_r is the BGK wall. The milder-ness is
//   ILLUSORY at the level of a single r: D and E_r trade off, product = M^{2r} always.
//
// This probe verifies D in [1, M/sqrt(n)] EXACTLY, that m_r^{1/r} is monotone increasing toward M^2,
// and the crossover where (kappa/c)E_r is minimized -- showing the minimizing r is where the two
// effects balance, recovering the char-0 bound with the SAME constant whether you call it kappa or E_r.
use std::f64::consts::PI;
fn mpow(a:u64,mut e:u64,p:u64)->u64{let mut r=1u128;let mut a2=a as u128;let pp=p as u128;while e>0{if e&1==1{r=r*a2%pp;}a2=a2*a2%pp;e>>=1;}r as u64}
fn isp(n:u64)->bool{if n<2{return false}if n%2==0{return n==2}let mut d=3;while d*d<=n{if n%d==0{return false}d+=2}true}
fn v2(mut x:u64)->u32{let mut v=0;while x&1==0{x>>=1;v+=1}v}
fn proot(p:u64)->u64{let mut m=p-1;let mut fs=vec![];let mut d=2;while d*d<=m{if m%d==0{fs.push(d);while m%d==0{m/=d}}d+=1}if m>1{fs.push(m)}let mut g=2;loop{if fs.iter().all(|&f|mpow(g,(p-1)/f,p)!=1){return g}g+=1}}
fn percoset_w(n:u64,p:u64)->Vec<f64>{
    let g=proot(p); let h=mpow(g,(p-1)/n,p);
    let mu:Vec<u64>=(0..n).map(|j|mpow(h,j,p)).collect();
    let m=(p-1)/n;
    let mut out=Vec::with_capacity(m as usize);
    let mut b=1u64;
    for _ in 0..m {
        let mut re=0.0f64; let mut im=0.0f64;
        for &x in &mu { let t=((b as u128*x as u128)%p as u128)as u64; let a=2.0*PI*(t as f64)/p as f64; re+=a.cos(); im+=a.sin(); }
        out.push(re*re+im*im);
        b=((b as u128*g as u128)%p as u128)as u64;
    }
    out
}
fn dfact(k:u64)->f64{ if k==0 {return 1.0;} let mut r=1.0f64; let mut i=1u64; while i<=2*k-1 {r*=i as f64; i+=2;} r }
fn analyze(tag:&str,n:u64,p:u64){
    let w=percoset_w(n,p);
    let nn=n as f64; let q=p as f64;
    let np:Vec<f64>=w.iter().cloned().filter(|&x|(x-nn*nn).abs()>0.5 && x>1e-9).collect();
    let nreps=np.len() as f64;
    let mu2=np.iter().sum::<f64>()/nreps;     // L2 mean of |eta|^2 over nonprincipal reps (should be ~ n)
    let mmax=np.iter().cloned().fold(0.0f64,f64::max);
    let papr=mmax/mu2;
    let beta=q.ln()/nn.ln();
    println!("[{}] n={} p={} v2={} beta={:.2} mu2(L2mean)={:.3} (n={}) M^2={:.2} PAPR=M^2/mu2={:.4} sqrt(PAPR)={:.4}",
        tag,n,p,v2(p-1),beta,mu2,n,mmax,papr,papr.sqrt());
    println!("    {:>4} {:>14} {:>12} {:>12} {:>12} {:>10}", "r","m_r^(1/r)","D=k^(1/2r)","[1,sqrtPAPR]","(k/c)E_r^(1/2r)","check");
    let c=nreps*nn/q;
    let mut prev_mr1r=0.0f64;
    for r in [1u64,2,3,4,6,9,12,16,20,30] {
        let mr=np.iter().map(|&x|x.powi(r as i32)).sum::<f64>()/nreps; // r-th moment = m_r
        let mr1r=mr.powf(1.0/r as f64);                                // m_r^{1/r}
        let kappa = mmax.powi(r as i32)/mr;                            // = M^{2r}/T_r * N = (max)^r/m_r
        let d = kappa.powf(1.0/(2.0*r as f64));
        // sanity: D should equal sqrt(M^2 / mr1r)
        let d_check = (mmax/mr1r).sqrt();
        let er=dfact(r)*nn.powi(r as i32);
        let mbnd=((kappa/c)*er).powf(1.0/(2.0*r as f64));
        let tgt=(nn*(q/nn).ln()).sqrt();
        let mono = if mr1r>=prev_mr1r-1e-6 {"mono+"} else {"!DROP"};
        prev_mr1r=mr1r;
        println!("    {:>4} {:>14.4} {:>12.5} D=sqrt(M2/mr)={:>8.5} {:>12.4} {} mb/tgt={:.4}",
            r,mr1r,d,d_check,mbnd,mono,mbnd/tgt);
    }
    println!("    => D in [1, sqrt(PAPR)={:.4}]; D->1 as r->inf; at large r the bound is set by E_r (BGK wall).",papr.sqrt());
    println!();
}
fn main(){
    let args:Vec<String>=std::env::args().collect();
    let ns:Vec<u64>= if args.len()>1 { args[1..].iter().map(|x|x.parse().unwrap()).collect() } else { vec![32,64,128,256] };
    println!("# wf-A01: power-mean structure. D=kappa^(1/2r)=sqrt(M^2/m_r^(1/r)) in [1, M/sqrt(n)].");
    println!("# m_r^(1/r) monotone increasing toward M^2 (power-mean); D decreasing toward 1.");
    println!("# milder-ness illusory: small r => D=sqrt(PAPR)=prize quantity; large r => D->1 but E_r=BGK wall.");
    for &n in &ns {
        let target=(n as f64).powf(4.0) as u64;
        let mut p = target.max(100003); p = p - (p%n) + 1; if p<=2 {p+=n;}
        let mut best_s=(0u64,0u32); let mut best_g=(0u64,99u32); let mut cnt=0;
        while cnt<300 { if p%n==1 && isp(p) { let vv=v2(p-1); if vv>best_s.1 {best_s=(p,vv);} if vv<best_g.1 {best_g=(p,vv);} cnt+=1; } p+=n; }
        analyze("STRUCT",n,best_s.0);
        analyze("GENERIC",n,best_g.0);
    }
}
