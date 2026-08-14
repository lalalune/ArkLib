// mgfwrap — the CLEAN wraparound-excess object.
//
// FULL MGF identity (exact, CoshMGFIdentity.lean):
//   Phi_charp(y) := sum_{b in F} cosh(|eta_b| y) = sum_r (q E_r^{charp}/(2r)!) y^{2r}.
//   char-0:        Phi_0(y)     := q * I0(2y)^{n/2}  = sum_r (q E_r^{char0}/(2r)!) y^{2r}.
// The WRAPAROUND EXCESS is the difference of generating functions:
//   W(y) := Phi_charp(y) - Phi_0(y) = (q/?) sum_r (E_r^{charp}-E_r^{char0})/(2r)! y^{2r}.
// This is the Lam-Leung short-relation object integrated against the Poisson(log q) weight
// (the (2r)! y^{2r} weights ARE the Poisson weights at the saddle).  W>=0 always (wraparound
// only ADDS coincidences in char p).  The DC term cosh(n y) is IDENTICAL in both (eta_0=n both),
// so it cancels EXACTLY in W: W = sum_{b!=0}(charp) - [Phi_0 - cosh(n y)] = the b!=0 excess too.
//
// budget: char-0 slack = q^2 - Phi_0(y*).  We report:
//   W/q^2          (excess as fraction of budget)
//   W/Phi_0        (excess relative to char-0 reference)
//   W as power of q,  Phi_0 as power of q,  Phi_charp as power of q
//   slack_used = W / (q^2 - Phi_0)   (does the excess fit in the char-0 slack? <1 = comfortable)
//
// Usage: mgfwrap <n> <num_primes> <beta_mult>
use rayon::prelude::*;
#[inline] fn mulmod(a:u64,b:u64,p:u64)->u64{((a as u128*b as u128)%p as u128)as u64}
fn powmod(mut b:u64,mut e:u64,p:u64)->u64{let mut r=1u64;b%=p;while e>0{if e&1==1{r=mulmod(r,b,p);}b=mulmod(b,b,p);e>>=1;}r}
fn isprime(x:u64)->bool{if x<2{return false;}for &q in &[2u64,3,5,7,11,13,17,19,23,29,31,37]{if x%q==0{return x==q;}}let mut d=x-1;let mut s=0;while d%2==0{d/=2;s+=1;}'a:for &a in &[2u64,3,5,7,11,13,17,19,23,29,31,37]{let mut y=powmod(a,d,x);if y==1||y==x-1{continue;}for _ in 0..s-1{y=mulmod(y,y,x);if y==x-1{continue 'a;}}return false;}true}
fn factor(mut x:u64)->Vec<u64>{let mut f=vec![];let mut d=2;while d*d<=x{if x%d==0{f.push(d);while x%d==0{x/=d;}}d+=1;}if x>1{f.push(x);}f}
fn proot(p:u64)->u64{let fs=factor(p-1);for g in 2..p{if fs.iter().all(|&q|powmod(g,(p-1)/q,p)!=1){return g;}}0}
fn v2(mut x:u64)->u32{let mut v=0;while x%2==0{x/=2;v+=1;}v}
fn bessel_i0(z:f64)->f64{ if z<30.0{let mut t=1.0f64;let mut s=1.0f64;let h2=(z*0.5)*(z*0.5);for k in 1..300{t*=h2/((k as f64)*(k as f64));s+=t;if t<s*1e-18{break;}}s}else{let c=1.0+1.0/(8.0*z)+9.0/(128.0*z*z)+225.0/(3072.0*z*z*z);z.exp()/(2.0*std::f64::consts::PI*z).sqrt()*c}}
fn log_i0(z:f64)->f64{ if z<30.0{bessel_i0(z).ln()}else{let c=1.0+1.0/(8.0*z)+9.0/(128.0*z*z)+225.0/(3072.0*z*z*z);z-0.5*(2.0*std::f64::consts::PI*z).ln()+c.ln()}}
fn coset_periods(n:u64,p:u64)->Vec<f64>{
    let g=proot(p); let m=(p-1)/n; let h=powmod(g,(p-1)/n,p);
    let mu:Vec<u64>=(0..n).map(|i|powmod(h,i,p)).collect();
    let tau=2.0*std::f64::consts::PI/(p as f64);
    (0..m).into_par_iter().map(|j|{let b=powmod(g,j,p);let mut re=0.0f64;let mut im=0.0f64;
        for &x in &mu{let bx=mulmod(b,x,p) as f64;let a=tau*bx;re+=a.cos();im+=a.sin();}re*re+im*im}).collect()
}
fn main(){
    let args:Vec<String>=std::env::args().collect();
    let n:u64=args.get(1).and_then(|s|s.parse().ok()).unwrap_or(16);
    let num:usize=args.get(2).and_then(|s|s.parse().ok()).unwrap_or(8);
    let beta:u32=args.get(3).and_then(|s|s.parse().ok()).unwrap_or(4);
    let mut p=n.pow(beta); p+=(n+1-p%n)%n; let nf=n as f64;
    println!("# n={} beta-target={} base=n^{}={}",n,beta,beta,n.pow(beta));
    println!("# FULL-MGF wraparound excess W = Phi_charp - Phi_0(Bessel).  saddle y*^2=2 ln q/n. budget q^2.");
    println!("# {:>13} {:>3} {:>6} {:>7} {:>8} {:>8} {:>8} {:>9} {:>9} {:>10}",
             "p","v2","beta","y*","Phicp_q","Phi0_q","W_q","W/q^2","W/Phi0","W/slack");
    let mut found=0;
    while found<num{
        if p%n==1 && isprime(p){
            let lq=(p as f64).ln(); let beff=lq/nf.ln();
            let ystar=(2.0*lq/nf).sqrt();
            let v=coset_periods(n,p); let m=v.len() as f64;
            let logcosh=|x:f64|->f64{ if x>20.0 {x-std::f64::consts::LN_2} else {x.cosh().ln()} };
            // Phi_charp = cosh(n y*) [b=0]  + n * sum_j cosh(|eta_j| y*)  [b!=0]
            // log-domain LSE over: one term ln cosh(n y*), and m terms ln n + logcosh(|eta_j| y*)
            let mut logs:Vec<f64>=Vec::with_capacity(v.len()+1);
            logs.push(logcosh(nf*ystar));                       // b=0 DC
            for &x2 in &v { logs.push(nf.ln()+logcosh(x2.sqrt()*ystar)); }
            let lmax=logs.iter().cloned().fold(f64::NEG_INFINITY,f64::max);
            let log_phicp=lmax+logs.iter().map(|&l|(l-lmax).exp()).sum::<f64>().ln();
            // Phi_0 = q I0(2y*)^{n/2}
            let log_phi0=lq+(nf/2.0)*log_i0(2.0*ystar);
            // W = Phi_charp - Phi_0 (>=0 expected).  log-safe subtraction.
            let (log_w, w_sign);
            if log_phicp>log_phi0 { let r=(log_phi0-log_phicp).exp(); log_w=log_phicp+(1.0-r).ln(); w_sign=1.0; }
            else { let r=(log_phicp-log_phi0).exp(); log_w=log_phi0+(1.0-r).ln(); w_sign=-1.0; }
            let log2q=2.0*lq;
            // slack = q^2 - Phi_0  (char-0 budget headroom).  Phi_0 < q^2 always here? check power.
            let (log_slack, slack_pos);
            if log2q>log_phi0 { let r=(log_phi0-log2q).exp(); log_slack=log2q+(1.0-r).ln(); slack_pos=true; }
            else { log_slack=f64::NAN; slack_pos=false; }
            let w_over_q2 = w_sign*(log_w-log2q).exp();
            let w_over_phi0 = w_sign*(log_w-log_phi0).exp();
            let w_over_slack = if slack_pos { w_sign*(log_w-log_slack).exp() } else { f64::NAN };
            println!("{:>15} {:>3} {:>6.3} {:>7.4} {:>8.4} {:>8.4} {:>8.4} {:>9.2e} {:>9.2e} {:>10.3e}",
                p, v2(p-1), beff, ystar, log_phicp/lq, log_phi0/lq, w_sign*log_w/lq,
                w_over_q2, w_over_phi0, w_over_slack);
            let _=m;
            found+=1;
        }
        p+=n;
    }
}
