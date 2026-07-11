// mgfscan — diagnose the saddle: scan y, compute the Chernoff sup-norm certificate
//   M_cert(y) = arccosh( Psi_charp(y) ) / y   where Psi_charp(y)=sum_{b!=0} cosh(|eta_b| y),
// and compare its minimum-over-y to the prize floor sqrt(2 n log q).
// Also reports, AT the proposed saddle y*=sqrt(2 ln q / n):
//   Psi_charp(y*)/q^2,   and the char-0 reference split (Bessel envelope vs DC term).
// Usage: mgfscan <n> <beta_mult> [prime_offset_blocks]
use rayon::prelude::*;
#[inline] fn mulmod(a:u64,b:u64,p:u64)->u64{((a as u128*b as u128)%p as u128)as u64}
fn powmod(mut b:u64,mut e:u64,p:u64)->u64{let mut r=1u64;b%=p;while e>0{if e&1==1{r=mulmod(r,b,p);}b=mulmod(b,b,p);e>>=1;}r}
fn isprime(x:u64)->bool{if x<2{return false;}for &q in &[2u64,3,5,7,11,13,17,19,23,29,31,37]{if x%q==0{return x==q;}}let mut d=x-1;let mut s=0;while d%2==0{d/=2;s+=1;}'a:for &a in &[2u64,3,5,7,11,13,17,19,23,29,31,37]{let mut y=powmod(a,d,x);if y==1||y==x-1{continue;}for _ in 0..s-1{y=mulmod(y,y,x);if y==x-1{continue 'a;}}return false;}true}
fn factor(mut x:u64)->Vec<u64>{let mut f=vec![];let mut d=2;while d*d<=x{if x%d==0{f.push(d);while x%d==0{x/=d;}}d+=1;}if x>1{f.push(x);}f}
fn proot(p:u64)->u64{let fs=factor(p-1);for g in 2..p{if fs.iter().all(|&q|powmod(g,(p-1)/q,p)!=1){return g;}}0}

fn coset_periods(n:u64,p:u64)->Vec<f64>{
    let g=proot(p); let m=(p-1)/n;
    let h=powmod(g,(p-1)/n,p);
    let mu:Vec<u64>=(0..n).map(|i|powmod(h,i,p)).collect();
    let tau=2.0*std::f64::consts::PI/(p as f64);
    (0..m).into_par_iter().map(|j|{
        let b=powmod(g,j,p);
        let mut re=0.0f64; let mut im=0.0f64;
        for &x in &mu{let bx=mulmod(b,x,p) as f64;let a=tau*bx;re+=a.cos(); im+=a.sin();}
        re*re+im*im
    }).collect()
}
// log Psi_charp(y) = ln n + LSE_j logcosh(|eta_j| y)
fn log_psi(v:&[f64], y:f64, n:f64)->f64{
    let logcosh=|x:f64|->f64{ if x>20.0 {x-std::f64::consts::LN_2} else {x.cosh().ln()} };
    let logs:Vec<f64>=v.iter().map(|&x2|logcosh(x2.sqrt()*y)).collect();
    let lmax=logs.iter().cloned().fold(f64::NEG_INFINITY,f64::max);
    let lse=lmax+logs.iter().map(|&l|(l-lmax).exp()).sum::<f64>().ln();
    n.ln()+lse
}
fn main(){
    let args:Vec<String>=std::env::args().collect();
    let n:u64=args.get(1).and_then(|s|s.parse().ok()).unwrap_or(16);
    let beta:u32=args.get(2).and_then(|s|s.parse().ok()).unwrap_or(4);
    let off:u64=args.get(3).and_then(|s|s.parse().ok()).unwrap_or(0);
    let mut p=n.pow(beta); p+=(n+1-p%n)%n; let mut c=0;
    while !(p%n==1&&isprime(p)) || c<off { if p%n==1&&isprime(p){c+=1;} p+=n; }
    let nf=n as f64; let lq=(p as f64).ln();
    let v=coset_periods(n,p);
    let m2max=v.iter().cloned().fold(0.0,f64::max);
    let floor=(2.0*nf*lq).sqrt();   // prize floor sqrt(2 n log q)
    let ystar=(2.0*lq/nf).sqrt();
    println!("# n={} p={} beta={:.3} m={} floor=sqrt(2n ln q)={:.3} sup|eta|=Mtop={:.3} (Mtop/floor={:.3})",
        n,p,lq/nf.ln(),v.len(),floor,m2max.sqrt(),m2max.sqrt()/floor);
    println!("# y-scan: M_cert(y)=arccosh(Psi(y))/y  (Chernoff sup-norm certificate; min over y is the bound)");
    println!("# {:>7} {:>10} {:>10} {:>10}", "y","lnPsi/lnq","Mcert","Mcert/floor");
    let mut best=f64::INFINITY; let mut besty=0.0;
    let mut yy=0.2;
    while yy<=2.5 {
        let lp=log_psi(&v,yy,nf);
        // arccosh(Psi)=ln(Psi+sqrt(Psi^2-1))~ln(2 Psi)=ln2+lnPsi for large Psi
        let mcert=(std::f64::consts::LN_2+lp)/yy;
        if mcert<best {best=mcert;besty=yy;}
        if (yy*10.0).round() as i64 % 2 == 0 {
            println!("{:>7.3} {:>10.4} {:>10.3} {:>10.4}", yy, lp/lq, mcert, mcert/floor);
        }
        yy+=0.05;
    }
    println!("# BEST: y={:.3} M_cert={:.3} M_cert/floor={:.4}   (saddle y*={:.3})", besty,best,best/floor,ystar);
    // at saddle:
    let lp_star=log_psi(&v,ystar,nf);
    println!("# AT SADDLE y*={:.4}: Psi_cp=q^{:.4} (Psi/q^2=q^{:.4}={:.3e})  Mcert={:.3} (/floor={:.4})",
        ystar, lp_star/lq, lp_star/lq-2.0, (lp_star-2.0*lq).exp(),
        (std::f64::consts::LN_2+lp_star)/ystar, (std::f64::consts::LN_2+lp_star)/ystar/floor);
}
