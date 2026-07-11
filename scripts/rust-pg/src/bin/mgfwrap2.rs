// mgfwrap2 — DEFINITIVE wraparound-excess of the DC-subtracted prize MGF.
//
// EXACT identities (in-tree):
//   Sum_{b in F}|eta_b|^{2r} = q E_r^{charp}            (subgroup_gaussSum_moment)
//   Sum_{b!=0}  |eta_b|^{2r} = q E_r^{charp} - n^{2r}   (sum_nonzero_moment; eta_0=n)
//   Sum_r E_r^{char0}/(2r)! y^{2r} = I0(2y)^{n/2}       (Bessel even-moment law)
//
// Prize MGF (DC-subtracted):
//   Psi(y) = Sum_{b!=0} cosh(|eta_b|y) = q I0(2y)^{n/2} - cosh(n y) + W(y),
//   W(y) = q * Sum_r (E_r^{charp}-E_r^{char0})/(2r)! y^{2r}   (the WRAPAROUND EXCESS, >=0).
//
//   char-0 prediction for the b!=0 mass:  P0(y) := q I0(2y)^{n/2} - cosh(n y).
//   So  Psi(y) = P0(y) + W(y),  and  W = Psi - P0.
//
// Saddle for the prize Chernoff bound on M=max_{b!=0}|eta_b|: minimize arccosh(Psi(y))/y over y.
// Budget: Psi(y*) <= q^2  certifies  M <= sqrt(2 n log q) (the floor).
// char-0 slack at the OPTIMAL y_opt:  q^2 - P0(y_opt).   Question: is W(y_opt) << that slack?
//
// Usage: mgfwrap2 <n> <num_primes> <beta_mult>
use rayon::prelude::*;
#[inline] fn mulmod(a:u64,b:u64,p:u64)->u64{((a as u128*b as u128)%p as u128)as u64}
fn powmod(mut b:u64,mut e:u64,p:u64)->u64{let mut r=1u64;b%=p;while e>0{if e&1==1{r=mulmod(r,b,p);}b=mulmod(b,b,p);e>>=1;}r}
fn isprime(x:u64)->bool{if x<2{return false;}for &q in &[2u64,3,5,7,11,13,17,19,23,29,31,37]{if x%q==0{return x==q;}}let mut d=x-1;let mut s=0;while d%2==0{d/=2;s+=1;}'a:for &a in &[2u64,3,5,7,11,13,17,19,23,29,31,37]{let mut y=powmod(a,d,x);if y==1||y==x-1{continue;}for _ in 0..s-1{y=mulmod(y,y,x);if y==x-1{continue 'a;}}return false;}true}
fn factor(mut x:u64)->Vec<u64>{let mut f=vec![];let mut d=2;while d*d<=x{if x%d==0{f.push(d);while x%d==0{x/=d;}}d+=1;}if x>1{f.push(x);}f}
fn proot(p:u64)->u64{let fs=factor(p-1);for g in 2..p{if fs.iter().all(|&q|powmod(g,(p-1)/q,p)!=1){return g;}}0}
fn v2(mut x:u64)->u32{let mut v=0;while x%2==0{x/=2;v+=1;}v}
fn bessel_i0(z:f64)->f64{ if z<30.0{let mut t=1.0f64;let mut s=1.0f64;let h2=(z*0.5)*(z*0.5);for k in 1..400{t*=h2/((k as f64)*(k as f64));s+=t;if t<s*1e-18{break;}}s}else{let c=1.0+1.0/(8.0*z)+9.0/(128.0*z*z)+225.0/(3072.0*z*z*z);z.exp()/(2.0*std::f64::consts::PI*z).sqrt()*c}}
fn log_i0(z:f64)->f64{ if z<30.0{bessel_i0(z).ln()}else{let c=1.0+1.0/(8.0*z)+9.0/(128.0*z*z)+225.0/(3072.0*z*z*z);z-0.5*(2.0*std::f64::consts::PI*z).ln()+c.ln()}}
fn coset_periods(n:u64,p:u64)->Vec<f64>{
    let g=proot(p); let m=(p-1)/n; let h=powmod(g,(p-1)/n,p);
    let mu:Vec<u64>=(0..n).map(|i|powmod(h,i,p)).collect();
    let tau=2.0*std::f64::consts::PI/(p as f64);
    (0..m).into_par_iter().map(|j|{let b=powmod(g,j,p);let mut re=0.0f64;let mut im=0.0f64;
        for &x in &mu{let bx=mulmod(b,x,p) as f64;let a=tau*bx;re+=a.cos();im+=a.sin();}re*re+im*im}).collect()
}
#[inline] fn logcosh(x:f64)->f64{ if x>20.0 {x-std::f64::consts::LN_2} else {x.cosh().ln()} }
// log Psi(y) = log( n * sum_j cosh(|eta_j| y) )   [b!=0 only, m cosets x n]
fn log_psi(v:&[f64], y:f64, n:f64)->f64{
    let logs:Vec<f64>=v.iter().map(|&x2|logcosh(x2.sqrt()*y)).collect();
    let lmax=logs.iter().cloned().fold(f64::NEG_INFINITY,f64::max);
    n.ln()+lmax+logs.iter().map(|&l|(l-lmax).exp()).sum::<f64>().ln()
}
// log P0(y) = log( q I0(2y)^{n/2} - cosh(n y) ); returns (log|P0|, sign)
fn log_p0(y:f64,n:f64,lq:f64)->(f64,f64){
    let a=lq+(n/2.0)*log_i0(2.0*y);          // log(q I0^{n/2})
    let b=logcosh(n*y);                        // log cosh(n y)
    if a>b { let r=(b-a).exp(); (a+(1.0-r).ln(),1.0) }
    else   { let r=(a-b).exp(); (b+(1.0-r).ln(),-1.0) }
}
fn main(){
    let args:Vec<String>=std::env::args().collect();
    let n:u64=args.get(1).and_then(|s|s.parse().ok()).unwrap_or(16);
    let num:usize=args.get(2).and_then(|s|s.parse().ok()).unwrap_or(6);
    let beta:u32=args.get(3).and_then(|s|s.parse().ok()).unwrap_or(4);
    let mut p=n.pow(beta); p+=(n+1-p%n)%n; let nf=n as f64;
    println!("# n={} beta-target={} base=n^{}={}",n,beta,beta,n.pow(beta));
    println!("# DC-subtracted prize MGF Psi=Sum_{{b!=0}}cosh.  P0=char-0 pred = qI0^(n/2)-cosh(ny).  W=Psi-P0.");
    println!("# y_opt = argmin arccosh(Psi)/y (the Chernoff saddle).  budget=q^2.  slack=q^2-P0.");
    println!("# {:>13} {:>3} {:>5} {:>7} {:>7} {:>8} {:>8} {:>8} {:>9} {:>9} {:>9}",
             "p","v2","beta","yopt","Mc/flr","Psi_q","P0_q","W_q","Psi/q2","W/q2","W/slack");
    let mut found=0;
    while found<num{
        if p%n==1 && isprime(p){
            let lq=(p as f64).ln(); let beff=lq/nf.ln();
            let floor=(2.0*nf*lq).sqrt();
            let v=coset_periods(n,p);
            // find optimal y minimizing arccosh(Psi)/y ~ (ln2+logPsi)/y
            let mut besty=0.0; let mut bestmc=f64::INFINITY;
            let mut yy=0.3;
            while yy<=3.0 {
                let lp=log_psi(&v,yy,nf);
                let mc=(std::f64::consts::LN_2+lp)/yy;
                if mc<bestmc {bestmc=mc;besty=yy;}
                yy+=0.02;
            }
            let yopt=besty;
            let lp=log_psi(&v,yopt,nf);
            let (lp0,sgn0)=log_p0(yopt,nf,lq);
            // W = Psi - P0
            let (lw, sw);
            // Psi>0; P0 sign=sgn0. If sgn0>0: W=Psi-P0. If sgn0<0: P0<0 so W=Psi+|P0| > Psi.
            if sgn0>0.0 {
                if lp>lp0 { let r=(lp0-lp).exp(); lw=lp+(1.0-r).ln(); sw=1.0; }
                else { let r=(lp-lp0).exp(); lw=lp0+(1.0-r).ln(); sw=-1.0; }
            } else {
                // W = Psi + |P0|  (both positive contributions)
                let m=lp.max(lp0); lw=m+((lp-m).exp()+(lp0-m).exp()).ln(); sw=1.0;
            }
            let log2q=2.0*lq;
            // slack = q^2 - P0.  if P0<0, slack > q^2.
            let (lslk, sslk);
            if sgn0>0.0 {
                if log2q>lp0 { let r=(lp0-log2q).exp(); lslk=log2q+(1.0-r).ln(); sslk=1.0; }
                else { lslk=f64::NAN; sslk=-1.0; }
            } else { let m=log2q.max(lp0); lslk=m+((log2q-m).exp()+(lp0-m).exp()).ln(); sslk=1.0; }
            let psi_over_q2=(lp-log2q).exp();
            let w_over_q2=sw*(lw-log2q).exp();
            let w_over_slk= if sslk>0.0 { sw*(lw-lslk).exp() } else { f64::NAN };
            println!("{:>15} {:>3} {:>5.2} {:>7.3} {:>7.4} {:>8.4} {:>8.4} {:>8.4} {:>9.2e} {:>9.2e} {:>9.2e}",
                p, v2(p-1), beff, yopt, bestmc/floor,
                lp/lq, sgn0*lp0/lq, sw*lw/lq, psi_over_q2, w_over_q2, w_over_slk);
            found+=1;
        }
        p+=n;
    }
}
