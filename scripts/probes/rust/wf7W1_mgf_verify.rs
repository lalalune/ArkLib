// HARD-CHECK W1: Phi_nz(y) = (1/q) sum_{b!=0} cosh(eta_b y) <= exp(n y^2/2)?  vs the FULL sum (incl b=0).
use std::f64::consts::PI;
fn mpow(mut a:u64,mut e:u64,p:u64)->u64{let mut r=1u128;let mut a2=a as u128;let pp=p as u128;while e>0{if e&1==1{r=r*a2%pp;}a2=a2*a2%pp;e>>=1;}r as u64}
fn isp(n:u64)->bool{if n<2{return false}let mut d=2;while d*d<=n{if n%d==0{return false}d+=1}true}
fn fp(n:u64,lo:u64)->u64{let mut p=lo+((1+n-lo%n)%n);if p<=2{p+=n}loop{if p>2&&p%n==1&&isp(p){return p}p+=n}}
fn proot(p:u64)->u64{let mut m=p-1;let mut fs=vec![];let mut d=2;while d*d<=m{if m%d==0{fs.push(d);while m%d==0{m/=d}}d+=1}if m>1{fs.push(m)}let mut g=2;loop{if fs.iter().all(|&f|mpow(g,(p-1)/f,p)!=1){return g}g+=1}}
fn run(n:u64,p:u64){
    let g=proot(p);let h=mpow(g,(p-1)/n,p);
    let mu:Vec<u64>=(0..n).map(|j|mpow(h,j,p)).collect();
    let m=(p-1)/n;let gn=mpow(g,n,p);
    let mut eta=Vec::with_capacity(m as usize);let mut b=1u64;
    for _ in 0..m{let mut re=0.0;for &x in &mu{let t=((b as u128*x as u128)%p as u128)as u64;re+=(2.0*PI*(t as f64)/p as f64).cos();}eta.push(re);b=((b as u128*gn as u128)%p as u128)as u64;}
    let q=p as f64; let nn=n as f64;
    let ystar=(2.0*q.ln()/nn).sqrt();
    let mut worst_nz=0.0f64; let mut worst_full=0.0f64; let mut at=0.0;
    let steps=400; let ymax=ystar*1.3;
    for i in 1..=steps {
        let y=ymax*(i as f64)/(steps as f64);
        let bound=(nn*y*y/2.0).exp();
        let mut snz=0.0; for &e in &eta { snz += (e*y).cosh(); }
        snz/=q;
        let full = snz + (nn*y).cosh()/q; // add principal b=0, eta_0=n
        let rnz=snz/bound; let rfull=full/bound;
        if rnz>worst_nz{worst_nz=rnz; at=y;}
        if rfull>worst_full{worst_full=rfull;}
    }
    println!("n={:4} p={:>10} y*={:.3} | max Phi_nz/exp(ny^2/2) = {:.4} (at y={:.2}) [<=1 => W1 holds] | full-sum ratio = {:.3e} [blows up]",
        n,p,ystar, worst_nz, at, worst_full);
}
fn main(){ run(16,fp(16,60000)); run(32,fp(32,1000000)); run(64,fp(64,16000000)); run(128,fp(128,260000000)); }
