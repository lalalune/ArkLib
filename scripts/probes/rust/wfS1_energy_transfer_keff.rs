// S1 DECISIVE: does the char-p NONPRINCIPAL energy transfer hold with bounded K?
// K_eff(r) = (E_r'/[(2r-1)!! n^r])^{1/r},  E_r' = (1/p) sum_{b!=0} eta_b^{2r}.
// If K_eff bounded (abs const) across r,n at STRUCTURED primes => transfer holds with slack => prize via L3 (C=sqrt K).
// If K_eff grows with n or r at structured primes => transfer FALSE (prize needs concentration, not energy).
use std::f64::consts::PI;
fn mpow(mut a:u64,mut e:u64,p:u64)->u64{let mut r=1u128;let mut a2=a as u128;let pp=p as u128;while e>0{if e&1==1{r=r*a2%pp;}a2=a2*a2%pp;e>>=1;}r as u64}
fn isp(n:u64)->bool{if n<2{return false}let mut d=2;while (d as u128)*(d as u128)<=n as u128{if n%d==0{return false}d+=1}true}
fn fp(n:u64,lo:u64)->u64{let mut p=lo+((1+n-lo%n)%n);if p<=2{p+=n}loop{if p>2&&p%n==1&&isp(p){return p}p+=n}}
fn proot(p:u64)->u64{let mut m=p-1;let mut fs=vec![];let mut d=2;while d*d<=m{if m%d==0{fs.push(d);while m%d==0{m/=d}}d+=1}if m>1{fs.push(m)}let mut g=2;loop{if fs.iter().all(|&f|mpow(g,(p-1)/f,p)!=1){return g}g+=1}}
fn v2(mut x:u64)->u32{let mut v=0;while x&1==0{v+=1;x>>=1}v}
fn largest_pf(mut x:u64)->u64{let mut L=1;let mut d=2;while d*d<=x{while x%d==0{L=d;x/=d}d+=1}if x>1{L=x}L}
fn dfact(r:usize)->f64{let mut v=1.0;for j in 1..=r{v*=(2*j-1)as f64}v}
fn run(n:u64,p:u64,tag:&str){
    let g=proot(p);let h=mpow(g,(p-1)/n,p);
    let mu:Vec<u64>=(0..n).map(|j|mpow(h,j,p)).collect();
    let m=(p-1)/n;let gn=mpow(g,n,p);
    let mut eta=Vec::with_capacity(m as usize);let mut b=1u64;
    for _ in 0..m{let mut re=0.0;for &x in &mu{let t=((b as u128*x as u128)%p as u128)as u64;re+=(2.0*PI*(t as f64)/p as f64).cos();}eta.push(re);b=((b as u128*gn as u128)%p as u128)as u64;}
    let lnq=(p as f64).ln(); let rmax=(1.4*lnq) as usize;
    print!("{} n={:4} p={:>11} v2={:2} lpf((p-1)/n)={:>9} lnq={:.0} beta={:.2} | K_eff(r): ",tag,n,p,v2(p-1),largest_pf((p-1)/n),lnq,lnq/(n as f64).ln());
    let mut maxk=0.0f64;
    for r in [1usize,2,3,5,8,12,16,20,25].iter().filter(|&&r|r<=rmax.max(6)) {
        let r=*r; let mut s=0.0; for &e in &eta{s+=e.powi(2*r as i32);}
        let er=s/(p as f64); let ratio=er/(dfact(r)*(n as f64).powi(r as i32));
        let k=ratio.powf(1.0/r as f64);
        if k>maxk{maxk=k;}
        print!("r{}={:.2} ",r,k);
    }
    println!("| MAX K_eff={:.3}", maxk);
}
fn main(){
    // beta~4, n=32: good vs structured (high-v2, rough) primes
    println!("== n=32, beta~4 ==");
    run(32, fp(32,1000003), "good ");
    // high-v2: p=1 mod 2^k large
    let mut p=fp(32, 1000003); for _ in 0..2000 { let q=fp(32,p+1); if v2(q-1)>=10 {run(32,q,"hi-v2"); break;} p=q; }
    // rough: (p-1)/32 has large prime factor
    let mut p=fp(32, 1000003); for _ in 0..3000 { let q=fp(32,p+1); if largest_pf((q-1)/32) > (q-1)/32/4 {run(32,q,"rough"); break;} p=q; }
    println!("== n=64, beta~4 ==");
    run(64, fp(64,16000003), "good ");
    let mut p=fp(64, 16000003); for _ in 0..3000 { let q=fp(64,p+1); if v2(q-1)>=12 {run(64,q,"hi-v2"); break;} p=q; }
}
