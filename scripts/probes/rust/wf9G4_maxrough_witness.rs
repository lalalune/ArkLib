// wf-G4: GROWING-WITNESS test of the roughness-driver thesis.
// For each n, find the MAXIMALLY-ROUGH prize prime: p = m*n+1 prime with m itself PRIME (P^+(m)=m,
// smoothness index 1.0 -- the worst case under the G4 thesis), AND beta = log_n p ~ 4 if reachable,
// else as thin as the m-cap allows. Track C = M/sqrt(n log m). If the G4 thesis is right, the
// maximally-rough C should GROW with n (a disproof witness). If it stays bounded, roughness is NOT
// the driver and the prize bound survives the rough family.
// Also report the maximally-SMOOTH counterpart (m a power of 2 -> Fermat-like / quiet) for contrast.
// build: rustc -O wf9G4_maxrough_witness.rs -o /tmp/g4mw
use std::f64::consts::PI;
fn mpow(_a:u64,mut e:u64,p:u64)->u64{let mut r=1u128;let mut a2=_a as u128;let pp=p as u128;while e>0{if e&1==1{r=r*a2%pp;}a2=a2*a2%pp;e>>=1;}r as u64}
fn is_prime(n:u64)->bool{if n<2{return false;}if n%2==0{return n==2;}let mut d=3;while (d as u128)*(d as u128)<=n as u128{if n%d==0{return false;}d+=2;}true}
fn primitive_root(p:u64)->u64{let mut m=p-1;let mut fs=vec![];let mut d=2;while (d as u128)*(d as u128)<=m as u128{if m%d==0{fs.push(d);while m%d==0{m/=d;}}d+=1;}if m>1{fs.push(m);}let mut g=2;loop{if fs.iter().all(|&f|mpow(g,(p-1)/f,p)!=1){return g;}g+=1;}}
fn measure(n:u64,p:u64)->f64{let g=primitive_root(p);let h=mpow(g,(p-1)/n,p);let mu:Vec<u64>=(0..n).map(|j|mpow(h,j,p)).collect();let m=(p-1)/n;let mut best=0.0f64;let mut b=1u64;let gn=mpow(g,n,p);for _ in 0..m{let mut re=0.0;let mut im=0.0;for &x in &mu{let t=((b as u128*x as u128)%p as u128)as u64;let ang=2.0*PI*(t as f64)/(p as f64);re+=ang.cos();im+=ang.sin();}let mag:f64=(re*re+im*im).sqrt();if mag>best{best=mag;}b=((b as u128*gn as u128)%p as u128)as u64;}best}
fn main(){
    let ns:Vec<u64>=vec![16,32,64,128,256,512];
    let mcap:u64=4_000_000; // measure cost ~ m*n; cap m
    eprintln!("# n   ROUGH: p  m(=prime?)  beta   C       |  SMOOTH(m=2^k): p  m   beta   C");
    for &n in &ns {
        // maximally rough: smallest m>=n that is PRIME with m*n+1 prime, m as large as cap allows but pick the LARGEST rough m under cap for max beta
        let mut best_rough:(u64,u64,f64)=(0,0,0.0); // p,m,C
        let mut m = mcap; // scan downward to get largest rough m (=> largest beta) feasible
        let mut tries=0;
        while m>=n && tries<200000 {
            if is_prime(m) { let p=m*n+1; if is_prime(p){ let c=measure(n,p)/(((n as f64)*((m as f64).ln())).sqrt()); best_rough=(p,m,c); break; } }
            m-=1; tries+=1;
        }
        // maximally smooth: m = 2^k, largest 2^k<=mcap with m*n+1 prime
        let mut best_smooth:(u64,u64,f64)=(0,0,0.0);
        let mut k=(mcap as f64).log2() as u32;
        while k>=1 { let mm=1u64<<k; if mm>=n && mm<=mcap { let p=mm*n+1; if is_prime(p){ let c=measure(n,p)/(((n as f64)*((mm as f64).ln())).sqrt()); best_smooth=(p,mm,c); break; } } if k==0{break;} k-=1; }
        let br=(best_rough.0 as f64).ln()/(n as f64).ln();
        let bs=(best_smooth.0 as f64).ln()/(n as f64).ln();
        eprintln!("{:5}  {:>12} {:>9}P b={:.2} C={:.4}  |  {:>12} {:>9} b={:.2} C={:.4}",
            n, best_rough.0, best_rough.1, br, best_rough.2, best_smooth.0, best_smooth.1, bs, best_smooth.2);
    }
}
