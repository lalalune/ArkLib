// HARD-VERIFY D5-3 (#bad cosets O(1)?) and D8-3 (GUE level repulsion?) at growing m.
use std::f64::consts::PI;
fn mpow(mut a:u64,mut e:u64,p:u64)->u64{let mut r=1u128;let mut a2=a as u128;let pp=p as u128;while e>0{if e&1==1{r=r*a2%pp;}a2=a2*a2%pp;e>>=1;}r as u64}
fn isp(n:u64)->bool{if n<2{return false}let mut d=2;while d*d<=n{if n%d==0{return false}d+=1}true}
fn fp(n:u64,lo:u64)->u64{let mut p=lo+((1+n-lo%n)%n);if p<=2{p+=n}loop{if p>2&&p%n==1&&isp(p){return p}p+=n}}
fn proot(p:u64)->u64{let mut m=p-1;let mut fs=vec![];let mut d=2;while d*d<=m{if m%d==0{fs.push(d);while m%d==0{m/=d}}d+=1}if m>1{fs.push(m)}let mut g=2;loop{if fs.iter().all(|&f|mpow(g,(p-1)/f,p)!=1){return g}g+=1}}
fn run(n:u64,p:u64){
    let g=proot(p); let h=mpow(g,(p-1)/n,p);
    let mu:Vec<u64>=(0..n).map(|j|mpow(h,j,p)).collect();
    let m=(p-1)/n;
    let gn=mpow(g,n,p); // generates quotient of order m
    let mut mags=Vec::with_capacity(m as usize);
    let mut b=1u64;
    for _ in 0..m {
        let mut re=0.0;let mut im=0.0;
        for &x in &mu{let t=((b as u128*x as u128)%p as u128)as u64;let a=2.0*PI*(t as f64)/p as f64;re+=a.cos();im+=a.sin();}
        mags.push((re*re+im*im).sqrt());
        b=((b as u128*gn as u128)%p as u128)as u64;
    }
    let mx=mags.iter().cloned().fold(0.0,f64::max);
    let n90=mags.iter().filter(|&&v|v>=0.9*mx).count();
    let n95=mags.iter().filter(|&&v|v>=0.95*mx).count();
    let n80=mags.iter().filter(|&&v|v>=0.8*mx).count();
    // white-noise prediction for #>=0.9 max: m^0.19
    let pred=(m as f64).powf(0.19);
    // spacing ratio <r> of sorted mags (consecutive gaps)
    let mut s=mags.clone(); s.sort_by(|a,b|a.partial_cmp(b).unwrap());
    let gaps:Vec<f64>=s.windows(2).map(|w|w[1]-w[0]).collect();
    let mut rs=0.0;let mut cnt=0;
    for i in 1..gaps.len(){let a=gaps[i-1];let b=gaps[i];if a>1e-12&&b>1e-12{rs+=a.min(b)/a.max(b);cnt+=1;}}
    let rmean=rs/cnt as f64;
    let beta=(p as f64).ln()/(n as f64).ln();
    println!("n={:4} p={:>11} m={:>9} beta={:.2} | M/sqrt(n log)={:.3} | #>=.9M={:3} (m^0.19={:.1}) #>=.95M={:2} #>=.8M={:3} | <r>={:.3} (GUE .603 Poisson .386)",
        n,p,m,beta, mx/(((n as f64)*((p as f64/n as f64).ln())).sqrt()), n90, pred, n95, n80, rmean);
}
fn main(){
    // D5-3: fix n=64, sweep m over orders of magnitude (vary p)
    println!("== D5-3 test: #bad cosets vs m (white-noise predicts ~m^0.19, NOT O(1)) ==");
    for lo in [5000u64, 50000, 500000, 5000000, 50000000, 300000000] {
        let p=fp(64,lo); run(64,p);
    }
    println!("== D8-3 test: spacing ratio <r> at larger n ==");
    for &(n,lo) in &[(128u64,3000000u64),(256,50000000)] { let p=fp(n,lo); run(n,p); }
}
