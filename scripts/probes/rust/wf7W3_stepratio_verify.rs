// HARD-CHECK W3: R(r)=M(r+1)/((2r+1)*s*M(r)), s=n. Prize <= [R(1)<=1 AND R antitone].
// M(r)=(1/m) sum_{b!=0} eta_b^{2r}. Test at n=16,32,64,128, band depth, prize p.
use std::f64::consts::PI;
fn mpow(mut a:u64,mut e:u64,p:u64)->u64{let mut r=1u128;let mut a2=a as u128;let pp=p as u128;while e>0{if e&1==1{r=r*a2%pp;}a2=a2*a2%pp;e>>=1;}r as u64}
fn isp(n:u64)->bool{if n<2{return false}let mut d=2;while d*d<=n{if n%d==0{return false}d+=1}true}
fn fp(n:u64,lo:u64)->u64{let mut p=lo+((1+n-lo%n)%n);if p<=2{p+=n}loop{if p>2&&p%n==1&&isp(p){return p}p+=n}}
fn proot(p:u64)->u64{let mut m=p-1;let mut fs=vec![];let mut d=2;while d*d<=m{if m%d==0{fs.push(d);while m%d==0{m/=d}}d+=1}if m>1{fs.push(m)}let mut g=2;loop{if fs.iter().all(|&f|mpow(g,(p-1)/f,p)!=1){return g}g+=1}}
fn run(n:u64,p:u64,rmax:usize){
    let g=proot(p);let h=mpow(g,(p-1)/n,p);
    let mu:Vec<u64>=(0..n).map(|j|mpow(h,j,p)).collect();
    let m=(p-1)/n;let gn=mpow(g,n,p);
    let mut eta=Vec::with_capacity(m as usize);let mut b=1u64;
    for _ in 0..m{let mut re=0.0;for &x in &mu{let t=((b as u128*x as u128)%p as u128)as u64;re+=(2.0*PI*(t as f64)/p as f64).cos();}eta.push(re);b=((b as u128*gn as u128)%p as u128)as u64;}
    let mom=|r:usize|->f64{ let mut s=0.0; for &e in &eta{s+=e.powi(2*r as i32);} s/(m as f64) };
    let s=n as f64;
    let mut rs=vec![0.0;rmax+2];
    for r in 1..=rmax+1 { rs[r]= mom(r+1)/((2*r+1) as f64 * s * mom(r)); }
    let r1ok = rs[1]<=1.0+1e-9;
    let mut anti=true; let mut worst=0.0f64;
    for r in 1..rmax { let inc=rs[r+1]-rs[r]; if inc>worst{worst=inc;} if inc>1e-6 {anti=false;} }
    print!("n={:4} p={:>10} lnq={:.1} | R(1)={:.4} {} | antitone={} worstInc={:+.4} | R: ",
        n,p,(p as f64).ln(), rs[1], if r1ok{"<=1 OK"}else{">1 FAIL"}, anti, worst);
    for r in 1..=rmax.min(8){print!("{:.3} ",rs[r]);} println!();
}
fn main(){
    run(16, fp(16,60000), 12);
    run(32, fp(32,1000000), 12);
    run(64, fp(64,16000000), 12);
    run(128, fp(128,260000000), 12);
}
