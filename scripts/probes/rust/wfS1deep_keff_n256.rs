use std::f64::consts::PI;
fn mpow(mut a:u64,mut e:u64,p:u64)->u64{let mut r=1u128;let mut a2=a as u128;let pp=p as u128;while e>0{if e&1==1{r=r*a2%pp;}a2=a2*a2%pp;e>>=1;}r as u64}
fn isp(n:u64)->bool{if n<2{return false}let mut d=2;while (d as u128)*(d as u128)<=n as u128{if n%d==0{return false}d+=1}true}
fn fp(n:u64,lo:u64)->u64{let mut p=lo+((1+n-lo%n)%n);if p<=2{p+=n}loop{if p>2&&p%n==1&&isp(p){return p}p+=n}}
fn proot(p:u64)->u64{let mut m=p-1;let mut fs=vec![];let mut d=2;while d*d<=m{if m%d==0{fs.push(d);while m%d==0{m/=d}}d+=1}if m>1{fs.push(m)}let mut g=2;loop{if fs.iter().all(|&f|mpow(g,(p-1)/f,p)!=1){return g}g+=1}}
fn v2(mut x:u64)->u32{let mut v=0;while x&1==0{v+=1;x>>=1}v}
fn lpf(mut x:u64)->u64{let mut l=1;let mut d=2;while d*d<=x{while x%d==0{l=d;x/=d}d+=1}if x>1{l=x}l}
fn dfact(r:usize)->f64{let mut v=1.0;for j in 1..=r{v*=(2*j-1)as f64}v}
fn run(n:u64,p:u64,tag:&str){
    let g=proot(p);let h=mpow(g,(p-1)/n,p);
    let mu:Vec<u64>=(0..n).map(|j|mpow(h,j,p)).collect();
    let m=(p-1)/n;let gn=mpow(g,n,p);
    let mut eta=Vec::with_capacity(m as usize);let mut b=1u64;
    for _ in 0..m{let mut re=0.0;for &x in &mu{let t=((b as u128*x as u128)%p as u128)as u64;re+=(2.0*PI*(t as f64)/p as f64).cos();}eta.push(re);b=((b as u128*gn as u128)%p as u128)as u64;}
    let mut maxk=0.0f64;
    print!("{} n={:4} p={:>11} v2={:2} lpf={:>8} beta={:.2} | Keff_Wick(r): ",tag,n,p,v2(p-1),lpf((p-1)/n),(p as f64).ln()/(n as f64).ln());
    for r in [2usize,3,5,8,12,16,20,24,28].iter() {let r=*r; let mut s=0.0; for &e in &eta{s+=e.powi(2*r as i32);} let er=s/(p as f64); let k=(er/(dfact(r)*(n as f64).powi(r as i32))).powf(1.0/r as f64); if k>maxk{maxk=k} print!("r{}={:.2} ",r,k);}
    println!("| MAXK={:.3}",maxk);
}
fn main(){
    println!("== n=128, beta=4 ==");
    run(128, fp(128,260000003),"good ");
    let mut p=fp(128,260000003); for _ in 0..4000 { let q=fp(128,p+1); if v2(q-1)>=14 {run(128,q,"hi-v2"); break;} p=q; }
    let mut p=fp(128,260000003); for _ in 0..5000 { let q=fp(128,p+1); if lpf((q-1)/128) > (q-1)/128/3 {run(128,q,"rough"); break;} p=q; }
    println!("== n=256, beta=4 ==");
    run(256, fp(256,4294967296),"good ");
    let mut p=fp(256,4294967296); for _ in 0..6000 { let q=fp(256,p+1); if v2(q-1)>=16 {run(256,q,"hi-v2"); break;} p=q; }
}
