// HARD-VERIFY B3/B4 witnesses: R(r) antitone? + MGF ratio? at SPECIFIC primes (rough/spur vs good).
use std::f64::consts::PI;
fn mpow(mut a:u64,mut e:u64,p:u64)->u64{let mut r=1u128;let mut a2=a as u128;let pp=p as u128;while e>0{if e&1==1{r=r*a2%pp;}a2=a2*a2%pp;e>>=1;}r as u64}
fn isp(n:u64)->bool{if n<2{return false}let mut d=2;while (d as u128)*(d as u128)<=n as u128{if n%d==0{return false}d+=1}true}
fn proot(p:u64)->u64{let mut m=p-1;let mut fs=vec![];let mut d=2;while d*d<=m{if m%d==0{fs.push(d);while m%d==0{m/=d}}d+=1}if m>1{fs.push(m)}let mut g=2;loop{if fs.iter().all(|&f|mpow(g,(p-1)/f,p)!=1){return g}g+=1}}
fn run(n:u64,p:u64,label:&str){
    if !isp(p){println!("{}: p={} NOT PRIME",label,p);return;}
    if (p-1)%n!=0{println!("{}: n!|p-1",label);return;}
    let g=proot(p);let h=mpow(g,(p-1)/n,p);
    let mu:Vec<u64>=(0..n).map(|j|mpow(h,j,p)).collect();
    let m=(p-1)/n;let gn=mpow(g,n,p);
    let mut eta=Vec::with_capacity(m as usize);let mut b=1u64;
    for _ in 0..m{let mut re=0.0;for &x in &mu{let t=((b as u128*x as u128)%p as u128)as u64;re+=(2.0*PI*(t as f64)/p as f64).cos();}eta.push(re);b=((b as u128*gn as u128)%p as u128)as u64;}
    let mom=|r:usize|->f64{let mut s=0.0;for &e in &eta{s+=e.powi(2*r as i32);}s/(m as f64)};
    let s=n as f64;
    // R(r)
    let rmax=8usize; let mut rs=vec![0.0;rmax+2];
    for r in 1..=rmax+1{rs[r]=mom(r+1)/((2*r+1)as f64*s*mom(r));}
    let mut anti=true; let mut at=0;
    for r in 1..=rmax{if rs[r+1]>rs[r]+1e-7{anti=false; at=r; break;}}
    // m_1 = M_2-style: kurtosis cap m_1 = M(1)/( (1)*n )? Use W3-base ratio a_2/W_2 ~ m_1 = M_2_moment/Wick_1... report R(1) and the 4th/2nd
    // MGF ratio
    let q=p as f64; let ystar=(2.0*q.ln()/s).sqrt();
    let mut worst=0.0f64; let steps=300; let ymax=ystar*1.25;
    for i in 1..=steps{let y=ymax*(i as f64)/steps as f64; let bound=(s*y*y/2.0).exp(); let mut sn=0.0; for &e in &eta{sn+=(e*y).cosh();} let r=(sn/q)/bound; if r>worst{worst=r;}}
    print!("{}: n={} p={} | R: ",label,n,p); for r in 1..=6{print!("{:.4} ",rs[r]);}
    println!("| antitone={}{} | maxMGF/exp={:.4} {}", anti, if !anti{format!(" (FAILS at r={}: R{}={:.4}<R{}={:.4})",at,at,rs[at],at+1,rs[at+1])}else{String::new()}, worst, if worst>1.0001{"BREAKS"}else{"holds"});
}
fn main(){
    run(32,1001153,"B3-witness(rough)");
    run(32,32993,"B4-witness(spur)");
    run(32,1000033,"good-prime(my earlier)");
    run(32,65537,"Fermat-spur");
}
