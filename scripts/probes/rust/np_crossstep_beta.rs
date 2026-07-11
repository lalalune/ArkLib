// Beta-threshold for NONPRINCIPAL cross-step closure. Use f64 energy (avoid u128 overflow at deep r);
// energy accumulated as f64 from exact u128 freq counts (counts stay < 2^53 until deep, flag if not).
// Question: at what beta does max_r cross'_r/slack drop <=1 ? And does E'_r/char0 stay <1 there?
fn mpow(a:u64,mut e:u64,p:u64)->u64{let mut r=1u128;let mut a2=a as u128;let pp=p as u128;while e>0{if e&1==1{r=r*a2%pp;}a2=a2*a2%pp;e>>=1;}r as u64}
fn isp(n:u64)->bool{if n<2{return false}let mut d=2;while d*d<=n{if n%d==0{return false}d+=1}true}
fn fp(n:u64,lo:u64)->u64{let mut p=lo+((1+n-lo%n)%n);if p<=2{p+=n}loop{if p>2&&p%n==1&&isp(p){return p}p+=n}}
fn proot(p:u64)->u64{let mut m=p-1;let mut fs=vec![];let mut d=2;while d*d<=m{if m%d==0{fs.push(d);while m%d==0{m/=d}}d+=1}if m>1{fs.push(m)}let mut g=2;loop{if fs.iter().all(|&f|mpow(g,(p-1)/f,p)!=1){return g}g+=1}}
fn dfact(r:i64)->f64{if r<=0{return 1.0}let mut v=1.0;let mut k=r;while k>0{v*=k as f64;k-=2;}v}
fn run(n:u64,p:u64,rmax:usize)->(f64,f64,f64){
    let g=proot(p); let h=mpow(g,(p-1)/n,p);
    let mu:Vec<u64>=(0..n).map(|j|mpow(h,j,p)).collect();
    let pp=p as usize;
    let mut freq=vec![0u128; pp];
    for &x in &mu { freq[x as usize]+=1; }
    let mut energies: Vec<f64>=Vec::new();
    let mut e1=0.0; for &f in &freq { e1+=(f as f64)*(f as f64); } energies.push(e1);
    let mut level=1usize;
    while level<rmax+1 {
        let mut nf=vec![0u128;pp];
        for d in 0..pp { let fd=freq[d]; if fd==0 {continue;} for &s in &mu { let idx=((d as u64 + s)%p) as usize; nf[idx]+=fd; } }
        freq=nf; level+=1;
        let mut e=0.0; for &f in &freq { e+=(f as f64)*(f as f64); } energies.push(e);
    }
    let nf=n as f64;
    let mut maxcp=0.0f64; let mut maxenp=0.0f64; let mut maxk=0.0f64;
    for r in 1..=rmax {
        let er=energies[r-1]; let er1=energies[r];
        let cross = er1 - nf*er;
        let pr_r = nf.powi(2*r as i32)/(p as f64);
        let pr_r1= nf.powi(2*(r as i32+1))/(p as f64);
        let er_p = er - pr_r;
        let cross_p = cross - (pr_r1 - nf*pr_r);
        let slack = 2.0*(r as f64)*dfact(2*r as i64 -1)*nf.powi(r as i32 +1);
        let char0 = dfact(2*r as i64 -1)*nf.powi(r as i32);
        let cp=cross_p/slack; let enp=er_p/char0; let k=enp.powf(1.0/r as f64);
        if cp>maxcp{maxcp=cp;} if enp>maxenp{maxenp=enp;} if k>maxk{maxk=k;}
    }
    (maxcp,maxenp,maxk)
}
fn main(){
    println!("  n  beta    p          max(cross'/slack)  max(E'/char0)  max K'   closure?");
    for &n in &[16u64,32,64] {
        for &(lo,_lbl) in &[(2000u64,""),(50000,""),(2_000_000u64,""),(40_000_000u64,"")] {
            let p=fp(n,lo);
            let rmax=((p as f64).ln()*1.2) as usize; let rmax=rmax.min(13).max(6);
            let (mc,me,mk)=run(n,p,rmax);
            let beta=(p as f64).ln()/(n as f64).ln();
            println!("  {:3} {:5.2}  {:11}  {:14.4}   {:11.4}  {:7.4}  {}",
                n,beta,p,mc,me,mk, if mc<=1.0 {"CLEAN"} else {"break"});
        }
    }
}
