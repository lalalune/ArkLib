// EXACT integer E_r(mu_n) for r=1,2,3 via mod-p convolution, crossA_r, K=1 check, at prize scale.
fn mpow(a:u64,mut e:u64,p:u64)->u64{let mut r=1u128;let mut a2=a as u128;let pp=p as u128;while e>0{if e&1==1{r=r*a2%pp;}a2=a2*a2%pp;e>>=1;}r as u64}
fn isp(n:u64)->bool{if n<2{return false}if n%2==0{return n==2}let mut d=3;while d*d<=n{if n%d==0{return false}d+=2}true}
fn primes(n:u64,lo:u64,k:usize)->Vec<u64>{let mut o=vec![];let mut p=lo+((1+n-lo%n)%n);if p<=2{p+=n}loop{if p>2&&p%n==1&&isp(p){o.push(p);if o.len()>=k{break}}p+=n}o}
fn proot(p:u64)->u64{let mut m=p-1;let mut fs=vec![];let mut d=2;while d*d<=m{if m%d==0{fs.push(d);while m%d==0{m/=d}}d+=1}if m>1{fs.push(m)}let mut g=2;loop{if fs.iter().all(|&f|mpow(g,(p-1)/f,p)!=1){return g}g+=1}}
// E_r = sum_s (#r-tuples summing to s)^2 = sum_s freq_r[s]^2, freq_r = r-fold convolution of indicator(mu_n).
// Use HashMap freq for r up to 3 (sizes up to n^r entries but distinct sums <= p; HashMap fine for n<=128).
use std::collections::HashMap;
fn energies(hgen:u64,sz:u64,p:u64,rmax:usize)->Vec<u128>{
    let mu:Vec<u64>=(0..sz).map(|j|mpow(hgen,j,p)).collect();
    let mut freq:HashMap<u64,u128>=HashMap::new(); freq.insert(0,1); // r=0 partial: empty sum
    let mut out=vec![];
    let mut cur:HashMap<u64,u128>=HashMap::new(); for &x in &mu{*cur.entry(x).or_insert(0)+=1;} // r=1 freq
    for r in 1..=rmax{
        let mut e=0u128; for(_,&c) in &cur{e+=c*c;} out.push(e);
        if r<rmax{ let mut nf:HashMap<u64,u128>=HashMap::new(); for(&s,&c) in &cur{for &x in &mu{*nf.entry((s+x)%p).or_insert(0)+=c;}} cur=nf; }
    }
    let _=freq;
    out
}
fn dfac(r:u64)->u128{let mut v=1u128; for k in 1..=r{v*=2*k as u128-1;} v}
fn main(){
    let beta=4.0;
    println!("# EXACT integer crossA_r at prize scale. Kcross=(crossA_r/denom)^(1/r). K=1 holds iff <=1.");
    for &n in &[8u64,16,32,64,128]{
        let lo=(n as f64).powf(beta) as u64;
        for &p in &primes(n,lo,2){
            let g=proot(p); let h=mpow(g,(p-1)/n,p); let h2=mpow(h,2,p);
            let en=energies(h,n,p,3); let eh=energies(h2,n/2,p,3);
            print!("n={:4} p={:11} | ",n,p);
            for r in 2..=3{
                let ar = en[r-1] as f64 - (n as f64).powi(2*r as i32)/p as f64;
                let arh= eh[r-1] as f64 - ((n/2) as f64).powi(2*r as i32)/p as f64;
                let cross=ar-2.0*arh;
                let denom = dfac(r as u64) as f64 * ((n as f64).powi(r as i32)-2.0*((n/2) as f64).powi(r as i32));
                let kc=(cross/denom).powf(1.0/r as f64);
                print!("r{}: cross={:.1} denom={:.1} K={:.4}{}  ",r,cross,denom,kc, if cross<=denom+1e-6{""}else{"!!>1"});
            }
            println!();
        }
    }
}
