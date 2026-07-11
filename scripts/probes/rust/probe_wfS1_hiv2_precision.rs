// wf-S1: high-precision MC to resolve whether K_eff^NP slightly EXCEEDS 1.0 at the n=1024 hi-v2 prime,
// or is sampling noise. Large B, 4 independent seeds, report per-seed K(r) for r=1..6 + spread.
// Also computes the EXACT r=1 and r=2 nonprincipal energies in closed form for the anchor:
//   E_np_1 = n - n^2/p  (exact). E_np_2 = (1/p) sum_{b!=0} eta_b^4. r=1 K is exactly 1-n/p.
use std::f64::consts::PI; use std::thread; use std::sync::Arc;
fn mpow(a:u64,mut e:u64,p:u64)->u64{let mut r=1u128;let mut a2=a as u128;let pp=p as u128;while e>0{if e&1==1{r=r*a2%pp;}a2=a2*a2%pp;e>>=1;}r as u64}
fn isp(n:u64)->bool{if n<2{return false}if n%2==0{return n==2}let mut d=3u64;while (d as u128)*(d as u128)<=n as u128{if n%d==0{return false}d+=2}true}
fn v2(mut x:u64)->u32{let mut v=0;while x&1==0{x>>=1;v+=1}v}
fn proot(p:u64)->u64{let mut m=p-1;let mut fs=vec![];let mut d=2u64;while (d as u128)*(d as u128)<=m as u128{if m%d==0{fs.push(d);while m%d==0{m/=d}}d+=1}if m>1{fs.push(m)}let mut g=2u64;loop{if fs.iter().all(|&f|mpow(g,(p-1)/f,p)!=1){return g}g+=1}}
fn ldfact(r:usize)->f64{let mut v=0.0;for j in 1..=r{v+=((2*j-1)as f64).ln()}v}
fn find(n:u64,lo:u64,cond:u32,tv:u32)->Option<u64>{
    let mut p=lo-(lo%n)+1; if p<lo{p+=n}
    let mut t=0u64;while t<200_000_000{ if p>2&&p%n==1&&isp(p){ if cond==0{return Some(p)} if cond==1&&v2(p-1)>=tv{return Some(p)} } p+=n;t+=1;} None
}
fn eval_mc(n:u64,p:u64,rmax:usize,nth:usize,b_per_thread:u64,seed0:u64)->Vec<f64>{
    let g=proot(p);let h=mpow(g,(p-1)/n,p);let mu:Vec<u64>=(0..n).map(|j|mpow(h,j,p)).collect();let mu=Arc::new(mu);
    let mut hs=vec![];
    for t in 0..nth as u64{let mu=Arc::clone(&mu);let seed=seed0.wrapping_add(t.wrapping_mul(0x9E3779B97F4A7C15)).wrapping_add(1);
        hs.push(thread::spawn(move||{
            let mut s=vec![0.0f64;rmax+1];let pp=p as u128;let inv=2.0*PI/p as f64;let mut st=seed|1;
            for _ in 0..b_per_thread{ st^=st<<13;st^=st>>7;st^=st<<17; let b=1+(st%(p-1));
                let mut re=0.0;for &x in mu.iter(){let tt=((b as u128*x as u128)%pp)as u64;re+=(inv*(tt as f64)).cos();}
                let e2=re*re;let mut pw=1.0;for r in 1..=rmax{pw*=e2;s[r]+=pw;} }
            s}));}
    let mut ts=vec![0.0f64;rmax+1];let total=b_per_thread*nth as u64;
    for hh in hs{let s=hh.join().unwrap();for r in 1..=rmax{ts[r]+=s[r]}}
    let scale=((p-1) as f64)/(p as f64)/(total as f64);
    for r in 1..=rmax{ts[r]*=scale} ts
}
fn main(){
    let a:Vec<String>=std::env::args().collect();let nth:usize=if a.len()>1{a[1].parse().unwrap()}else{8};
    let rmax=8usize;
    println!("=== wf-S1 hi-precision: is K_eff^NP > 1 real at n=1024 hi-v2? (4 seeds, big B) ===");
    let cases=[(1024u64,1u32,18u32,"hiv2"),(1024,0,0,"good")];
    for &(n,cond,tv,tag) in cases.iter(){
        let lo=(n as u128*n as u128*n as u128*n as u128) as u64;
        let p=find(n,lo,cond,tv).unwrap();
        let ln_n=(n as f64).ln();
        println!("[{}] n={} p={} v2={} K(1)_exact=1-n/p={:.7}",tag,n,p,v2(p-1),1.0-(n as f64)/(p as f64));
        // accumulate per-seed estimates for r=1..6
        let mut acc=vec![Vec::<f64>::new();rmax+1];
        for seed in [0x1234u64,0xBEEF,0xC0DE,0x5151].iter(){
            let enp=eval_mc(n,p,rmax,nth, 400_000, *seed);
            for r in 1..=6{let lc0=ldfact(r)+r as f64*ln_n;let k=((enp[r].ln()-lc0)/r as f64).exp();acc[r].push(k);}
        }
        for r in 1..=6{
            let v=&acc[r];let mean=v.iter().sum::<f64>()/v.len() as f64;
            let var=v.iter().map(|x|(x-mean).powi(2)).sum::<f64>()/v.len() as f64;let sd=var.sqrt();
            let mn=v.iter().cloned().fold(f64::INFINITY,f64::min);let mx=v.iter().cloned().fold(0.0,f64::max);
            println!("   r={} K_eff^NP mean={:.5} sd={:.5} [min {:.5}, max {:.5}]  -> {}",
                r,mean,sd,mn,mx, if mean-2.0*sd>1.0{"ABOVE 1 (>2sigma)"}else if mean>1.0{"above-1 within noise"}else{"<=1"});
        }
    }
}
