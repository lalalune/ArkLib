// periodscan — Track A (#444): period distribution + tail-excess of thin dyadic mu_n.
// Computes M=max_{b!=0}|eta_b|, the top-K periods, tail-excess vs Gaussian extreme-value,
// and scans across primes p≡1 mod n (beta≈4) to correlate badness with v2(p-1)/m-structure.
// Usage: periodscan <n> <num_primes> [start_offset_in_blocks]
use rayon::prelude::*;
#[inline] fn mulmod(a:u64,b:u64,p:u64)->u64{((a as u128*b as u128)%p as u128)as u64}
fn powmod(mut b:u64,mut e:u64,p:u64)->u64{let mut r=1u64;b%=p;while e>0{if e&1==1{r=mulmod(r,b,p);}b=mulmod(b,b,p);e>>=1;}r}
fn isprime(x:u64)->bool{if x<2{return false;}for &q in &[2u64,3,5,7,11,13,17,19,23,29,31,37]{if x%q==0{return x==q;}}let mut d=x-1;let mut s=0;while d%2==0{d/=2;s+=1;}'a:for &a in &[2u64,3,5,7,11,13,17,19,23,29,31,37]{let mut y=powmod(a,d,x);if y==1||y==x-1{continue;}for _ in 0..s-1{y=mulmod(y,y,x);if y==x-1{continue 'a;}}return false;}true}
fn factor(mut x:u64)->Vec<u64>{let mut f=vec![];let mut d=2;while d*d<=x{if x%d==0{f.push(d);while x%d==0{x/=d;}}d+=1;}if x>1{f.push(x);}f}
fn proot(p:u64)->u64{let fs=factor(p-1);for g in 2..p{if fs.iter().all(|&q|powmod(g,(p-1)/q,p)!=1){return g;}}0}
fn v2(mut x:u64)->u32{let mut v=0;while x%2==0{x/=2;v+=1;}v}

// compute exact |eta_b|^2 for all m cosets; return (M2max, top moments E[X], E[X^2], E[X^3], E[X^4], top3 periods)
fn periods(n:u64,p:u64)->(f64,f64,f64,f64,f64,[f64;3],u64){
    let g=proot(p); let m=(p-1)/n;
    let h=powmod(g,(p-1)/n,p);
    let mu:Vec<u64>=(0..n).map(|i|powmod(h,i,p)).collect();
    let tau=2.0*std::f64::consts::PI/(p as f64);
    // precompute exp table? p huge. compute per-term cos/sin.
    let chunk:Vec<(f64,f64,f64,f64,f64,[f64;3])>=(0..m).into_par_iter().map(|j|{
        let b=powmod(g,j,p);
        let mut re=0.0f64; let mut im=0.0f64;
        for &x in &mu{
            let bx=mulmod(b,x,p) as f64;
            let a=tau*bx;
            re+=a.cos(); im+=a.sin();
        }
        let x2=re*re+im*im;
        let mut top=[0.0f64;3];
        top[0]=x2;
        (x2, x2*x2, x2*x2*x2, x2*x2*x2*x2, x2, top)
    }).collect();
    // aggregate
    let mut s1=0.0;let mut s2=0.0;let mut s3=0.0;let mut s4=0.0;let mut mx=0.0f64;
    let mut top=[0.0f64;3];
    for c in &chunk{
        s1+=c.0; s2+=c.1; s3+=c.2; s4+=c.3;
        let x=c.4;
        if x>mx{mx=x;}
        if x>top[0]{top[2]=top[1];top[1]=top[0];top[0]=x;}
        else if x>top[1]{top[2]=top[1];top[1]=x;}
        else if x>top[2]{top[2]=x;}
    }
    let mf=m as f64;
    (mx, s1/mf, s2/mf, s3/mf, s4/mf, top, m)
}

fn main(){
    let args:Vec<String>=std::env::args().collect();
    let n:u64=args.get(1).and_then(|s|s.parse().ok()).unwrap_or(64);
    let num:usize=args.get(2).and_then(|s|s.parse().ok()).unwrap_or(30);
    let off:i64=args.get(3).and_then(|s|s.parse().ok()).unwrap_or(0);
    // start near n^4
    let base=n.pow(4);
    let mut p=(base as i64 + off*(n as i64)) as u64;
    p += (n + 1 - p%n)%n; // make p≡1 mod n
    println!("# n={} beta-target=4  base=n^4={}", n, base);
    println!("# {:>11} {:>3} {:>9} {:>11} {:>9} {:>9} {:>9}", "p","v2","R","top1/nlogm","E[X]/n","EX2/EX^2","EX4/EX^4");
    let mut found=0;
    let mut bad=vec![];
    while found<num{
        if p%n==1 && isprime(p){
            let (m2,e1,e2,_e3,e4,top,m)=periods(n,p);
            let mm=(m as f64).ln();
            let r=m2.sqrt()/(2.0*(n as f64)*mm).sqrt();
            let t1=m2/((n as f64)*mm);
            let nf=n as f64;
            let ex2norm=e2/(e1*e1);
            let ex4norm=e4/(e1*e1*e1*e1);
            let flag=if r>1.0{" <<<BAD"}else if r>0.97{" marg"}else{""};
            println!("{:>13} {:>3} {:>9.4} {:>11.4} {:>9.4} {:>9.4} {:>9.2}  top=[{:.0},{:.0},{:.0}] m={}{}",
                p, v2(p-1), r, t1, e1/nf, ex2norm, ex4norm, top[0],top[1],top[2], m, flag);
            if r>1.0 { bad.push((p,v2(p-1))); }
            found+=1;
        }
        p+=n;
    }
    println!("# BAD primes (R>1): {:?}", bad);
}
