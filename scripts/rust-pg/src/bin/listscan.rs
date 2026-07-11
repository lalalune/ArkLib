// Broad worst-case list scan: max over MANY received words of the window-interior list size.
// Tests the floor's UPPER bound: does the worst-case list EVER exceed the dilation orbit (O(1)) in the window?
// Words scanned: all monomials x^a (a=0..n-1), all 2-term lacunary x^a+x^b, random words.
use rayon::prelude::*;
use std::collections::HashSet;
#[inline] fn mulmod(a:u64,b:u64,p:u64)->u64{((a as u128*b as u128)%p as u128)as u64}
#[inline] fn addmod(a:u64,b:u64,p:u64)->u64{let s=a+b;if s>=p{s-p}else{s}}
#[inline] fn submod(a:u64,b:u64,p:u64)->u64{if a>=b{a-b}else{p-b+a}}
fn powmod(mut b:u64,mut e:u64,p:u64)->u64{let mut r=1u64;b%=p;while e>0{if e&1==1{r=mulmod(r,b,p);}b=mulmod(b,b,p);e>>=1;}r}
#[inline] fn invmod(a:u64,p:u64)->u64{powmod(a,p-2,p)}
fn isprime(x:u64)->bool{if x<2{return false;}for &q in &[2u64,3,5,7,11,13,17,19,23,29,31,37]{if x%q==0{return x==q;}}let mut d=x-1;let mut s=0;while d%2==0{d/=2;s+=1;}'a:for &a in &[2u64,3,5,7,11,13,17,19,23,29,31,37]{let mut y=powmod(a,d,x);if y==1||y==x-1{continue;}for _ in 0..s-1{y=mulmod(y,y,x);if y==x-1{continue 'a;}}return false;}true}
fn factor(mut x:u64)->Vec<u64>{let mut f=vec![];let mut d=2;while d*d<=x{if x%d==0{f.push(d);while x%d==0{x/=d;}}d+=1;}if x>1{f.push(x);}f}
fn proot(p:u64)->u64{let fs=factor(p-1);for g in 2..p{if fs.iter().all(|&q|powmod(g,(p-1)/q,p)!=1){return g;}}0}
fn big_prime(n:u64)->u64{let mut p=n*n*n*n;loop{if p%n==1&&isprime(p){return p;}p+=1;}}
fn interp(idx:&[usize],mu:&[u64],w:&[u64],k:usize,p:u64)->Vec<u64>{
    let xs:Vec<u64>=idx.iter().map(|&i|mu[i]).collect();
    let ys:Vec<u64>=idx.iter().map(|&i|w[i]).collect();
    let mut coef=vec![0u64;k];
    for i in 0..k{let mut denom=1u64;for j in 0..k{if j!=i{denom=mulmod(denom,submod(xs[i],xs[j],p),p);}}
        let scale=mulmod(ys[i],invmod(denom,p),p);
        let mut np=vec![0u64;k];np[0]=1;let mut deg=0usize;
        for j in 0..k{if j!=i{let mut nn=vec![0u64;k];for t in 0..=deg{nn[t+1]=addmod(nn[t+1],np[t],p);nn[t]=addmod(nn[t],mulmod(np[t],submod(0,xs[j],p),p),p);}np=nn;deg+=1;}}
        for t in 0..k{coef[t]=addmod(coef[t],mulmod(scale,np[t],p),p);}}
    coef}
#[inline] fn eval(c:&[u64],x:u64,p:u64)->u64{let mut r=0u64;for &v in c.iter().rev(){r=addmod(mulmod(r,x,p),v,p);}r}
fn agree(c:&[u64],mu:&[u64],w:&[u64],p:u64)->usize{(0..mu.len()).filter(|&i|eval(c,mu[i],p)==w[i]).count()}
fn next_comb(c:&mut [usize],n:usize)->bool{let s=c.len();let mut i=s;while i>0{i-=1;if c[i]!=i+n-s{c[i]+=1;for j in i+1..s{c[j]=c[j-1]+1;}return true;}}false}
fn list_size(w:&[u64],mu:&[u64],k:usize,p:u64,t:usize)->usize{
    let n=mu.len();
    let firsts:Vec<usize>=(0..=n-k).collect();
    let sets:Vec<HashSet<Vec<u64>>>=firsts.par_iter().map(|&f0|{
        let mut found=HashSet::new();let mut c:Vec<usize>=(0..k).collect();c[0]=f0;for j in 1..k{c[j]=f0+j;}
        if c[k-1]>=n{return found;}
        loop{let coef=interp(&c,mu,w,k,p);if agree(&coef,mu,w,p)>=t{found.insert(coef);}
            if c[0]!=f0{break;} if !next_comb(&mut c,n){break;}}
        found}).collect();
    let mut all=HashSet::new();for s in sets{all.extend(s);} all.len()}
fn main(){
    let args:Vec<String>=std::env::args().collect();
    let n:usize=args[1].parse().unwrap(); let k:usize=args[2].parse().unwrap();
    let p=big_prime(n as u64); let g=proot(p); let h=powmod(g,(p-1)/n as u64,p);
    let mu:Vec<u64>=(0..n).map(|i|powmod(h,i as u64,p)).collect();
    let rho=k as f64/n as f64; let john=1.0-rho.sqrt();
    // window-interior agreement: t = round(0.5*(rho + sqrt(rho))*n) -- midpoint of (rho n, sqrt(rho) n), robustly interior
    let t_mid=(0.5*(rho+rho.sqrt())*(n as f64)).round() as usize;
    let t=t_mid.max(k+2);  // ensure > capacity by >=2
    let delta=1.0-(t as f64)/(n as f64);
    println!("n={} k={} rho={:.3} p={} Johnson={:.3} | window-mid t={} (delta={:.3}, {} Johnson)",n,k,rho,p,john,t,delta, if delta>john {"PAST"} else {"<="});
    // scan all monomials + all 2-term lacunary; track max window list
    let mut words:Vec<(String,Vec<u64>)>=vec![];
    for a in 0..n { words.push((format!("x^{}",a), mu.iter().map(|&x|powmod(x,a as u64,p)).collect())); }
    for a in 1..n { for b in 0..a { words.push((format!("x^{}+x^{}",a,b), mu.iter().map(|&x|addmod(powmod(x,a as u64,p),powmod(x,b as u64,p),p)).collect())); } }
    let results:Vec<(usize,String)>=words.par_iter().map(|(name,w)|{(list_size(w,&mu,k,p,t),name.clone())}).collect();
    let mx=results.iter().max_by_key(|r|r.0).unwrap();
    let nz=results.iter().filter(|r|r.0>0).count();
    println!("  scanned {} words (all monomial + all 2-lacunary); MAX window list = {} at [{}]; {} words have nonzero list",words.len(),mx.0,mx.1,nz);
    // distribution of nonzero list sizes
    let mut dist=std::collections::BTreeMap::new();
    for (l,_) in &results { if *l>0 { *dist.entry(*l).or_insert(0)+=1; } }
    println!("  nonzero list-size distribution: {:?}", dist);
    println!("DONE");
}
