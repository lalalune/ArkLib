// worstgap.rs — for fixed (n,k), scan ALL 2-lacunary words x^a+x^b and report, per window radius t,
// the MAX list size and the argmax word. Distinguishes the trivial capacity-edge spike (t=k+1)
// from the genuine worst-case window list deeper out. Also flags whether the argmax word's
// frequency support {0..k-1,a,b} is a CONTIGUOUS band (which is provably <=k+1 agreement) or GAPPED.
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
    let n=mu.len();let firsts:Vec<usize>=(0..=n-k).collect();
    let sets:Vec<HashSet<Vec<u64>>>=firsts.par_iter().map(|&f0|{
        let mut found=HashSet::new();let mut c:Vec<usize>=(0..k).collect();c[0]=f0;for j in 1..k{c[j]=f0+j;}
        if c[k-1]>=n{return found;}
        loop{let coef=interp(&c,mu,w,k,p);if agree(&coef,mu,w,p)>=t{found.insert(coef);}
            if c[0]!=f0{break;} if !next_comb(&mut c,n){break;}}
        found}).collect();
    let mut all=HashSet::new();for s in sets{all.extend(s);} all.len()}
// is the support {0..k-1, a, b} a contiguous block mod n?
fn is_band(a:usize,b:usize,k:usize,n:usize)->bool{
    let mut s:Vec<usize>=(0..k).collect(); s.push(a%n); s.push(b%n); s.sort(); s.dedup();
    // contiguous mod n iff complement is contiguous: check max run of present == len, cyclically
    let present:HashSet<usize>=s.iter().cloned().collect();
    // find a gap start, then walk
    let m=s.len();
    // try each rotation start: contiguous iff there exists i with present = {i,i+1,...,i+m-1} mod n
    for &start in &s { let mut ok=true; for d in 0..m { if !present.contains(&((start+d)%n)){ok=false;break;} } if ok {return true;} }
    false
}
fn main(){
    let args:Vec<String>=std::env::args().collect();
    let n:usize=args[1].parse().unwrap(); let k:usize=args[2].parse().unwrap();
    let p=big_prime(n as u64);let g=proot(p);let h=powmod(g,(p-1)/n as u64,p);
    let mu:Vec<u64>=(0..n).map(|i|powmod(h,i as u64,p)).collect();
    let rho=k as f64/n as f64; let john=1.0-rho.sqrt();
    let t_cap=(rho*n as f64).ceil() as usize; let t_john=(rho.sqrt()*n as f64).floor() as usize;
    let t_lo=t_cap.max(k)+1; // first level past capacity
    println!("n={} k={} rho={:.3} p={} John={:.3} | window t in [{}..{}] (capacity+1 .. Johnson)",n,k,rho,p,john,t_lo,t_john);
    // all 2-lacunary words
    let words:Vec<(usize,usize)>=(1..n).flat_map(|a|(0..a).map(move|b|(a,b))).collect();
    // for each t, find max L and argmax over all words
    for t in (t_lo..=t_john).rev(){
        let res:Vec<(usize,usize,usize)>=words.par_iter().map(|&(a,b)|{
            let w:Vec<u64>=mu.iter().map(|&x|addmod(powmod(x,a as u64,p),powmod(x,b as u64,p),p)).collect();
            (list_size(&w,&mu,k,p,t),a,b)}).collect();
        let &(mx,ma,mb)=res.iter().max_by_key(|r|r.0).unwrap();
        let delta=1.0-(t as f64)/(n as f64);
        let nzwords=res.iter().filter(|r|r.0>0).count();
        let band=is_band(ma,mb,k,n);
        let kind=if t==t_lo {"<-capacity+1 spike (trivial)"} else {""};
        println!("  t={} d={:.3}{}: MAX L={} @ x^{}+x^{} ({}); {} words nonzero {}",
            t,delta, if delta>john{" WIN"}else{" Joh"}, mx,ma,mb, if band{"CONTIGUOUS-band"}else{"GAPPED"}, nzwords, kind);
    }
    println!("DONE");
}
