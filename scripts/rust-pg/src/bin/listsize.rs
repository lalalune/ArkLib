// List size of explicit smooth-domain RS[mu_n, k] past Johnson — the prize list-decoding object.
// L(w, t) = # distinct deg<k codewords agreeing with received word w on >= t points of mu_n.
// Computed via k-subset interpolation + dedup (a list member agrees on >=t>=k pts, so it is the
// interpolant of some k of its agreement points). Max over structured worst-case words w.
// Tests: does the worst-case list stay POLY past Johnson (window t in (rho n, sqrt(rho) n))?
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

// interpolate deg<k poly through points (xs[i], ys[i]) (k points); return coeff vec len k, or None if degenerate
fn interp(idx:&[usize], mu:&[u64], w:&[u64], k:usize, p:u64)->Option<Vec<u64>>{
    // Lagrange -> coefficients. xs distinct (subgroup elements always distinct).
    let xs:Vec<u64>=idx.iter().map(|&i|mu[i]).collect();
    let ys:Vec<u64>=idx.iter().map(|&i|w[i]).collect();
    let mut coef=vec![0u64;k];
    for i in 0..k {
        // basis poly L_i(x) = prod_{j!=i} (x - xs[j])/(xs[i]-xs[j]); scale by ys[i]
        let mut denom=1u64;
        for j in 0..k { if j!=i { denom=mulmod(denom, submod(xs[i],xs[j],p), p); } }
        let scale=mulmod(ys[i], invmod(denom,p), p);
        // numerator poly = prod_{j!=i}(x - xs[j]) ; build coeffs
        let mut np=vec![0u64;k]; np[0]=1; let mut deg=0usize;
        for j in 0..k { if j!=i {
            // multiply np by (x - xs[j])
            let mut nn=vec![0u64;k];
            for t in 0..=deg { nn[t+1]=addmod(nn[t+1], np[t], p); nn[t]=addmod(nn[t], mulmod(np[t], submod(0,xs[j],p), p), p); }
            np=nn; deg+=1;
        }}
        for t in 0..k { coef[t]=addmod(coef[t], mulmod(scale, np[t], p), p); }
    }
    Some(coef)
}
#[inline] fn eval(coef:&[u64], x:u64, p:u64)->u64{ let mut r=0u64; for &c in coef.iter().rev(){ r=addmod(mulmod(r,x,p),c,p);} r }
fn agreement(coef:&[u64], mu:&[u64], w:&[u64], p:u64)->usize{ (0..mu.len()).filter(|&i| eval(coef,mu[i],p)==w[i]).count() }

// next k-combination in lex (in place); false when done
fn next_comb(c:&mut [usize], n:usize)->bool{ let s=c.len(); let mut i=s; while i>0 { i-=1; if c[i]!=i+n-s { c[i]+=1; for j in i+1..s { c[j]=c[j-1]+1;} return true;} } false }

// L(w,t) = # distinct deg<k codewords agreeing with w on >= t points
fn list_size(w:&[u64], mu:&[u64], k:usize, p:u64, t:usize)->usize{
    let n=mu.len();
    // parallelize over first index of the k-subset
    let firsts:Vec<usize>=(0..=n-k).collect();
    let sets:Vec<HashSet<Vec<u64>>>=firsts.par_iter().map(|&f0|{
        let mut found:HashSet<Vec<u64>>=HashSet::new();
        let mut c:Vec<usize>=(0..k).collect(); c[0]=f0; for j in 1..k { c[j]=f0+j; }
        if c[k-1]>=n { return found; }
        loop {
            if let Some(coef)=interp(&c,mu,w,k,p){
                if agreement(&coef,mu,w,p)>=t { found.insert(coef); }
            }
            if c[0]!=f0 { break; }
            if !next_comb(&mut c,n){ break; }
        }
        found
    }).collect();
    let mut all:HashSet<Vec<u64>>=HashSet::new(); for s in sets { all.extend(s); } all.len()
}

fn main(){
    let args:Vec<String>=std::env::args().collect();
    let n:usize=args[1].parse().unwrap();
    let k:usize=args[2].parse().unwrap();
    let p=big_prime(n as u64); let g=proot(p); let h=powmod(g,(p-1)/n as u64,p);
    let mu:Vec<u64>=(0..n).map(|i|powmod(h,i as u64,p)).collect();
    let rho=k as f64/n as f64; let john=1.0-rho.sqrt(); let cap=1.0-rho;
    println!("n={} k={} rho={:.3} p={} Johnson={:.3} cap={:.3}",n,k,rho,p,john,cap);
    // worst-case structured received words: try several (far-line x^a, deep-hole x^k, lacunary x^a+x^b, random)
    let mut words:Vec<(String,Vec<u64>)>=vec![];
    words.push(("x^k (deg-k, just outside)".into(), mu.iter().map(|&x|powmod(x,k as u64,p)).collect()));
    words.push(("x^{n-1} (top)".into(), mu.iter().map(|&x|powmod(x,(n-1) as u64,p)).collect()));
    words.push(("x^{n/2} (antipodal/2-torsion)".into(), mu.iter().map(|&x|powmod(x,(n/2) as u64,p)).collect()));
    words.push(("x^k+x^{k+1}".into(), mu.iter().map(|&x|addmod(powmod(x,k as u64,p),powmod(x,(k+1)as u64,p),p)).collect()));
    // window radii: agreement t from cap (t=rho n) up to Johnson (t=sqrt(rho) n)
    let t_cap=((rho)*n as f64).ceil() as usize;          // capacity agreement ~ rho n (+1)
    let t_john=((rho.sqrt())*n as f64).floor() as usize;  // Johnson agreement ~ sqrt(rho) n
    println!("  window agreement t in [{}..{}] (cap..Johnson); t=k is trivial-MDS (k={})",t_cap.max(k+1),t_john,k);
    for (name,w) in &words {
        print!("  [{}] L(t):", name);
        for t in (k+1..=t_john+1).rev() {
            let l=list_size(w,&mu,k,p,t);
            let delta=1.0-(t as f64)/(n as f64);
            let region = if delta>john {"window"} else {"<=John"};
            print!("  t={}(d={:.2},{}):L={}", t, delta, region, l);
        }
        println!();
    }
    println!("DONE");
}
