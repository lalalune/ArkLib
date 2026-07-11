// SECOND-HORN boundary mapper for the §6 dichotomy (#444 decoupling lane).
// For given (n,k): full (a,b) in [1,n)^2 a!=b direction sweep, exact incidence per witness size s,
// reports the TRUE max incidence profile I(s), the binding s* (first s with maxI<=budget=n),
// c*=s*-k, delta*=(n-s*)/n, and the maximizing direction. Multi-prime via mult arg (p~n^mult).
// Usage: secondhorn <n> <k> [mult=4]
use rayon::prelude::*;
use std::collections::HashSet;

#[inline] fn mulmod(a:u64,b:u64,p:u64)->u64{((a as u128*b as u128)%p as u128)as u64}
#[inline] fn addmod(a:u64,b:u64,p:u64)->u64{let s=a+b;if s>=p{s-p}else{s}}
#[inline] fn submod(a:u64,b:u64,p:u64)->u64{if a>=b{a-b}else{p-b+a}}
fn powmod(mut b:u64,mut e:u64,p:u64)->u64{let mut r=1u64;b%=p;while e>0{if e&1==1{r=mulmod(r,b,p);}b=mulmod(b,b,p);e>>=1;}r}
#[inline] fn invmod(a:u64,p:u64)->u64{powmod(a,p-2,p)}
fn is_prime(x:u64)->bool{if x<2{return false;}for &q in &[2u64,3,5,7,11,13,17,19,23,29,31,37]{if x%q==0{return x==q;}}let mut d=x-1;let mut s=0;while d%2==0{d/=2;s+=1;}'a:for &a in &[2u64,3,5,7,11,13,17,19,23,29,31,37]{let mut y=powmod(a,d,x);if y==1||y==x-1{continue;}for _ in 0..s-1{y=mulmod(y,y,x);if y==x-1{continue 'a;}}return false;}true}
fn factor(mut x:u64)->Vec<u64>{let mut f=vec![];let mut d=2;while d*d<=x{if x%d==0{f.push(d);while x%d==0{x/=d;}}d+=1;}if x>1{f.push(x);}f}
fn proot(p:u64)->u64{let fs=factor(p-1);for g in 2..p{if fs.iter().all(|&q|powmod(g,(p-1)/q,p)!=1){return g;}}0}
fn big_prime(n:u64,mult:u32)->u64{let mut p=n.pow(mult);if p<1000{p=1000;}p+= (1 + n - p % n) % n; loop{if p%n==1&&is_prime(p){return p;}p+=n;}}

#[inline]
fn ddk_idx(vals:&[u64],idx:&[usize],k:usize,p:u64,invd:&[u64],n:usize)->u64{
    let mut vs:[u64;64]=[0u64;64];
    for t in 0..=k{vs[t]=vals[t];}
    for j in 1..=k{for i in (j..=k).rev(){let inv=invd[idx[i]*n+idx[i-j]];vs[i]=mulmod(submod(vs[i],vs[i-1],p),inv,p);}}
    vs[k]
}
#[inline]
fn in_rs_idx(vals:&[u64],idx:&[usize],k:usize,p:u64,invd:&[u64],n:usize)->bool{
    let s=idx.len(); if s<=k{return true;}
    for st in 0..(s-k){if ddk_idx(&vals[st..st+k+1],&idx[st..st+k+1],k,p,invd,n)!=0{return false;}}
    true
}
fn incidence(n:usize,mua:&[u64],mub:&[u64],k:usize,p:u64,s:usize,invd:&[u64])->u64{
    let mut local:HashSet<u64>=HashSet::new();
    let mut comb:Vec<usize>=(0..s).collect();
    let mut u0=vec![0u64;s];let mut u1=vec![0u64;s];let mut full=vec![0u64;s];
    loop{
        for (j,&idx) in comb.iter().enumerate(){u0[j]=mua[idx];u1[j]=mub[idx];}
        if in_rs_idx(&u1,&comb,k,p,invd,n){
            if in_rs_idx(&u0,&comb,k,p,invd,n){return u64::MAX;}
        } else {
            let a0=ddk_idx(&u0,&comb,k,p,invd,n);let a1=ddk_idx(&u1,&comb,k,p,invd,n);
            if a1!=0{let gm=mulmod(submod(0,a0,p),invmod(a1,p),p);
                for i in 0..s{full[i]=addmod(u0[i],mulmod(gm,u1[i],p),p);}
                if in_rs_idx(&full,&comb,k,p,invd,n){local.insert(gm);}}
        }
        let mut i=s;let mut adv=false;
        while i>0{i-=1;if comb[i]!=i+n-s{comb[i]+=1;for j in (i+1)..s{comb[j]=comb[j-1]+1;}adv=true;break;}}
        if !adv{break;}
    }
    local.len() as u64
}

fn main(){
    let args:Vec<String>=std::env::args().collect();
    let n:usize=args[1].parse().unwrap();
    let k:usize=args[2].parse().unwrap();
    let mult:u32=args.get(3).and_then(|a|a.parse().ok()).unwrap_or(4);
    let p=big_prime(n as u64,mult);
    let g=proot(p);let h=powmod(g,(p-1)/n as u64,p);
    let mu:Vec<u64>=(0..n).map(|i|powmod(h,i as u64,p)).collect();
    let mut invd=vec![0u64;n*n];
    for a in 0..n{for b in 0..n{if a!=b{invd[a*n+b]=invmod(submod(mu[a],mu[b],p),p);}}}
    let budget=n as u64;
    let rho=k as f64/n as f64;
    let m=(p-1)/n as u64;
    println!("# n={} k={} rho={:.4} p={} m={} budget={} (FULL (a,b) sweep, a,b in [1,n) a!=b)",n,k,rho,p,m,budget);
    // all directions a,b in [1,n), a!=b (exclude 0 = constant)
    let dirs:Vec<(u64,u64)>=(1..n as u64).flat_map(|b|(1..n as u64).filter(move|&a|a!=b).map(move|a|(a,b))).collect();
    let mut sstar=0usize;
    for s in (k+2)..n {
        let csz={let kk=(s as u64).min(n as u64-s as u64);let mut r:u128=1;for i in 0..kk{r=r*(n as u64-i)as u128/(i+1)as u128;}r};
        if csz>200_000_000{println!("  s={} C={} too big, stop",s,csz);break;}
        let (mx,arg)=dirs.par_iter().map(|&(a,b)|{
            let mua:Vec<u64>=(0..n).map(|i|powmod(mu[i],a,p)).collect();
            let mub:Vec<u64>=(0..n).map(|i|powmod(mu[i],b,p)).collect();
            let inc=incidence(n,&mua,&mub,k,p,s,&invd);
            if inc==u64::MAX{(0u64,(a,b))}else{(inc,(a,b))}
        }).reduce(||(0u64,(0u64,0u64)),|x,y|if y.0>x.0{y}else{x});
        let good=mx<=budget;
        println!("  s={} (c=s-k={}): maxI={} at {:?} {}",s,s-k,mx,arg,if good{"<=budget GOOD"}else{"bad"});
        if good&&sstar==0{sstar=s;}
        if s>=n/2+2 && sstar>0 {break;}
    }
    if sstar>0{
        let ds=(n-sstar)as f64/n as f64;
        let john=1.0-rho.sqrt();
        println!("=> s*={} c*=s*-k={} delta*={:.4} c*/n={:.4} [Johnson {:.4}] horn={}",
            sstar,sstar-k,ds,(sstar-k)as f64/n as f64,john,
            if (sstar as f64-k as f64)/n as f64 > 0.15 {"FIRST?(deep)"} else {"SECOND?(shallow/recouple)"});
    } else {
        println!("=> NO crossing in band (under-determined / re-couple candidate)");
    }
}
