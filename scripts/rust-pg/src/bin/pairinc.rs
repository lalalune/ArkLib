// pairinc — PARALLEL single-(u0,u1) incidence at ONE s. Splits the C(n,s) combinations across
// threads by first-index blocks. For n=32 binding-radius single-direction probes.
// Usage: pairinc <n> <k> <s> <mult> <u0word> <u1word>
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
fn big_prime(n:u64,mult:u32)->u64{let mut p=n.pow(mult);if p<1000{p=1000;}p+=(1+n-p%n)%n;loop{if p%n==1&&is_prime(p){return p;}p+=n;}}
#[inline]
fn ddk_idx(vals:&[u64],idx:&[usize],k:usize,p:u64,invd:&[u64],n:usize)->u64{
    let mut vs:[u64;72]=[0u64;72];
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
fn parse_word(s:&str,p:u64)->Vec<(u64,u64)>{
    s.split(',').map(|t|{let mut it=t.split(':');let e:u64=it.next().unwrap().trim().parse().unwrap();
        let c:i64=it.next().unwrap().trim().parse().unwrap();
        let cm=if c<0{p-((-c)as u64%p)}else{c as u64%p};(e,cm)}).collect()
}
fn main(){
    let a:Vec<String>=std::env::args().collect();
    let n:usize=a[1].parse().unwrap();let k:usize=a[2].parse().unwrap();let s:usize=a[3].parse().unwrap();
    let mult:u32=a[4].parse().unwrap();
    let p=big_prime(n as u64,mult);
    let w0=parse_word(&a[5],p);let w1=parse_word(&a[6],p);
    let g=proot(p);let h=powmod(g,(p-1)/n as u64,p);
    let mu:Vec<u64>=(0..n).map(|i|powmod(h,i as u64,p)).collect();
    let mut invd=vec![0u64;n*n];
    for x in 0..n{for y in 0..n{if x!=y{invd[x*n+y]=invmod(submod(mu[x],mu[y],p),p);}}}
    let ev_of=|w:&[(u64,u64)]|->Vec<u64>{let mut ev=vec![0u64;n];
        for &(e,c) in w{for i in 0..n{ev[i]=addmod(ev[i],mulmod(c,powmod(mu[i],e,p),p),p);}}ev};
    let ev0=ev_of(&w0);let ev1=ev_of(&w1);
    let budget=n as u64;
    // parallel over the choice of the FIRST index f in [0, n-s]; for each, enumerate the rest
    // as (s-1)-combinations of [f+1, n). Each thread returns its local distinct-gamma set.
    let firsts:Vec<usize>=(0..=(n-s)).collect();
    let sets:Vec<HashSet<u64>>=firsts.par_iter().map(|&f|{
        let mut local:HashSet<u64>=HashSet::new();
        let rest=s-1; let lo=f+1;
        if lo + rest > n { return local; }
        let mut comb:Vec<usize>=(0..s).collect();
        comb[0]=f; for j in 1..s { comb[j]=lo + (j-1); }
        let mut u0=vec![0u64;s];let mut u1=vec![0u64;s];let mut full=vec![0u64;s];
        loop{
            for (j,&idx) in comb.iter().enumerate(){u0[j]=ev0[idx];u1[j]=ev1[idx];}
            if in_rs_idx(&u1,&comb,k,p,&invd,n){
                // heavy if u0 also in RS — we skip (saturated semantics: do not count)
            } else {
                let a0=ddk_idx(&u0,&comb,k,p,&invd,n);let a1=ddk_idx(&u1,&comb,k,p,&invd,n);
                if a1!=0{let gm=mulmod(submod(0,a0,p),invmod(a1,p),p);
                    for i in 0..s{full[i]=addmod(u0[i],mulmod(gm,u1[i],p),p);}
                    if in_rs_idx(&full,&comb,k,p,&invd,n){local.insert(gm);}}
            }
            // advance only positions 1..s (position 0 fixed = f)
            let mut i=s;let mut adv=false;
            while i>1{i-=1;if comb[i]!=i+n-s{comb[i]+=1;for j in (i+1)..s{comb[j]=comb[j-1]+1;}adv=true;break;}}
            if !adv{break;}
        }
        local
    }).collect();
    let mut all:HashSet<u64>=HashSet::new();
    for st in sets{ for g in st { all.insert(g); } }
    let inc=all.len() as u64;
    println!("n={} k={} s={} (c={}) p={} | u0={:?} u1={:?} : I={} ({})",
        n,k,s,s-k,p,w0,w1,inc, if inc<=budget {"<=budget"} else {">budget"});
}
