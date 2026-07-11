// binoscan — scan ALL binomial far directions u1 = x^b1 + c*x^b2 (b1<b2 in [k,n), c in {1,-1,2}),
// each against ALL monomial bases x^a, and report:
//   - the edge incidence I(k+2) and the incidence at the MONOMIAL binding radius s*_mono
//   - whether ANY binomial direction LINGERS (I > budget) at s*_mono  (=> would push s* higher)
//   - the decay shape (does it crash to ~0 in one step, or decay slowly like a monomial orbit?)
// This tests the squeeze-critical claim: do non-monomials ever decay SLOWLY (orbit-like)?
//
// Usage: binoscan <n> <k> <sstar_mono> [mult=4]
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
fn incidence_ev(n:usize,ev0:&[u64],ev1:&[u64],k:usize,p:u64,s:usize,invd:&[u64])->u64{
    let mut local:HashSet<u64>=HashSet::new();
    let mut comb:Vec<usize>=(0..s).collect();
    let mut u0=vec![0u64;s];let mut u1=vec![0u64;s];let mut full=vec![0u64;s];
    loop{
        for (j,&idx) in comb.iter().enumerate(){u0[j]=ev0[idx];u1[j]=ev1[idx];}
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
    let n:usize=args[1].parse().unwrap();let k:usize=args[2].parse().unwrap();
    let sstar:usize=args[3].parse().unwrap();
    let mult:u32=args.get(4).and_then(|a|a.parse().ok()).unwrap_or(4);
    let p=big_prime(n as u64,mult);
    let g=proot(p);let h=powmod(g,(p-1)/n as u64,p);
    let mu:Vec<u64>=(0..n).map(|i|powmod(h,i as u64,p)).collect();
    let mut invd=vec![0u64;n*n];
    for x in 0..n{for y in 0..n{if x!=y{invd[x*n+y]=invmod(submod(mu[x],mu[y],p),p);}}}
    let mut powtab=vec![0u64;n*n];
    for e in 0..n{for i in 0..n{powtab[e*n+i]=powmod(mu[i],e as u64,p);}}
    let ev_of=|word:&[(u64,u64)]|->Vec<u64>{let mut ev=vec![0u64;n];
        for &(e,c) in word{for i in 0..n{ev[i]=addmod(ev[i],mulmod(c%p,powtab[(e as usize)*n+i],p),p);}}ev};
    let budget=n as u64;
    let bases:Vec<u64>=((k as u64)..(n as u64)).collect();
    let edge=k+2;
    // all binomials
    let mut bino:Vec<Vec<(u64,u64)>>=vec![];
    for b1 in (k as u64)..(n as u64){for b2 in (b1+1)..(n as u64){for &c in &[1u64,p-1,2u64]{bino.push(vec![(b1,1),(b2,c)]);}}}
    println!("# n={} k={} edge_s={} sstar_mono={} budget={} #bino={}",n,k,edge,sstar,budget,bino.len());
    // for each binomial: max over bases of I(edge) and of I(sstar). Also count how many LINGER at sstar.
    let stats:Vec<(u64,u64,Vec<(u64,u64)>)> = bino.par_iter().map(|word|{
        let supp:HashSet<u64>=word.iter().map(|&(e,_)|e).collect();
        let ev1=ev_of(word);
        let idxf:Vec<usize>=(0..n).collect();
        if in_rs_idx(&ev1,&idxf,k,p,&invd,n){return (0u64,0u64,word.clone());}
        let mut bedge=0u64; let mut bstar=0u64;
        for &a in &bases{ if supp.contains(&a){continue;}
            let ev0=ev_of(&[(a,1)]);
            let ie=incidence_ev(n,&ev0,&ev1,k,p,edge,&invd); let ie=if ie==u64::MAX{0}else{ie};
            let is=incidence_ev(n,&ev0,&ev1,k,p,sstar,&invd); let is=if is==u64::MAX{0}else{is};
            if ie>bedge{bedge=ie;}
            if is>bstar{bstar=is;}
        }
        (bedge,bstar,word.clone())
    }).collect();
    let max_edge=stats.iter().map(|s|s.0).max().unwrap();
    let max_star=stats.iter().map(|s|s.1).max().unwrap();
    let lingering:Vec<&(u64,u64,Vec<(u64,u64)>)>=stats.iter().filter(|s|s.1>budget).collect();
    println!("max binomial I(edge={}) = {}", edge, max_edge);
    println!("max binomial I(sstar={}) = {}  (budget={})", sstar, max_star, budget);
    println!("# binomials still ABOVE budget at sstar_mono = {}", lingering.len());
    if lingering.is_empty(){
        println!("=> NO binomial lingers at s*_mono => binomials do NOT push s* higher. MONOMIAL GOVERNS BINDING.");
    } else {
        println!("=> {} binomials LINGER above budget at s*_mono => they WOULD push s* higher!", lingering.len());
        for l in lingering.iter().take(8){ println!("     u1={:?}  I(sstar)={}",l.2,l.1); }
    }
    // also report the single binomial with the biggest I(sstar) and its edge
    let argmax=stats.iter().max_by_key(|s|s.1).unwrap();
    println!("   biggest-at-sstar binomial: u1={:?} I(edge)={} I(sstar)={}",argmax.2,argmax.0,argmax.1);
}
