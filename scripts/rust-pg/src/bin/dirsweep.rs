// dirsweep — for a fixed (n,k), find s* = min s such that max-incidence over ALL tested far
// directions (monomial + binomial + trinomial, with several coeffs) is <= budget=n.
// Reports, per s, the max over MONOMIAL-only vs the max over ALL-directions, and the winning dir.
// This decides whether non-monomial directions push s* HIGHER (=> smaller delta*, toward/below Johnson)
// or whether they decay fast enough that s* is unchanged (=> monomial governs the BINDING).
//
// Usage: dirsweep <n> <k> [mult=4] [smin=k+2] [smax=n/2+2]
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
    let n:usize=args[1].parse().unwrap();
    let k:usize=args[2].parse().unwrap();
    let mult:u32=args.get(3).and_then(|a|a.parse().ok()).unwrap_or(4);
    let smin:usize=args.get(4).and_then(|a|a.parse().ok()).unwrap_or(k+2);
    let smax:usize=args.get(5).and_then(|a|a.parse().ok()).unwrap_or(n/2+2);
    let p=big_prime(n as u64,mult);
    let g=proot(p);let h=powmod(g,(p-1)/n as u64,p);
    let mu:Vec<u64>=(0..n).map(|i|powmod(h,i as u64,p)).collect();
    let mut invd=vec![0u64;n*n];
    for x in 0..n{for y in 0..n{if x!=y{invd[x*n+y]=invmod(submod(mu[x],mu[y],p),p);}}}
    let mut powtab=vec![0u64;n*n];
    for e in 0..n{for i in 0..n{powtab[e*n+i]=powmod(mu[i],e as u64,p);}}
    let budget=n as u64;
    let ev_of=|word:&[(u64,u64)]|->Vec<u64>{
        let mut ev=vec![0u64;n];
        for &(e,c) in word{ for i in 0..n{ ev[i]=addmod(ev[i],mulmod(c%p,powtab[(e as usize)*n+i],p),p); } }
        ev
    };
    let bases:Vec<u64>=((k as u64)..(n as u64)).collect();
    // build direction families (each tagged: 1=mono,2=bino,3=trino)
    let mut dirs:Vec<(u8,Vec<(u64,u64)>)>=vec![];
    for b in (k as u64)..(n as u64){ dirs.push((1,vec![(b,1)])); }
    for b1 in (k as u64)..(n as u64){ for b2 in (b1+1)..(n as u64){
        for &c in &[1u64,2u64,p-1]{ dirs.push((2,vec![(b1,1),(b2,c)])); }
    }}
    for b1 in (k as u64)..(n as u64){ for b2 in (b1+1)..(n as u64){ for b3 in (b2+1)..(n as u64){
        dirs.push((3,vec![(b1,1),(b2,1),(b3,1)]));
        dirs.push((3,vec![(b1,1),(b2,p-1),(b3,1)]));
    }}}
    println!("# n={} k={} p={} budget={} #dirs={} (mono+bino+trino)",n,k,p,budget,dirs.len());
    let mut sstar_mono=0usize; let mut sstar_all=0usize;
    for s in smin..=smax {
        // per direction: max over monomial bases
        let results:Vec<(u8,u64,Vec<(u64,u64)>,u64)> = dirs.par_iter().map(|(tag,word)|{
            let supp:HashSet<u64>=word.iter().map(|&(e,_)|e).collect();
            let ev1=ev_of(word);
            let idxf:Vec<usize>=(0..n).collect();
            if in_rs_idx(&ev1,&idxf,k,p,&invd,n){ return (*tag,0u64,word.clone(),0u64); }
            let mut best=0u64; let mut ba=0u64;
            for &a in &bases{ if supp.contains(&a){continue;}
                let ev0=ev_of(&[(a,1u64)]);
                let inc=incidence_ev(n,&ev0,&ev1,k,p,s,&invd);
                let v=if inc==u64::MAX{0}else{inc};
                if v>best{best=v;ba=a;}
            }
            (*tag,best,word.clone(),ba)
        }).collect();
        let mut mono_mx=0u64; let mut all_mx=0u64; let mut all_arg=(0u8,vec![],0u64);
        for (tag,v,w,ba) in &results {
            if *tag==1 && *v>mono_mx { mono_mx=*v; }
            if *v>all_mx { all_mx=*v; all_arg=(*tag,w.clone(),*ba); }
        }
        let gm= mono_mx<=budget; let ga= all_mx<=budget;
        println!("  s={} (c={}): monoMax={:>6} allMax={:>6} {}  winner=tag{} u1={:?} base=x^{}",
            s,s-k,mono_mx,all_mx, if all_mx>mono_mx {"[NONMONO WINS]"} else {"[mono>=]"},
            all_arg.0, all_arg.1, all_arg.2);
        if gm && sstar_mono==0 { sstar_mono=s; }
        if ga && sstar_all==0 { sstar_all=s; }
        if sstar_all>0 && sstar_mono>0 { break; }
    }
    let dm=(n-sstar_mono)as f64/n as f64; let da=(n-sstar_all)as f64/n as f64;
    let john=1.0-(k as f64/n as f64).sqrt();
    println!("=> n={} k={}: s*_mono={} (m*={}, d*={:.4})  s*_all={} (m*={}, d*={:.4})  Johnson={:.4}",
        n,k,sstar_mono,sstar_mono as i64-k as i64,dm,sstar_all,sstar_all as i64-k as i64,da,john);
    if sstar_all>sstar_mono { println!("   ==> NON-MONOMIAL PUSHES s* HIGHER => delta* SMALLER (toward/below Johnson)"); }
    else if sstar_all==sstar_mono { println!("   ==> s* UNCHANGED: non-monomial decays fast, MONOMIAL GOVERNS THE BINDING"); }
}
