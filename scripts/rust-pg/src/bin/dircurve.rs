// dircurve — per-direction I(s) DECAY CURVE for an explicit (u0,u1) word, swept over s.
// Reports, for each s in [k+2, smax], the incidence I(s) for the given direction, and where it
// crosses budget=n (its own binding radius). Lets us compare monomial vs binomial DECAY directly.
//
// Usage: dircurve <n> <k> <mult> <u0word> <u1word> [smax]
//   word format "e:c,e:c,...". Use base sweep separately; here u0 fixed.
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
fn parse_word(s:&str,p:u64)->Vec<(u64,u64)>{
    s.split(',').map(|t|{let mut it=t.split(':');let e:u64=it.next().unwrap().trim().parse().unwrap();
        let c:i64=it.next().unwrap().trim().parse().unwrap();
        let cm=if c<0{p-((-c)as u64%p)}else{c as u64%p};(e,cm)}).collect()
}
fn nck(n:u64,k:u64)->u128{if k>n{return 0;}let k=k.min(n-k);let mut r:u128=1;for i in 0..k{r=r*(n-i)as u128/(i+1)as u128;}r}
fn main(){
    let a:Vec<String>=std::env::args().collect();
    let n:usize=a[1].parse().unwrap();let k:usize=a[2].parse().unwrap();let mult:u32=a[3].parse().unwrap();
    let p=big_prime(n as u64,mult);
    let w0=parse_word(&a[4],p);let w1=parse_word(&a[5],p);
    let smax:usize=a.get(6).and_then(|x|x.parse().ok()).unwrap_or(n/2+2);
    let g=proot(p);let h=powmod(g,(p-1)/n as u64,p);
    let mu:Vec<u64>=(0..n).map(|i|powmod(h,i as u64,p)).collect();
    let mut invd=vec![0u64;n*n];
    for x in 0..n{for y in 0..n{if x!=y{invd[x*n+y]=invmod(submod(mu[x],mu[y],p),p);}}}
    let ev_of=|w:&[(u64,u64)]|->Vec<u64>{let mut ev=vec![0u64;n];
        for &(e,c) in w{for i in 0..n{ev[i]=addmod(ev[i],mulmod(c,powmod(mu[i],e,p),p),p);}}ev};
    let ev0=ev_of(&w0);let ev1=ev_of(&w1);
    let budget=n as u64;
    println!("# n={} k={} p={} budget={} u0={:?} u1={:?}",n,k,p,budget,w0,w1);
    let mut cross=0usize;
    for s in (k+2)..=smax{
        if nck(n as u64,s as u64)>400_000_000{println!("  s={} C too big",s);break;}
        let inc=incidence_ev(n,&ev0,&ev1,k,p,s,&invd);
        let is=if inc==u64::MAX{"HEAVY".to_string()}else{inc.to_string()};
        let mark=if inc!=u64::MAX && inc<=budget {if cross==0{cross=s;} " <=budget"} else {""};
        println!("  s={} (c={}): I={}{}",s,s-k,is,mark);
    }
    if cross>0{println!("=> this direction binds at s={} (m={})",cross,cross as i64-k as i64);}
}
