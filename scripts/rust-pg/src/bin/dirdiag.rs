// dirdiag — diagnostic for ONE (u0,u1) direction: per-witness gamma multiplicity + total incidence.
// Verifies whether the over-determination dichotomy (<=1 gamma per witness) holds, and reports the
// distinct-gamma count. u0,u1 given as explicit word lists on the command line.
//
// Usage: dirdiag <n> <k> <s> <mult> <u0word> <u1word>
//   word format: "e:c,e:c,..."  (exponent:coeff). coeff -1 written as "-1".
// Example: dirdiag 16 4 6 4 "15:1" "4:1,14:1"
use std::collections::HashSet;
use std::collections::HashMap;

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
    s.split(',').map(|t|{
        let mut it=t.split(':');
        let e:u64=it.next().unwrap().trim().parse().unwrap();
        let cs=it.next().unwrap().trim();
        let c:i64=cs.parse().unwrap();
        let cm= if c<0 { p - ((-c) as u64 % p) } else { c as u64 % p };
        (e,cm)
    }).collect()
}

fn main(){
    let a:Vec<String>=std::env::args().collect();
    let n:usize=a[1].parse().unwrap();
    let k:usize=a[2].parse().unwrap();
    let s:usize=a[3].parse().unwrap();
    let mult:u32=a[4].parse().unwrap();
    let p=big_prime(n as u64,mult);
    let w0=parse_word(&a[5],p);
    let w1=parse_word(&a[6],p);
    let g=proot(p);let h=powmod(g,(p-1)/n as u64,p);
    let mu:Vec<u64>=(0..n).map(|i|powmod(h,i as u64,p)).collect();
    let mut invd=vec![0u64;n*n];
    for x in 0..n{for y in 0..n{if x!=y{invd[x*n+y]=invmod(submod(mu[x],mu[y],p),p);}}}
    let ev_of=|w:&[(u64,u64)]|->Vec<u64>{
        let mut ev=vec![0u64;n];
        for &(e,c) in w{ for i in 0..n{ ev[i]=addmod(ev[i],mulmod(c,powmod(mu[i],e,p),p),p); } }
        ev
    };
    let ev0=ev_of(&w0); let ev1=ev_of(&w1);
    // is u1 far?
    let idxf:Vec<usize>=(0..n).collect();
    let u1far=!in_rs_idx(&ev1,&idxf,k,p,&invd,n);
    let u0far=!in_rs_idx(&ev0,&idxf,k,p,&invd,n);
    println!("# n={} k={} s={} p={} | u0={:?} (far={}) u1={:?} (far={})",n,k,s,p,w0,u0far,w1,u1far);

    // enumerate witnesses, collect gamma per witness, and global gamma multiset
    let mut comb:Vec<usize>=(0..s).collect();
    let mut gamma_count:HashMap<u64,u64>=HashMap::new(); // gamma -> #witnesses that produce it
    let mut distinct:HashSet<u64>=HashSet::new();
    let mut heavy_witnesses=0u64;
    let mut multi_gamma_witnesses=0u64; // witnesses giving >1 gamma (should be 0 if over-det dichotomy)
    let mut u0=vec![0u64;s];let mut u1=vec![0u64;s];let mut full=vec![0u64;s];
    let mut total_witnesses=0u64;
    loop{
        total_witnesses+=1;
        for (j,&idx) in comb.iter().enumerate(){u0[j]=ev0[idx];u1[j]=ev1[idx];}
        let u1in=in_rs_idx(&u1,&comb,k,p,&invd,n);
        if u1in{
            if in_rs_idx(&u0,&comb,k,p,&invd,n){ heavy_witnesses+=1; }
            // if u1 in RS but u0 not: NO finite gamma forces membership unless u0 in RS too
            // (these contribute 0 gammas in the standard count)
        } else {
            let a0=ddk_idx(&u0,&comb,k,p,&invd,n);let a1=ddk_idx(&u1,&comb,k,p,&invd,n);
            if a1!=0{
                let gm=mulmod(submod(0,a0,p),invmod(a1,p),p);
                for i in 0..s{full[i]=addmod(u0[i],mulmod(gm,u1[i],p),p);}
                if in_rs_idx(&full,&comb,k,p,&invd,n){
                    *gamma_count.entry(gm).or_insert(0)+=1;
                    distinct.insert(gm);
                }
            }
        }
        let mut i=s;let mut adv=false;
        while i>0{i-=1;if comb[i]!=i+n-s{comb[i]+=1;for j in (i+1)..s{comb[j]=comb[j-1]+1;}adv=true;break;}}
        if !adv{break;}
    }
    let _=multi_gamma_witnesses;
    // how many distinct gammas; max #witnesses sharing a single gamma; histogram of multiplicities
    let inc=distinct.len();
    let max_share=gamma_count.values().cloned().max().unwrap_or(0);
    let tot_incidences:u64=gamma_count.values().sum();
    println!("incidence (distinct gamma) = {}", inc);
    println!("total (gamma,witness) incidences = {}", tot_incidences);
    println!("total witnesses C(n,s) = {}, heavy(u0,u1 both in RS) = {}", total_witnesses, heavy_witnesses);
    println!("max #witnesses sharing one gamma = {}", max_share);
    // multiplicity histogram
    let mut hist:HashMap<u64,u64>=HashMap::new();
    for &v in gamma_count.values(){ *hist.entry(v).or_insert(0)+=1; }
    let mut hv:Vec<(u64,u64)>=hist.into_iter().collect(); hv.sort();
    println!("gamma-multiplicity histogram (witnesses-per-gamma : #gammas): {:?}", hv);
}
