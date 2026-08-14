// Necklace (cyclic-orbit) accelerated far-line incidence for #444 growth-law.
// mu_n is closed under x -> h*x (cyclic shift of indices i -> i+1 mod n). The over-det
// incidence I(a,b;s) (# distinct gamma s.t. x^a + gamma x^b agrees with deg<k poly on >=s pts)
// is shift-COVARIANT: rotating a witness subset by t multiplies its gamma by h^{(b-a)*t}.
// So we enumerate s-subsets up to cyclic rotation (canonical = lexicographically-smallest
// rotation, ~n x fewer), find each subset's gamma, then the true distinct-gamma SET is the
// union over canonical subsets of the full cyclic orbit {gamma * h^{(b-a)*t} : t in 0..n}.
// This reproduces the exact I(a,b;s) at ~n x speedup. Verified against the lex engine (pg).
//
// Modes:
//   pgneck n k a b              -> single-dir I(a,b;s) decay curve over s
//   pgneck n k curveb <bmax>    -> full max-over-(a in [k,n), b in [k,min(s,bmax+1))) curve over s
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
fn big_prime(n:u64)->u64{let mut p=n*n*n*n;loop{if p%n==1&&is_prime(p){return p;}p+=1;}}

#[inline]
fn ddk_idx(vals:&[u64],idx:&[usize],k:usize,p:u64,invd:&[u64],n:usize)->u64{
    let mut vs:[u64;64]=[0u64;64];
    for t in 0..=k{vs[t]=vals[t];}
    for j in 1..=k{for i in (j..=k).rev(){let inv=invd[idx[i]*n+idx[i-j]];vs[i]=mulmod(submod(vs[i],vs[i-1],p),inv,p);}}
    vs[k]
}
#[inline]
fn in_rs_idx(vals:&[u64],idx:&[usize],k:usize,p:u64,invd:&[u64],n:usize)->bool{
    let s=idx.len();
    if s<=k{return true;}
    for st in 0..(s-k){if ddk_idx(&vals[st..st+k+1],&idx[st..st+k+1],k,p,invd,n)!=0{return false;}}
    true
}

// is the sorted subset `comb` (containing 0) the canonical (lexicographically-smallest) rotation?
// Rotations: subtract c from each element mod n, for each c in comb, re-sort, compare.
#[inline]
fn is_canonical(comb:&[usize],n:usize)->bool{
    let s=comb.len();
    let mut rot:[usize;64]=[0;64];
    for &c in comb.iter(){
        for j in 0..s{rot[j]=(comb[j]+n-c)%n;}
        rot[..s].sort_unstable();
        // compare rot[..s] < comb lexicographically
        for j in 0..s{
            if rot[j]<comb[j]{return false;}
            if rot[j]>comb[j]{break;}
        }
    }
    true
}

// Necklace incidence for direction (a,b), witness size s. Enumerates canonical s-subsets
// containing index 0; for each, finds gamma; adds the full cyclic orbit gamma*h^{(b-a)t}.
fn incidence_neck(n:usize,mua:&[u64],mub:&[u64],k:usize,p:u64,s:usize,invd:&[u64],fac:u64)->u64{
    if s<=k {return u64::MAX;} // underdetermined here irrelevant
    let mut local:HashSet<u64>=HashSet::new();
    // enumerate (s-1)-subsets of {1..n-1}; prepend 0.
    let mut rest:Vec<usize>=(1..s).collect(); // [1,2,...,s-1]
    let mut comb=vec![0usize;s];
    let mut u0=vec![0u64;s];let mut u1=vec![0u64;s];let mut full=vec![0u64;s];
    let mut heavy=false;
    loop{
        comb[0]=0;
        for j in 0..s-1{comb[j+1]=rest[j];}
        if is_canonical(&comb,n){
            for (j,&idx) in comb.iter().enumerate(){u0[j]=mua[idx];u1[j]=mub[idx];}
            if in_rs_idx(&u1,&comb,k,p,invd,n){
                if in_rs_idx(&u0,&comb,k,p,invd,n){heavy=true;}
            } else {
                let a0=ddk_idx(&u0,&comb,k,p,invd,n);
                let a1=ddk_idx(&u1,&comb,k,p,invd,n);
                if a1!=0{
                    let gm=mulmod(submod(0,a0,p),invmod(a1,p),p);
                    for i in 0..s{full[i]=addmod(u0[i],mulmod(gm,u1[i],p),p);}
                    if in_rs_idx(&full,&comb,k,p,invd,n){
                        // add full cyclic orbit of gm
                        let mut x=gm;
                        for _ in 0..n{local.insert(x);x=mulmod(x,fac,p);}
                    }
                }
            }
        }
        // next (s-1)-combination of [1,n) in lex order
        let mut i=s-1;let mut advanced=false;
        while i>0{i-=1;if rest[i]!=i+1+n-s{rest[i]+=1;for j in (i+1)..s-1{rest[j]=rest[j-1]+1;}advanced=true;break;}}
        if !advanced{break;}
    }
    if heavy{return u64::MAX;}
    local.len() as u64
}

fn main(){
    let args:Vec<String>=std::env::args().collect();
    let n:usize=args[1].parse().unwrap();
    let k:usize=args[2].parse().unwrap();
    let p=big_prime(n as u64);
    let g=proot(p);
    let h=powmod(g,(p-1)/n as u64,p);
    let mu:Vec<u64>=(0..n).map(|i|powmod(h,i as u64,p)).collect();
    let mut invd=vec![0u64;n*n];
    for a in 0..n{for b in 0..n{if a!=b{invd[a*n+b]=invmod(submod(mu[a],mu[b],p),p);}}}
    let budget=n as u64;
    // single dir mode: "n k a b"
    let single:Option<(u64,u64)>=match(args.get(3).and_then(|s|s.parse::<u64>().ok()),args.get(4).and_then(|s|s.parse::<u64>().ok())){
        (Some(a),Some(b))=>Some((a,b)),_=>None};
    if let Some((a,b))=single{
        let mua:Vec<u64>=(0..n).map(|i|powmod(mu[i],a,p)).collect();
        let mub:Vec<u64>=(0..n).map(|i|powmod(mu[i],b,p)).collect();
        let fac=powmod(h,((b+n as u64-a)%n as u64) as u64,p); // h^{b-a}
        println!("NECK single (a={},b={}) n={} k={} p={}:",a,b,n,k,p);
        for s in (k+2)..(n-1){
            let inc=incidence_neck(n,&mua,&mub,k,p,s,&invd,fac);
            let isz=if inc==u64::MAX{"HEAVY".into()}else{inc.to_string()};
            println!("  s={} (s-k={}): I={}",s,s-k,isz);
        }
        return;
    }
    // full curve mode: "n k curveb <smax>"
    let curveb = args.get(3).map(|a|a=="curveb").unwrap_or(false);
    let smax:usize = args.get(4).and_then(|s|s.parse().ok()).unwrap_or(n/2+1);
    println!("NECK n={} k={} p={} budget={} : max-over-far-dir I(s) curve",n,k,p,budget);
    let mut sstar=0usize;
    for s in (k+2)..=smax {
        let dirs:Vec<(u64,u64)>=((k as u64)..(s as u64)).flat_map(|b|((k as u64)..(n as u64)).filter(move|&a|a!=b).map(move|a|(a,b))).collect();
        let (mx,arg)=dirs.par_iter().map(|&(a,b)|{
            let mua:Vec<u64>=(0..n).map(|i|powmod(mu[i],a,p)).collect();
            let mub:Vec<u64>=(0..n).map(|i|powmod(mu[i],b,p)).collect();
            let fac=powmod(h,((b+n as u64-a)%n as u64) as u64,p);
            let inc=incidence_neck(n,&mua,&mub,k,p,s,&invd,fac);
            if inc==u64::MAX{(0u64,(a,b))}else{(inc,(a,b))}
        }).reduce(||(0u64,(0u64,0u64)),|x,y|if y.0>x.0{y}else{x});
        let good=mx<=budget;
        println!("  s={} (s-k={}): maxI={} at {:?}  {}",s,s-k,mx,arg,if good{"GOOD"}else{"bad"});
        if good&&sstar==0{sstar=s;}
        if sstar>0 && s>=sstar+1 {break;}
    }
    if sstar>0{
        let ds=(n-sstar)as f64/n as f64;
        let rho=k as f64/n as f64;
        println!("  => s*={}, m*=s*-k={}, delta*={:.4}  [Johnson {:.4}, cap {:.4}]",sstar,sstar-k,ds,1.0-rho.sqrt(),1.0-rho);
    }
}
