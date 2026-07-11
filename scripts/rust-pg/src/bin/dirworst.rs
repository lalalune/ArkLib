// dirworst — is the MONOMIAL far direction the WORST far direction? (#444 growth-law squeeze)
//
// Far-line incidence: line gamma -> u0 + gamma*u1 against RS[k] on mu_n.
// incidence(u0,u1;s) = #{distinct gamma in F_p : u0 + gamma*u1 agrees with a deg<k poly on >= s pts}.
// The "far direction" is u1. The in-tree claim is "monomial far-line IS the worst-case stack".
// We test it: at the over-determined binding edge s = k+2 (where I is ~n^3, decays to budget=n),
// compute max-incidence over
//   (A) MONOMIAL far directions  u1 = x^b           (b in [k,n))
//   (B) BINOMIAL  far directions u1 = x^b1 + x^b2   (b1<b2 in [k,n))
//   (C) TRINOMIAL far directions u1 = x^b1+x^b2+x^b3
//   (D) RANDOM    far words      u1 = random combo of x^j (j in [k,n)), random coeffs
// For each candidate u1, the base u0 is swept over monomials x^a (a in [k,n), a not a u1-exponent)
// — and additionally we let coeffs of u1 vary (the line direction is projective, but coeff RATIOS
// inside a multi-term u1 matter). Reports the max incidence per class and which class wins.
//
// Usage: dirworst <n> <k> <s>            (single witness size s; s=k+2 is the edge)
//        dirworst <n> <k> <s> <mult>     (prime ~ n^mult, default 4)
// Cost ~ C(n,s) * (#u0) * (#u1 candidates). At s=k+2 and small n this is feasible.
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

// k-th divided difference of vals over node-INDICES idx, precomputed inv-diff table.
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

// incidence for arbitrary evaluation vectors ev0 (=u0 on mu) and ev1 (=u1 on mu).
// Returns count of distinct gamma, or u64::MAX if some witness is "heavy" (both u0,u1 in RS) = saturated.
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
    let s:usize=args[3].parse().unwrap();
    let mult:u32=args.get(4).and_then(|a|a.parse().ok()).unwrap_or(4);
    let p=big_prime(n as u64,mult);
    let g=proot(p);let h=powmod(g,(p-1)/n as u64,p);
    let mu:Vec<u64>=(0..n).map(|i|powmod(h,i as u64,p)).collect();
    let mut invd=vec![0u64;n*n];
    for a in 0..n{for b in 0..n{if a!=b{invd[a*n+b]=invmod(submod(mu[a],mu[b],p),p);}}}
    // powtab[e*n+i] = mu_i^e  for e in [0,n)
    let mut powtab=vec![0u64;n*n];
    for e in 0..n{for i in 0..n{powtab[e*n+i]=powmod(mu[i],e as u64,p);}}
    let budget=n as u64;
    let rho=k as f64/n as f64;
    let john=1.0-rho.sqrt();
    eprintln!("# n={} k={} s={} (s-k={}) rho={:.4} p={} budget={} Johnson={:.4}",n,k,s,s-k,rho,p,budget,john);

    // helper: evaluate word (exp,coeff) list on mu mod p
    let ev_of=|word:&[(u64,u64)]|->Vec<u64>{
        let mut ev=vec![0u64;n];
        for &(e,c) in word{ for i in 0..n{ ev[i]=addmod(ev[i],mulmod(c%p,powtab[(e as usize)*n+i],p),p); } }
        ev
    };

    // base u0 candidates: monomials x^a, a in [k,n)  (far base; classic worst base is high exponent)
    let bases:Vec<u64>=((k as u64)..(n as u64)).collect();

    // (A) MONOMIAL far directions u1 = x^b, b in [k,n)
    let mono:Vec<Vec<(u64,u64)>> = ((k as u64)..(n as u64)).map(|b|vec![(b,1u64)]).collect();
    // (B) BINOMIAL far directions u1 = x^b1 + c*x^b2, c in {1, small}, b1<b2 in [k,n)
    let mut bino:Vec<Vec<(u64,u64)>>=vec![];
    for b1 in (k as u64)..(n as u64){ for b2 in (b1+1)..(n as u64){
        for &c in &[1u64,2u64, p-1 /*=-1*/]{ bino.push(vec![(b1,1),(b2,c)]); }
    }}
    // (C) TRINOMIAL far directions u1 = x^b1 + x^b2 + x^b3, distinct in [k,n)
    let mut trino:Vec<Vec<(u64,u64)>>=vec![];
    for b1 in (k as u64)..(n as u64){ for b2 in (b1+1)..(n as u64){ for b3 in (b2+1)..(n as u64){
        trino.push(vec![(b1,1),(b2,1),(b3,1)]);
        trino.push(vec![(b1,1),(b2,p-1),(b3,1)]);
    }}}
    // (D) RANDOM far words: random subset of exps in [k,n), random nonzero coeffs (LCG, deterministic)
    let mut rng:u64=0x9e3779b97f4a7c15 ^ (n as u64)<<8 ^ (k as u64);
    let mut next=||{rng^=rng<<13;rng^=rng>>7;rng^=rng<<17;rng};
    let mut randw:Vec<Vec<(u64,u64)>>=vec![];
    let nexp=(n-k) as u64;
    for _ in 0..400 {
        // random nonempty subset of [k,n)
        let mut w:Vec<(u64,u64)>=vec![];
        for e in (k as u64)..(n as u64){ if next()&1==1 { let c=1+ next()%(p-1); w.push((e,c)); } }
        if w.is_empty(){ w.push((k as u64 + next()%nexp, 1)); }
        randw.push(w);
    }

    // compute max incidence over a class: for each u1, max over monomial bases u0 (a not in supp u1).
    let run=|class:&[Vec<(u64,u64)>], label:&str|->(u64, Vec<(u64,u64)>, u64){
        let res = class.par_iter().map(|word|{
            let supp:HashSet<u64>=word.iter().map(|&(e,_)|e).collect();
            let ev1=ev_of(word);
            // skip if u1 happens to be in RS[k] (low effective degree) — must be far
            // (we check via: is ev1 a deg<k poly on all of mu? if so it's not far) — cheap full check on k+1 windows of [0..n)
            // quick far test: ev1 must not lie on a deg<k poly over the FULL mu (use first n indices)
            let idx_full:Vec<usize>=(0..n).collect();
            if in_rs_idx(&ev1,&idx_full,k,p,&invd,n){ return (0u64,(0u64,0u64),word.clone()); }
            let mut best=0u64; let mut ba=(0u64,0u64);
            for &a in &bases{
                if supp.contains(&a){ continue; }
                let ev0=ev_of(&[(a,1u64)]);
                let inc=incidence_ev(n,&ev0,&ev1,k,p,s,&invd);
                let v= if inc==u64::MAX {0} else {inc};
                if v>best{ best=v; ba=(a, word[0].0); }
            }
            (best, ba, word.clone())
        }).reduce(||(0u64,(0u64,0u64),vec![]),|x,y| if y.0>x.0 {y} else {x});
        let _=label;
        (res.0, res.2, (res.1).0)
    };

    let (ma,wa,ba)=run(&mono,"mono");
    println!("A MONOMIAL  : maxI={:>6}  u1={:?}  bestBase=x^{}", ma, wa, ba);
    let (mb,wb,bb)=run(&bino,"bino");
    println!("B BINOMIAL  : maxI={:>6}  u1={:?}  bestBase=x^{}", mb, wb, bb);
    let (mc,wc,bc)=run(&trino,"trino");
    println!("C TRINOMIAL : maxI={:>6}  u1={:?}  bestBase=x^{}", mc, wc, bc);
    let (md,wd,bd)=run(&randw,"rand");
    println!("D RANDOM    : maxI={:>6}  u1={:?}  bestBase=x^{}", md, wd, bd);

    let overall=ma.max(mb).max(mc).max(md);
    let verdict = if ma>=mb && ma>=mc && ma>=md {"MONOMIAL IS WORST (>= all)"}
                  else {"NON-MONOMIAL EXCEEDS MONOMIAL"};
    println!("=> n={} k={} s={}: monoMax={} binoMax={} trinoMax={} randMax={} overall={} budget={} ==> {}",
        n,k,s,ma,mb,mc,md,overall,budget,verdict);
}
