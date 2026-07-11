// orbcount — ANGLE B: decompose over-det MONOMIAL far-line incidence  D = z + S*O.
//
// Far pencil  gamma -> x^a + gamma*x^b  on mu_n  against RS[k].
// D(a,b;s) = #{distinct bad gamma}.  Action-Orbit (2026/861): bad-gamma set is a union of
// orbits of  gamma -> gamma * h^{b-a}  (h = generator of mu_n).  Orbit size of any nonzero
// gamma is  S = n / gcd(b-a, n).  Fixed point gamma=0 (z in {0,1}).  So  D = z + S * O,
// O = #nonzero orbits.  Crossing law:  D <= budget(=n)  <=>  O <= gcd(b-a,n) = d   (off z).
//
// This binary reports, per s, the WORST monomial direction's full decomposition
//   D, binder (a,b), d=gcd(b-a,n), S=n/d, z, O=(D-z)/S, and the checks O<=d, D<=n.
// It locates the BINDING radius s* (first s with D<=n) and prints O at s* and s*-1.
//
// Usage: orbcount <n> <k> [s_lo] [s_hi] [mult]
use rayon::prelude::*;
use std::collections::HashSet;

#[inline] fn mulmod(a:u64,b:u64,p:u64)->u64{((a as u128*b as u128)%p as u128)as u64}
#[inline] fn addmod(a:u64,b:u64,p:u64)->u64{let s=a+b;if s>=p{s-p}else{s}}
#[inline] fn submod(a:u64,b:u64,p:u64)->u64{if a>=b{a-b}else{p-b+a}}
fn powmod(mut b:u64,mut e:u64,p:u64)->u64{let mut r=1u64;b%=p;while e>0{if e&1==1{r=mulmod(r,b,p);}b=mulmod(b,b,p);e>>=1;}r}
#[inline] fn invmod(a:u64,p:u64)->u64{powmod(a,p-2,p)}
fn gcd(a:u64,b:u64)->u64{if b==0{a}else{gcd(b,a%b)}}
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

// distinct bad gammas for monomial pencil ev0=x^a, ev1=x^b  at witness size s.
// returns u64::MAX (heavy) if some witness has both u0,u1 in RS.
fn gammas(n:usize,ev0:&[u64],ev1:&[u64],k:usize,p:u64,s:usize,invd:&[u64])->Option<HashSet<u64>>{
    let mut local:HashSet<u64>=HashSet::new();
    let mut comb:Vec<usize>=(0..s).collect();
    let mut u0=vec![0u64;s];let mut u1=vec![0u64;s];let mut full=vec![0u64;s];
    loop{
        for (j,&idx) in comb.iter().enumerate(){u0[j]=ev0[idx];u1[j]=ev1[idx];}
        if in_rs_idx(&u1,&comb,k,p,invd,n){
            if in_rs_idx(&u0,&comb,k,p,invd,n){return None;}
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
    Some(local)
}

fn main(){
    let args:Vec<String>=std::env::args().collect();
    let n:usize=args[1].parse().unwrap();
    let k:usize=args.get(2).and_then(|a|a.parse().ok()).unwrap_or(n/4);
    let s_lo:usize=args.get(3).and_then(|a|a.parse().ok()).unwrap_or(k+1);
    let s_hi:usize=args.get(4).and_then(|a|a.parse().ok()).unwrap_or(n-k+1);
    let mult:u32=args.get(5).and_then(|a|a.parse().ok()).unwrap_or(4);
    let p=big_prime(n as u64,mult);
    let g=proot(p);let h=powmod(g,(p-1)/n as u64,p);
    let mu:Vec<u64>=(0..n).map(|i|powmod(h,i as u64,p)).collect();
    let mut invd=vec![0u64;n*n];
    for a in 0..n{for b in 0..n{if a!=b{invd[a*n+b]=invmod(submod(mu[a],mu[b],p),p);}}}
    let mut powtab=vec![0u64;n*n];
    for e in 0..n{for i in 0..n{powtab[e*n+i]=powmod(mu[i],e as u64,p);}}
    let budget=n as u64;
    let rho=k as f64/n as f64;
    let john=1.0-rho.sqrt();
    println!("# n={} k={} rho={:.4} p={} budget(=n)={} Johnson={:.4} n/4={}",n,k,rho,p,budget,john,n/4);
    println!("#  s   m |      D    binder   d    S |  z     O | D=z+S*O | O<=d | GOOD(D<=n) | delta*=1-s/n  (CORRECTED off-by-one)");

    // directions: monomial pencil (a,b), b in [k,n) (far), a in [0,n) a!=b, a!=exponents.
    // We sweep ALL (a,b) and report the worst (max D) per s.
    let mut binding_s: Option<usize>=None;
    let mut last = String::new();
    for s in s_lo..=s_hi {
        // parallel over (a,b)
        let cands:Vec<(usize,usize)>=(0..n).flat_map(|a|((k)..n).filter(move |&b|b!=a).map(move |b|(a,b))).collect();
        // We seek the worst GENUINE far pencil: exclude HEAVY (saturated) directions, which are
        // degenerate near-pairs (both monomials in RS on a common support) — not over-det far lines.
        let best = cands.par_iter().filter_map(|&(a,b)|{
            let ev0=&powtab[a*n..a*n+n];
            let ev1=&powtab[b*n..b*n+n];
            match gammas(n,ev0,ev1,k,p,s,&invd){
                None=>None, // heavy => saturated; skip (degenerate, not a far pencil)
                Some(set)=>{
                    let z = if set.contains(&0){1u64}else{0u64};
                    Some((set.len() as u64, a, b, z))
                }
            }
        }).max_by_key(|t|t.0).unwrap_or((0,0,0,0));
        let (d_count, a, b, z) = best;
        let dd = gcd(((b as i64 - a as i64).rem_euclid(n as i64)) as u64, n as u64);
        let ssz = (n as u64)/dd;
        let (o_str, recon_ok, odle, good);
        if d_count==u64::MAX {
            o_str="HEAVY".to_string(); recon_ok="-".to_string(); odle="-".to_string(); good=false;
        } else {
            // O = (D - z)/S
            let num = d_count - z;
            let o = if ssz>0 && num % ssz==0 { num/ssz } else { u64::MAX };
            o_str = if o==u64::MAX {format!("BAD({})",num)} else {format!("{}",o)};
            recon_ok = if o!=u64::MAX && z + ssz*o == d_count {"yes".to_string()} else {"NO".to_string()};
            odle = if o!=u64::MAX {format!("{}", o<=dd)} else {"-".to_string()};
            good = d_count<=budget;
        }
        let dstar = 1.0 - (s as f64 - 1.0)/(n as f64);
        let dcol = if d_count==u64::MAX {"HEAVY".to_string()} else {format!("{}",d_count)};
        let line=format!("  {:>2} {:>3} | {:>6} ({:>2},{:>2}) {:>3} {:>4} | {:>2} {:>5} | {:>6} | {:>4} | {:>9} | {:.4}",
            s, s as i64 - k as i64, dcol, a, b, dd, ssz, z, o_str, recon_ok, odle, if good{"GOOD"}else{"bad"}, dstar);
        println!("{}", line);
        if good && binding_s.is_none() { binding_s=Some(s); }
        if good && binding_s==Some(s) { last=line.clone(); }
    }
    if let Some(ss)=binding_s {
        println!("# BINDING s*={} m*={} (n/4={}, n/4-1={})", ss, ss as i64-k as i64, n/4, n/4-1);
        println!("# delta* (over-det monomial) = 1-(s*-1)/n = {:.4}; Johnson = {:.4}", 1.0-(ss as f64-1.0)/(n as f64), john);
        let _=last;
    }
}
