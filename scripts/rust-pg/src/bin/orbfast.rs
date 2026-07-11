// orbfast — ANGLE B growth-law DECIDER. Fast dilation-orbit-accelerated worst-direction
// far-line incidence at the over-det binding, pushing to n=32,64 to measure m*(level).
//
// Far pencil gamma -> x^a + gamma*x^b on mu_n vs RS[k].  Bad-gamma set is a union of orbits
// of gamma -> gamma*h^{b-a}; AND the bad witness-SUBSETS R come in cyclic-shift orbits of size n
// (shifting R by +1 multiplies gamma_R by h^{b-a}). So:
//   D(a,b;s) = (n/gcd(b-a,n)) * O  + z,   O = #distinct nonzero gamma-orbits.
// We enumerate only subsets R that CONTAIN index 0 (factor ~n/s reduction vs all C(n,s); every
// shift-orbit has >=1 such rep; we then dedup the resulting gammas into their h^{b-a}-orbits so
// no double counting). This is exact for D.
//
// We restrict the direction scan to a chosen gcd class (default: scan ALL b in [k,n), a in [0,n))
// OR a fixed (a,b) via "dir a b". Reports per-s the worst D and m=s-k; locates s* (first D<=n)
// => m* = s*-k.  Usage:
//   orbfast <n> <k> <s_lo> <s_hi> [mult] [gcdfilter]   (gcdfilter: only dirs with gcd(b-a,n)==g)
//   orbfast <n> <k> <s_lo> <s_hi> [mult] dir <a> <b>     (single direction)
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
    let mut vs:[u64;80]=[0u64;80];
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

// For one direction (a,b): enumerate subsets R of [0,n) of size s WITH 0 in R; for each,
// derive the (at most one) bad gamma; collect into a set; then count gammas grouped by the
// gamma -> gamma*fac orbit (fac = h^{b-a}). Returns (D = total distinct bad gamma over the WHOLE
// shift family, O = #nonzero orbits, z, heavy).
fn dir_decompose(n:usize,a:usize,b:usize,k:usize,p:u64,s:usize,invd:&[u64],powtab:&[u64],h:u64)->(u64,u64,u64,bool){
    let ev0=&powtab[a*n..a*n+n];
    let ev1=&powtab[b*n..b*n+n];
    // far test: ev1 must not lie on deg<k poly over all mu
    let idx_full:Vec<usize>=(0..n).collect();
    if in_rs_idx(ev1,&idx_full,k,p,invd,n){return (0,0,0,false);}
    let fac=powmod(h,((b as i64 - a as i64).rem_euclid(n as i64)) as u64,p);
    // enumerate s-subsets of {0..n-1} containing 0: choose s-1 from {1..n-1}
    let rest:Vec<usize>=(1..n).collect();
    let m=rest.len();
    // collect gammas in parallel by splitting on first chosen element
    let gammas:HashSet<u64> = (0..=(m-(s-1))).into_par_iter().map(|first|{
        let mut local:HashSet<u64>=HashSet::new();
        // first chosen index in rest is `first`; choose remaining s-2 from rest[first+1..]
        let mut comb:Vec<usize>=Vec::with_capacity(s);
        comb.push(0usize); // index 0 always
        // we will fill comb[1..] = rest[c0], rest[c1], ... with c0=first
        let need=s-1;
        let mut sel=vec![0usize;need];
        sel[0]=first;
        for j in 1..need { sel[j]=first+j; }
        if sel[need-1] >= m { return local; }
        let mut u0=vec![0u64;s];let mut u1=vec![0u64;s];let mut full=vec![0u64;s];
        loop{
            // build comb
            comb.truncate(1);
            for &si in &sel { comb.push(rest[si]); }
            for (j,&idx) in comb.iter().enumerate(){u0[j]=ev0[idx];u1[j]=ev1[idx];}
            if in_rs_idx(&u1,&comb,k,p,invd,n){
                if in_rs_idx(&u0,&comb,k,p,invd,n){ /* heavy: mark via sentinel */ local.insert(u64::MAX); }
            } else {
                let a0=ddk_idx(&u0,&comb,k,p,invd,n);let a1=ddk_idx(&u1,&comb,k,p,invd,n);
                if a1!=0{let gm=mulmod(submod(0,a0,p),invmod(a1,p),p);
                    for i in 0..s{full[i]=addmod(u0[i],mulmod(gm,u1[i],p),p);}
                    if in_rs_idx(&full,&comb,k,p,invd,n){local.insert(gm);}}
            }
            // advance sel within rest[first.. ] keeping sel[0]==first fixed
            let mut i=need;let mut adv=false;
            while i>1{i-=1; let maxv=m-(need-i); if sel[i]<maxv{sel[i]+=1;for j in (i+1)..need{sel[j]=sel[j-1]+1;} adv=true;break;}}
            if !adv{break;}
        }
        local
    }).reduce(HashSet::new,|mut x,y|{x.extend(y);x});
    if gammas.contains(&u64::MAX){return (u64::MAX,u64::MAX,0,true);}
    // now: the gammas we collected are bad gammas. But the FULL bad set is the union of their
    // fac-orbits (since we only enumerated R containing 0, we caught >=1 rep per shift-orbit; the
    // full shift-orbit gives the whole fac-orbit of gamma). So expand to full orbits then count.
    let mut full:HashSet<u64>=HashSet::new();
    for &g0 in &gammas {
        let mut x=g0;
        for _ in 0..n { full.insert(x); x=mulmod(x,fac,p); if x==g0 {break;} }
    }
    let z = if full.contains(&0){1u64}else{0u64};
    let nonzero:HashSet<u64>=full.iter().cloned().filter(|&x|x!=0).collect();
    // count orbits
    let mut visited:HashSet<u64>=HashSet::new();
    let mut o=0u64;
    let mut elems:Vec<u64>=nonzero.iter().cloned().collect(); elems.sort();
    for &g in &elems {
        if visited.contains(&g){continue;}
        let mut x=g;
        loop{ if !nonzero.contains(&x)||visited.contains(&x){break;} visited.insert(x); x=mulmod(x,fac,p); if x==g{break;} }
        o+=1;
    }
    (full.len() as u64, o, z, false)
}

fn main(){
    let args:Vec<String>=std::env::args().collect();
    let n:usize=args[1].parse().unwrap();
    let k:usize=args[2].parse().unwrap();
    let s_lo:usize=args[3].parse().unwrap();
    let s_hi:usize=args[4].parse().unwrap();
    let mult:u32=args.get(5).and_then(|a|a.parse().ok()).unwrap_or(4);
    let single:Option<(usize,usize)> = if args.get(6).map(|x|x=="dir").unwrap_or(false){
        Some((args[7].parse().unwrap(), args[8].parse().unwrap()))
    } else { None };
    let gcdfilter:Option<u64> = if single.is_none() { args.get(6).and_then(|a|a.parse().ok()) } else { None };
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
    println!("# orbfast n={} k={} rho={:.4} p={} budget={} Johnson={:.4} mult={} {}",
        n,k,rho,p,budget,john,mult, match (single,gcdfilter){(Some((a,b)),_)=>format!("dir=({},{})",a,b),(_,Some(g))=>format!("gcdfilter={}",g),_=>"ALLDIRS".to_string()});
    let mut binding:Option<usize>=None;
    for s in s_lo..=s_hi {
        let dirs:Vec<(usize,usize)> = match single {
            Some((a,b))=>vec![(a,b)],
            None=>{
                (0..n).flat_map(|a|(k..n).filter(move|&b|b!=a).map(move|b|(a,b)))
                    .filter(|&(a,b)|{
                        match gcdfilter{ Some(gf)=>gcd(((b as i64-a as i64).rem_euclid(n as i64))as u64,n as u64)==gf, None=>true }
                    }).collect()
            }
        };
        // sequentially over dirs but each dir is internally parallel
        let mut best=(0u64,0usize,0usize,0u64,0u64);
        for &(a,b) in &dirs {
            let (d,o,z,heavy)=dir_decompose(n,a,b,k,p,s,&invd,&powtab,h);
            if heavy {continue;}
            if d>best.0 { best=(d,a,b,o,z); }
        }
        let (d,a,b,o,z)=best;
        let dd=gcd(((b as i64-a as i64).rem_euclid(n as i64))as u64,n as u64);
        let ssz=if dd>0 {(n as u64)/dd} else {0};
        let good=d<=budget;
        println!("  s={:>2} m={:>2} | D={:>7} dir=({:>2},{:>2}) d={:>2} S={:>3} O={:>5} z={} | {}",
            s, s as i64-k as i64, d, a, b, dd, ssz, o, z, if good{"GOOD"}else{"bad"});
        if good && binding.is_none(){ binding=Some(s); }
    }
    if let Some(ss)=binding {
        println!("# => s*={} m*={}  delta*=1-(s*-1)/n={:.4}  [n/4={}, log2(n)={:.1}]",
            ss, ss as i64-k as i64, 1.0-(ss as f64-1.0)/(n as f64), n/4, (n as f64).log2());
    } else {
        println!("# => no binding in [{}, {}] (still bad at s_hi)", s_lo, s_hi);
    }
}
