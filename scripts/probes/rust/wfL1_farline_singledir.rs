// wf-L1 (#444): INDEPENDENT fresh engine — exact far-line incidence I(a,b;size) for a SINGLE
// direction over mu_n in F_p, computed by Newton divided-difference RS-membership (a DIFFERENT
// algorithm from deltastar_farline.rs's left-null Gaussian elimination, and from OT2's cyclotomic
// norm method). Used to settle OT2-vs-wfLC at n=32 k=8 by checking whether the incidence at the
// binding agreement size (15 = 2k-1) and at the under-determined boundary (k+1) is p-INDEPENDENT.
//
// usage: wfL1_farline_singledir <n> <k> <a> <b> <size> <prime_lo> [nthreads]
//   size = agreement-set size (= n - r).  Reports (count, n_heavy).  count=p means saturated.
//
// MEMBERSHIP TEST (independent of left-null): a value vector v on points X[0..size] lies in
// RS[X,k] = {deg<k polys} iff ALL k-th order Newton divided differences vanish, i.e. the (size-k)
// successive (k)-th divided differences are 0. The line x^a + g x^b is in RS iff DD_k(u0)+g DD_k(u1)=0
// componentwise; pick first nonzero DD_k(u1) coord to solve g, then verify all coords.

use std::collections::HashSet;
use std::sync::{Arc, Mutex};
use std::thread;

#[inline] fn mmul(a:u64,b:u64,p:u64)->u64{ ((a as u128 * b as u128) % p as u128) as u64 }
#[inline] fn madd(a:u64,b:u64,p:u64)->u64{ let s=a+b; if s>=p {s-p} else {s} }
#[inline] fn msub(a:u64,b:u64,p:u64)->u64{ if a>=b {a-b} else {a+p-b} }
fn mpow(mut a:u64, mut e:u64, p:u64)->u64{ let mut r=1u64; a%=p; while e>0 { if e&1==1 {r=mmul(r,a,p);} a=mmul(a,a,p); e>>=1; } r }
fn minv(a:u64,p:u64)->u64{ mpow(a,p-2,p) }
fn is_prime(n:u64)->bool{ if n<2 {return false;} let mut d=2u64; while d*d<=n { if n%d==0 {return false;} d+=1; } true }
fn find_prime_cong1(n:u64, lo:u64)->u64{ let mut p = lo + ((1 + n - lo % n) % n); if p<=2 {p+=n;} loop { if p>2 && p%n==1 && is_prime(p) { return p; } p+=n; } }
fn primitive_root(p:u64)->u64{
    let mut m=p-1; let mut fs=vec![]; let mut d=2u64;
    while d*d<=m { if m%d==0 { fs.push(d); while m%d==0 {m/=d;} } d+=1; }
    if m>1 {fs.push(m);}
    let mut g=2u64;
    loop { if fs.iter().all(|&f| mpow(g,(p-1)/f,p)!=1) { return g; } g+=1; }
}
fn mu_n(n:u64,p:u64)->Vec<u64>{
    let g=primitive_root(p); let h=mpow(g,(p-1)/n,p);
    let mut s:Vec<u64>=(0..n).map(|j| mpow(h,j,p)).collect();
    s.sort(); s.dedup(); s
}

// Newton k-th divided differences of value-vector `vals` on points `pts` (both len = size).
// Returns the (size-k) successive top divided differences (the RS[k]-membership residual).
fn dd_residual(vals:&[u64], pts:&[u64], k:usize, p:u64)->Vec<u64>{
    let size=vals.len();
    // table[j] = divided differences; iteratively build columns up to order k.
    let mut col:Vec<u64>=vals.to_vec();
    // order m: col[i] becomes [pts[i..i+m]] divided diff, for i in 0..size-m
    for m in 1..=k {
        let mut nxt=vec![0u64; size-m];
        for i in 0..size-m {
            let denom = msub(pts[i+m], pts[i], p);
            let num = msub(col[i+1], col[i], p);
            nxt[i]=mmul(num, minv(denom,p), p);
        }
        col=nxt;
    }
    // col now has length size-k: these are the k-th divided diffs; membership <=> all zero.
    col
}

// incidence for one direction (a,b) at agreement size `size`: (count, heavy_sets)
fn incidence_dir(s:&[u64], p:u64, k:usize, a:u64, b:u64, size:usize, nthreads:usize)->(u64,u64){
    let n=s.len();
    if size<=k { return (p,0); }
    let pa_:Vec<u64>=s.iter().map(|&x| mpow(x,a,p)).collect();
    let pb_:Vec<u64>=s.iter().map(|&x| mpow(x,b,p)).collect();
    let s=Arc::new(s.to_vec()); let pa_=Arc::new(pa_); let pb_=Arc::new(pb_);
    let good=Arc::new(Mutex::new(HashSet::<u64>::new()));
    let heavy=Arc::new(Mutex::new(0u64));
    let sat=Arc::new(Mutex::new(false));
    // partition the combination space by the first chosen index
    let first_choices:Vec<usize>=(0..=(n-size)).collect();
    let next=Arc::new(Mutex::new(0usize));
    let fc=Arc::new(first_choices);
    let mut handles=vec![];
    for _ in 0..nthreads {
        let s=Arc::clone(&s); let pa_=Arc::clone(&pa_); let pb_=Arc::clone(&pb_);
        let good=Arc::clone(&good); let heavy=Arc::clone(&heavy); let sat=Arc::clone(&sat);
        let next=Arc::clone(&next); let fc=Arc::clone(&fc);
        handles.push(thread::spawn(move||{
            let mut local_good:HashSet<u64>=HashSet::new();
            let mut local_heavy=0u64;
            loop{
                if *sat.lock().unwrap() { break; }
                let ji={ let mut g=next.lock().unwrap(); let j=*g; *g+=1; j };
                if ji>=fc.len() { break; }
                let f0=fc[ji];
                // enumerate subsets whose smallest index is f0, of total size `size`
                // choose remaining size-1 indices from (f0+1 .. n)
                let rem=size-1;
                let mut idx:Vec<usize>=(0..rem).map(|t| f0+1+t).collect();
                if f0+rem >= n { // not enough room
                    continue;
                }
                let pts0=s[f0];
                loop {
                    // build pts and value vectors
                    let mut pts=Vec::with_capacity(size); pts.push(pts0);
                    for &ii in &idx { pts.push(s[ii]); }
                    let mut u0=Vec::with_capacity(size); u0.push(pa_[f0]);
                    for &ii in &idx { u0.push(pa_[ii]); }
                    let mut u1=Vec::with_capacity(size); u1.push(pb_[f0]);
                    for &ii in &idx { u1.push(pb_[ii]); }
                    let r0=dd_residual(&u0,&pts,k,p);
                    let r1=dd_residual(&u1,&pts,k,p);
                    let any_b = r1.iter().any(|&x| x%p!=0);
                    if !any_b {
                        if r0.iter().all(|&x| x%p==0) { local_heavy+=1; *sat.lock().unwrap()=true; }
                    } else {
                        let i=r1.iter().position(|&x| x%p!=0).unwrap();
                        let g=mmul(msub(0,r0[i],p), minv(r1[i],p), p);
                        if (0..r1.len()).all(|t| madd(r0[t], mmul(g,r1[t],p), p)%p==0) {
                            local_good.insert(g);
                        }
                    }
                    // next combination of idx within (f0+1..n)
                    let mut i=rem as isize -1;
                    while i>=0 && idx[i as usize]==n-rem+i as usize { i-=1; }
                    if i<0 { break; }
                    idx[i as usize]+=1;
                    for j in (i as usize+1)..rem { idx[j]=idx[j-1]+1; }
                }
            }
            { let mut g=good.lock().unwrap(); for v in local_good { g.insert(v); } }
            { let mut h=heavy.lock().unwrap(); *h+=local_heavy; }
        }));
    }
    for h in handles { h.join().unwrap(); }
    if *sat.lock().unwrap() { return (p, *heavy.lock().unwrap()); }
    let g=good.lock().unwrap(); (g.len() as u64, 0)
}

fn main(){
    let args:Vec<String>=std::env::args().collect();
    let n:u64 = args[1].parse().unwrap();
    let k:usize = args[2].parse().unwrap();
    let a:u64 = args[3].parse().unwrap();
    let b:u64 = args[4].parse().unwrap();
    let size:usize = args[5].parse().unwrap();
    let lo:u64 = args[6].parse().unwrap();
    let nthreads:usize = args.get(7).map(|x|x.parse().unwrap()).unwrap_or(8);
    let p=find_prime_cong1(n,lo);
    let m=(p-1)/n;
    let s=mu_n(n,p);
    let (cnt,heavy)=incidence_dir(&s,p,k,a,b,size,nthreads);
    let r = n as usize - size;
    println!("n={} k={} dir(a={},b={}) size={} r={} delta={:.4} | p={} (m=(p-1)/n={}, m%2={}) => I={} heavy={} {}",
        n,k,a,b,size,r, r as f64/n as f64, p,m,m%2, cnt, heavy,
        if cnt>n {"BAD(>budget)"} else {"good(<=budget)"});
}
