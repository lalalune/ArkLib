// Exact far-line delta* over mu_n in F_p — faithful Rust port of
// scripts/probes/probe_farline_incidence_exact.py (the proven in-tree object).
// delta* = (largest r with max_far_incidence(r) <= budget) / n,  budget = n (prize).
// Resolves regime-B: does delta* decrease toward Johnson (1/2) [locked] or increase toward the floor [revival]?

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
    // factor p-1
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

// left null space of V (size x k) over F_p: rows of the size-dim space killing the columns.
// Returns Vec of null vectors (each length `size`).
fn left_null(vmat:&[Vec<u64>], size:usize, k:usize, p:u64)->Vec<Vec<u64>>{
    // augment [V | I_size], rref
    let mut rows: Vec<Vec<u64>> = (0..size).map(|i|{
        let mut r=vec![0u64; k+size];
        for j in 0..k { r[j]=vmat[i][j]; }
        r[k+i]=1;
        r
    }).collect();
    let nc=k+size; let mut pr=0usize;
    for c in 0..nc {
        let mut sel=None;
        for rr in pr..size { if rows[rr][c]%p!=0 { sel=Some(rr); break; } }
        let sel=match sel{Some(x)=>x,None=>continue};
        rows.swap(pr,sel);
        let inv=minv(rows[pr][c],p);
        for j in 0..nc { rows[pr][j]=mmul(rows[pr][j],inv,p); }
        for rr in 0..size { if rr!=pr && rows[rr][c]%p!=0 {
            let f=rows[rr][c];
            for j in 0..nc { rows[rr][j]=msub(rows[rr][j], mmul(f,rows[pr][j],p), p); }
        }}
        pr+=1; if pr==size {break;}
    }
    let mut out=vec![];
    for r in &rows {
        if (0..k).all(|j| r[j]%p==0) && (0..size).any(|j| r[k+j]%p!=0) {
            out.push((0..size).map(|j| r[k+j]%p).collect());
        }
    }
    out
}

// incidence I(a,b;r): returns (count, saturated)
// enumerates all size-subsets R of [0,n), size=n-r.
fn incidence(s:&[u64], p:u64, k:usize, pa_:&[u64], pb_:&[u64], r:usize)->(u64,bool){
    let n=s.len(); let size=n-r;
    if size<=k { return (p,true); }
    let mut good:HashSet<u64>=HashSet::new();
    // subset enumeration via index combinations
    let mut idx:Vec<usize>=(0..size).collect();
    loop {
        // build V (size x k) and run
        let vmat:Vec<Vec<u64>>=idx.iter().map(|&ii|{
            let xi=s[ii]; let mut row=vec![0u64;k]; let mut acc=1u64;
            for j in 0..k { row[j]=acc; acc=mmul(acc,xi,p); }
            row
        }).collect();
        let pnull=left_null(&vmat,size,k,p);
        if !pnull.is_empty() {
            // pa = P * pa_|R, pb = P * pb_|R
            let mut sat=false; let mut single=false;
            // compute pb vector and pa vector per null row
            let dim=pnull.len();
            let mut pav=vec![0u64;dim]; let mut pbv=vec![0u64;dim];
            for t in 0..dim {
                let mut sa=0u64; let mut sb=0u64;
                for (jj,&ii) in idx.iter().enumerate() {
                    let c=pnull[t][jj];
                    if c!=0 { sa=madd(sa, mmul(c,pa_[ii],p), p); sb=madd(sb, mmul(c,pb_[ii],p), p); }
                }
                pav[t]=sa; pbv[t]=sb;
            }
            let any_pb = pbv.iter().any(|&x| x%p!=0);
            if !any_pb {
                if pav.iter().all(|&x| x%p==0) { sat=true; }
            } else {
                let i=pbv.iter().position(|&x| x%p!=0).unwrap();
                let g=mmul(msub(0,pav[i],p), minv(pbv[i],p), p);
                if (0..dim).all(|t| madd(pav[t], mmul(g,pbv[t],p), p)%p==0) { single=true;
                    good.insert(g);
                }
            }
            if sat { return (p,true); }
            let _=single;
        }
        // next combination (lexicographic over increasing idx in [0,n))
        let mut i=size as isize -1;
        while i>=0 && idx[i as usize]==n-size+i as usize { i-=1; }
        if i<0 { break; }
        idx[i as usize]+=1;
        for j in (i as usize+1)..size { idx[j]=idx[j-1]+1; }
    }
    (good.len() as u64, false)
}

// max far incidence over directions b in [k, n-r), a in [0,n), a!=b. Parallel over (a,b).
fn max_far_incidence(s:&[u64], p:u64, k:usize, r:usize, nthreads:usize)->(u64,(usize,usize)){
    let n=s.len(); let size=n-r;
    if size<=k { return (p,(0,0)); }
    let mut jobs=vec![];
    for b in k..size { for a in 0..n { if a!=b { jobs.push((a,b)); } } }
    let jobs=Arc::new(jobs);
    let s=Arc::new(s.to_vec());
    let best=Arc::new(Mutex::new((0i64,(0usize,0usize))));
    let next=Arc::new(Mutex::new(0usize));
    let mut handles=vec![];
    for _ in 0..nthreads {
        let jobs=Arc::clone(&jobs); let s=Arc::clone(&s); let best=Arc::clone(&best); let next=Arc::clone(&next);
        handles.push(thread::spawn(move||{
            loop{
                let ji={ let mut g=next.lock().unwrap(); let j=*g; *g+=1; j };
                if ji>=jobs.len() {break;}
                let (a,b)=jobs[ji];
                let pa_:Vec<u64>=s.iter().map(|&x| mpow(x,a as u64,p)).collect();
                let pb_:Vec<u64>=s.iter().map(|&x| mpow(x,b as u64,p)).collect();
                let (c,_)=incidence(&s,p,k,&pa_,&pb_,r);
                let mut bg=best.lock().unwrap();
                if c as i64 > bg.0 { *bg=(c as i64,(a,b)); }
            }
        }));
    }
    for h in handles { h.join().unwrap(); }
    let bg=best.lock().unwrap(); (bg.0 as u64, bg.1)
}

fn delta_star(n:u64, k:usize, p:u64, budget:u64, nthreads:usize, rmin:usize, rmax_cap:usize)->(Option<usize>,Option<usize>){
    let s=mu_n(n,p);
    let mut last_good= if rmin>k+1 { Some(rmin-1) } else { None };
    let hi = std::cmp::min((n as usize)-k+1, rmax_cap);
    for r in rmin..=hi {
        let (mx,st)=max_far_incidence(&s,p,k,r,nthreads);
        eprintln!("  n={} p={} r={} (delta={:.4}) max_far={} binder={:?} budget={}", n,p,r, r as f64/n as f64, mx, st, budget);
        if mx<=budget { last_good=Some(r); } else { return (last_good, Some(r)); }
    }
    (last_good, None)
}

fn main(){
    let args:Vec<String>=std::env::args().collect();
    let n:u64 = args.get(1).map(|x|x.parse().unwrap()).unwrap_or(16);
    let k:usize = args.get(2).map(|x|x.parse().unwrap()).unwrap_or((n/4) as usize);
    let lo:u64 = args.get(3).map(|x|x.parse().unwrap()).unwrap_or(200003);
    let rmin:usize = args.get(4).map(|x|x.parse().unwrap()).unwrap_or(k+1);
    let rmax_cap:usize = args.get(5).map(|x|x.parse().unwrap()).unwrap_or(n as usize);
    let nthreads=8usize;
    let p=find_prime_cong1(n,lo);
    let budget=n;
    let (lg,bad)=delta_star(n,k,p,budget,nthreads,rmin,rmax_cap);
    match lg {
        Some(r)=>println!("RESULT n={} k={} rho={:.3} p={} : delta* = {}/{} = {:.4}  (Johnson {:.4}={}/{}); first bad r={:?}",
            n,k,k as f64/n as f64,p, r,n, r as f64/n as f64, 1.0-(k as f64/n as f64).sqrt(), n/2, n, bad),
        None=>println!("RESULT n={} k={} p={} : no bad r up to cap {}", n,k,p,rmax_cap),
    }
}
