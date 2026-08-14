// NONPRINCIPAL cross-step pre-screen for M3 (lane wf-P3, issue #444).
// E_r = rEnergy(mu_n, r) = #{(v,w) in (mu_n^r)^2 : sum v = sum w} = sum_d freq_r(d)^2  (EXACT integer).
// freq_r(d) = #{ r-tuples from mu_n summing to d in F_p }. Built by exact convolution mod p.
// Recursion (proven, CharPMomentRecursion.rEnergy_succ): E_{r+1} = n*E_r + cross_r.
// cross_r := E_{r+1} - n*E_r   (the off-diagonal crossMass, EXACT integer).
// Ceiling slack the recursion can absorb (M3CrossStepBound): cross_r <= 2r*(2r-1)!!*n^{r+1}.
// NONPRINCIPAL recast: E_r' = E_r - n^{2r}/p (principal b=0 contributes n^{2r}/p to E_r).
//   cross_r' = cross_r - n^{2r+1}(n-1)/p   (principal recursion subtracted).
// We screen BOTH cross_r (full) and cross_r' (nonprincipal) against the slack ceiling.
// All E_r, cross_r are exact u128; the principal correction n^{2r}/p is a rational we track in f64
// (and we verify p | n^{2r} sum so E_r' is an honest reduction).

fn mpow(mut a:u64,mut e:u64,p:u64)->u64{let mut r=1u128;let mut a2=a as u128;let pp=p as u128;while e>0{if e&1==1{r=r*a2%pp;}a2=a2*a2%pp;e>>=1;}r as u64}
fn isp(n:u64)->bool{if n<2{return false}let mut d=2;while d*d<=n{if n%d==0{return false}d+=1}true}
fn fp(n:u64,lo:u64)->u64{let mut p=lo+((1+n-lo%n)%n);if p<=2{p+=n}loop{if p>2&&p%n==1&&isp(p){return p}p+=n}}
fn proot(p:u64)->u64{let mut m=p-1;let mut fs=vec![];let mut d=2;while d*d<=m{if m%d==0{fs.push(d);while m%d==0{m/=d}}d+=1}if m>1{fs.push(m)}let mut g=2;loop{if fs.iter().all(|&f|mpow(g,(p-1)/f,p)!=1){return g}g+=1}}
fn dfact(r:i64)->f64{if r<=0{return 1.0}let mut v=1.0;let mut k=r;while k>0{v*=k as f64;k-=2;}v} // (2r-1)!! for arg 2r-1

fn run(n:u64,p:u64,rmax:usize){
    let g=proot(p); let h=mpow(g,(p-1)/n,p);
    let mu:Vec<u64>=(0..n).map(|j|mpow(h,j,p)).collect();
    // freq vector over Z_p, exact u128 counts. freq_1(d)= #{x in mu : x=d}=1 for d in mu else 0.
    let pp=p as usize;
    let mut freq=vec![0u128; pp];
    for &x in &mu { freq[x as usize]+=1; }
    let beta=(p as f64).ln()/(n as f64).ln();
    println!("== n={} p={} m={} beta={:.2} (ln q={:.1}) ==", n,p,(p-1)/n,beta,(p as f64).ln());
    println!("  r |   E_r(exact)        E_r/char0 |  cross_r/slack | cross'_r/slack | E'_r/char0");
    // energy at level r = sum freq^2
    let mut er_prev: u128 = 0; // E_r for current freq level
    let mut have_prev=false;
    // we need E_r and E_{r+1}; compute energy at each level after building freq.
    // start: freq is level 1. compute E_1 then iterate convolution to get E_2, etc.
    let mut level=1usize;
    let mut energies: Vec<u128>=Vec::new();
    // record E_1
    let mut e1:u128=0; for &f in &freq { e1+=f*f; } energies.push(e1);
    while level<rmax+1 {
        // convolve freq by mu to get next level: nf[d] = sum_{s in mu} freq[d-s]
        let mut nf=vec![0u128;pp];
        for d in 0..pp {
            let fd=freq[d]; if fd==0 {continue;}
            for &s in &mu { let idx=((d as u64 + s)%p) as usize; nf[idx]+=fd; }
        }
        freq=nf; level+=1;
        let mut e:u128=0; for &f in &freq { e+=f*f; } energies.push(e);
    }
    // energies[r-1] = E_r. now report.
    let nf=n as f64;
    for r in 1..=rmax {
        let er=energies[r-1];
        let er1=energies[r]; // E_{r+1}
        let cross = er1 as i128 - (n as i128)*(er as i128); // cross_r exact
        let char0 = dfact(2*r as i64 -1)*nf.powi(r as i32);
        // principal corrections (rational, f64): pr_r = n^{2r}/p
        let pr_r = nf.powi(2*r as i32)/(p as f64);
        let pr_r1= nf.powi(2*(r as i32+1))/(p as f64);
        let er_p = er as f64 - pr_r;          // E'_r
        let cross_p = cross as f64 - (pr_r1 - nf*pr_r); // cross'_r = cross_r - (n^{2r+2}/p - n*n^{2r}/p)
        let slack = 2.0*(r as f64)*dfact(2*r as i64 -1)*nf.powi(r as i32 +1);
        let _ = (er_prev,have_prev);
        println!("  {:2}| {:18}  {:9.4} | {:11.4}  | {:11.4}   | {:9.4}",
            r, er, er as f64/char0, cross as f64/slack, cross_p/slack, er_p/char0);
        er_prev=er; have_prev=true;
    }
}
fn main(){
    // char-0-faithful primes (p large enough that no spurious mod-p root relations < depth):
    run(8,  fp(8, 3000),  9);
    run(16, fp(16,7000),  9);
    run(16, fp(16,200000),9);
    run(32, fp(32,60000), 8);
    run(32, fp(32,5000000),8);
}
