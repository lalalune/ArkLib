// Probe T19b: sweep the spectrum threshold alpha to show the large-spectrum count is NOT
// O(n*log(p/n)/dim+) for ANY alpha up to the floor scale -- the duality inequality fails
// at every threshold, and the SINGLE max keeps growing like sqrt(n log).
//
// For the duality (dim+ ~ n) to give M <= C sqrt(n log) via Parseval, one needs
//   |{b: |eta_b| >= alpha sqrt(n)}| <= (something forcing the max alpha to be O(sqrt(log))).
// Parseval: sum_{b!=0} |eta_b|^2 = (p-n)*... ~ p*n. If |Spec_alpha| frequencies each have
//   |eta_b|^2 >= alpha^2 n, then |Spec_alpha| <= p*n/(alpha^2 n) = p/alpha^2. That is the ONLY
//   constraint Parseval+count give -- and it is the trivial sqrt(p) bound at alpha~1 (since
//   |Spec| can be up to p/alpha^2). dim+ does NOT enter. We display this.

use std::f64::consts::PI;
fn mpow(mut a:u64, mut e:u64, p:u64)->u64{ let mut r=1u128; let mut a2=a as u128; let pp=p as u128;
    while e>0 { if e&1==1 { r=r*a2%pp; } a2=a2*a2%pp; e>>=1; } let _=&mut a; r as u64 }
fn is_prime(n:u64)->bool{ if n<2 {return false;} let mut d=2; while d*d<=n { if n%d==0 {return false;} d+=1; } true }
fn find_prime_cong1(n:u64, lo:u64)->u64{ let mut p=lo+((n-lo%n)%n)+1; while p%n!=1 {p+=1;}
    loop { if p>2 && p%n==1 && is_prime(p) { return p; } p+=n; } }
fn primitive_root(p:u64)->u64{ let mut m=p-1; let mut fs=vec![]; let mut d=2;
    while d*d<=m { if m%d==0 { fs.push(d); while m%d==0 {m/=d;} } d+=1; } if m>1 {fs.push(m);}
    let mut g=2u64; loop { if fs.iter().all(|&f| mpow(g,(p-1)/f,p)!=1) { return g; } g+=1; } }
fn eta_mag(b:u64, mu:&[u64], p:u64)->f64{ let mut re=0.0f64; let mut im=0.0f64;
    for &x in mu { let t=((b as u128 * x as u128)%p as u128) as u64; let ang=2.0*PI*(t as f64)/(p as f64);
        re+=ang.cos(); im+=ang.sin(); } (re*re+im*im).sqrt() }

fn main(){
    println!("# Probe T19b: spectrum-count vs alpha threshold, full m (beta=4 prize-faithful)");
    let mus=[3u32,4,5]; // n=8,16,32 (full m enumeration)
    let alphas=[1.0f64,1.5,2.0,2.5,3.0,3.5,4.0];
    for &mu in &mus {
        let n=1u64<<mu;
        let target=(n as f64).powi(4) as u64;
        let p=find_prime_cong1(n,target);
        let g=primitive_root(p); let h=mpow(g,(p-1)/n,p);
        let muset:Vec<u64>=(0..n).map(|j|mpow(h,j,p)).collect();
        let m=(p-1)/n; let gn=mpow(g,n,p);
        let lnpn=((p as f64)/(n as f64)).ln();
        // enumerate all m coset reps, collect magnitudes
        let mut mags=Vec::with_capacity(m as usize);
        let mut b=1u64;
        for _ in 0..m { mags.push(eta_mag(b,&muset,p)); b=((b as u128*gn as u128)%p as u128) as u64; }
        let best=mags.iter().cloned().fold(0.0f64,f64::max);
        // each coset rep counts for n frequencies (period coset-constant) -> total nonzero freqs = n*m = p-1
        println!("n={} p={} m={} M={:.3} M/sqrt(n)={:.3} M/sqrt(n*ln)={:.3} ln(p/n)={:.3}",
            n,p,m,best,best/(n as f64).sqrt(),best/((n as f64)*lnpn).sqrt(),lnpn);
        for &a in &alphas {
            let thr=a*(n as f64).sqrt();
            let cnt_cosets=mags.iter().filter(|&&v| v>=thr).count() as u64;
            let cnt_freqs=cnt_cosets*n; // total frequencies (each coset = n freqs)
            // Parseval-permitted max count at this alpha: p/alpha^2 (the ONLY count bound, dim-free)
            let parseval_permit=(p as f64)/(a*a);
            println!("  alpha={:.1}: |Spec|(freqs)={:>10} |Spec|/n={:>9.2} Parseval-permit(p/a^2)={:>12.0} ratio={:.4}",
                a,cnt_freqs,(cnt_freqs as f64)/(n as f64),parseval_permit,(cnt_freqs as f64)/parseval_permit);
        }
        println!();
    }
    println!("# VERDICT: |Spec_alpha| is governed by Parseval (count <= p/alpha^2), NOT by dim+.");
    println!("# The duality C*log(p/n)/dim+ ~ const is off by orders of magnitude. And the SINGLE max M");
    println!("# grows like sqrt(n log) regardless -- count-sparsity is the wrong lever for a sup-norm.");
}
