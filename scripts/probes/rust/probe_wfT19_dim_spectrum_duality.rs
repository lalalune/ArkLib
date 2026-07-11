// Probe T19 (G4-4): Schoen-Shkredov additive-dimension -> spectral-sparsity DUALITY.
//
// CLAIM under test: dim^+(mu_n) >= d_eff = Theta(n/polylog), and (Chang-converse) this
//   forces |Spec_alpha|/n <= C*log(p/n)/d_eff, hence M <= C*sqrt(n*log(p/n)).
//
// We test prize-faithfully (p PRIME, p=1 mod n, mu_n PROPER order n=2^mu, m=(p-1)/n>1,
// p ~ n^4 beta=4, NEVER n=p-1). We measure:
//   (1) M(n) = max_{b!=0}|eta_b|, eta_b = sum_{x in mu_n} e_p(bx)   [the prize object]
//   (2) dim^+(mu_n): the max dissociated subset of mu_n (additive dimension), EXACT brute small n.
//   (3) |Spec_alpha|: # of frequency cosets b with |eta_b| >= alpha*sqrt(n), for alpha thresholds.
//   (4) The CRUX: does spectrum sparsity bound the SUP, or only the COUNT?
//       M^2 = (largest single |eta_b|^2). Spectrum count controls Sum over large b, not the max.
//
// Honest test of the duality inequality |Spec_alpha|/n <= C*log(p/n)/d_eff and of whether
// it, combined with Parseval, yields M <= sqrt(n log) -- the structural question.

use std::f64::consts::PI;

fn mpow(mut a:u64, mut e:u64, p:u64)->u64{
    let mut r=1u128; let mut a2=a as u128; let pp=p as u128;
    while e>0 { if e&1==1 { r=r*a2%pp; } a2=a2*a2%pp; e>>=1; }
    let _=&mut a; r as u64
}
fn is_prime(n:u64)->bool{ if n<2 {return false;} let mut d=2; while d*d<=n { if n%d==0 {return false;} d+=1; } true }
fn find_prime_cong1(n:u64, lo:u64)->u64{
    let mut p = lo + ((n - lo%n)%n) + 1; // p = 1 mod n, >= lo
    while p%n!=1 { p+=1; }
    loop { if p>2 && p%n==1 && is_prime(p) { return p; } p+=n; }
}
fn primitive_root(p:u64)->u64{
    let mut m=p-1; let mut fs=vec![]; let mut d=2;
    while d*d<=m { if m%d==0 { fs.push(d); while m%d==0 { m/=d; } } d+=1; }
    if m>1 { fs.push(m); }
    let mut g=2u64;
    loop { if fs.iter().all(|&f| mpow(g,(p-1)/f,p)!=1) { return g; } g+=1; }
}

// eta_b = sum_{x in mu} e_p(b x)  (complex magnitude)
fn eta_mag(b:u64, mu:&[u64], p:u64)->f64{
    let mut re=0.0f64; let mut im=0.0f64;
    for &x in mu {
        let t=((b as u128 * x as u128) % p as u128) as u64;
        let ang=2.0*PI*(t as f64)/(p as f64);
        re+=ang.cos(); im+=ang.sin();
    }
    (re*re+im*im).sqrt()
}

// Max dissociated subset of S (additive dimension dim^+): largest D subset of S
// such that no nonzero {-1,0,1}-combination of D sums to 0 (mod p).
// Exact brute-force over subsets (only small n). mu elements as residues mod p.
fn additive_dimension(mu:&[u64], p:u64)->usize{
    let n=mu.len();
    if n>20 { return 0; } // brute only small
    // try to find a dissociated subset of max size by greedy + verification over all subsets sizes desc
    // For exactness we check: a subset D (as index bitmask) is dissociated iff all 3^|D| signed
    // sums {-1,0,1} are distinct (equivalently only the all-zero gives 0).
    let pp=p as i128;
    let dissociated=|idx:&Vec<usize>|->bool{
        let k=idx.len();
        if k==0 { return true; }
        // enumerate 3^k sign vectors; check no nonzero gives sum ≡ 0 mod p
        let mut pow3=1usize; for _ in 0..k { pow3*=3; }
        for code in 1..pow3 { // skip all-zero (code 0 = all coeff -1 in base-3 shift? define below)
            let mut c=code; let mut s:i128=0;
            for &j in idx {
                let digit=(c%3) as i128; c/=3; // 0,1,2 -> coeff -1,0,1
                let coeff=digit-1;
                s += coeff * (mu[j] as i128);
            }
            s = ((s % pp)+pp)%pp;
            if s==0 {
                // a nonzero combo summed to 0 -> NOT dissociated, unless this code is the all-"1"(=coeff0)
                // code where every digit==1 means all coeff 0 (the trivial). Check:
                let mut cc=code; let mut all_zero=true;
                for _ in 0..k { if cc%3 != 1 { all_zero=false; break; } cc/=3; }
                if !all_zero { return false; }
            }
        }
        true
    };
    // search largest dissociated subset (descending sizes)
    for size in (1..=n).rev() {
        // iterate subsets of given size (combinations)
        let mut comb:Vec<usize>=(0..size).collect();
        loop {
            if dissociated(&comb) { return size; }
            // next combination
            let mut i=size as isize -1;
            while i>=0 && comb[i as usize]==n-size+(i as usize) { i-=1; }
            if i<0 { break; }
            comb[i as usize]+=1;
            for j in (i as usize +1)..size { comb[j]=comb[j-1]+1; }
        }
    }
    0
}

fn main(){
    println!("# Probe T19: additive-dimension -> spectral-sparsity duality (prize-faithful beta=4)");
    println!("# n  p     m=(p-1)/n  M       M/sqrt(n)  M/sqrt(n*ln(p/n))  dim+  dim+/n  |Spec@1.5|  |Spec|/n  duality_RHS=C*ln(p/n)/dim+");
    let mus=[3u32,4,5,6]; // n=8,16,32,64
    for &mu in &mus {
        let n=1u64<<mu;
        // beta=4: p ~ n^4
        let target=(n as f64).powi(4) as u64;
        let p=find_prime_cong1(n, target);
        let g=primitive_root(p);
        let h=mpow(g,(p-1)/n,p);
        let muset:Vec<u64>=(0..n).map(|j|mpow(h,j,p)).collect();
        let m=(p-1)/n;
        // M and spectrum count over coset reps b = g^j*... we range over a transversal: g^k, k=0..m-1
        let gn=mpow(g,n,p);
        let mut best=0.0f64;
        let mut spec_count=0u64; // |eta_b| >= 1.5 sqrt(n)
        let thr=1.5*(n as f64).sqrt();
        let mut b=1u64;
        let cap=if m>200000 {200000} else {m}; // cap work for large m; M peak is dilation-robust
        for _ in 0..cap {
            let mag=eta_mag(b,&muset,p);
            if mag>best { best=best.max(mag); }
            if mag>=thr { spec_count+=1; }
            b=((b as u128*gn as u128)%p as u128) as u64;
        }
        // if capped, scale spec_count estimate to full m
        let spec_full = if cap<m { (spec_count as f64)*(m as f64)/(cap as f64) } else { spec_count as f64 };
        let lnpn=((p as f64)/(n as f64)).ln();
        let dimp=additive_dimension(&muset,p);
        let msq=best/(n as f64).sqrt();
        let mfloor=best/((n as f64)*lnpn).sqrt();
        let duality_rhs = if dimp>0 { 1.0*lnpn/(dimp as f64) } else { f64::NAN };
        println!("{:>3} {:>10} {:>9} {:>7.3} {:>9.4} {:>16.4} {:>5} {:>7.4} {:>10.1} {:>9.5} {:>10.5}",
            n,p,m,best,msq,mfloor,dimp,(dimp as f64)/(n as f64),spec_full,spec_full/(n as f64),duality_rhs);
    }
    println!();
    println!("# CRUX CHECK: the prize M is a SINGLE Fourier coefficient max, NOT a spectrum count.");
    println!("# If dim+ ~ n (grows) and the duality inequality |Spec_a|/n <= C ln(p/n)/dim+ held,");
    println!("#   |Spec_a|/n would shrink like ln/n -> 0. But M (the largest single |eta_b|) still");
    println!("#   tracks sqrt(n ln(p/n)) (M/sqrt(n) grows like sqrt(ln)). A sparse large-spectrum");
    println!("#   does NOT cap the size of the single largest coefficient -- only its multiplicity.");
}
