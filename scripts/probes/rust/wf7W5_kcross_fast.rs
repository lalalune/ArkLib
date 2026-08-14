// wf-W5 K-STABILITY via FLOAT-PERIOD method (fast, O(m*n) per level, no O(p) array).
// A_r(mu_n) = (1/p) sum_{b!=0} eta_b^{2r}, eta_b = sum_{x in mu_n} cos(2 pi b x / p)  (real, neg-closed).
//   (= E_r - n^{2r}/p exactly; the DC-subtracted moment.)
// We use the SAME prime p for mu_n AND mu_{n/2}=squares (h2 = h^2 generates the index-2 subgroup),
//   so the dyadic split A_r(mu_n)=2 A_r(mu_{n/2})+crossA_r is computed against a common field.
//   mu_{n/2} as a subset of mu_n: x -> x^2, i.e. generator h^2, n/2 elements; b ranges over SAME nonzero F_p.
// crossA_r := A_r(n) - 2 A_r(n/2).
// Kcross(n,r) := ( crossA_r / [(2r-1)!! (n^r - 2 (n/2)^r)] )^{1/r}   (per-level K increment; the induction load-bearer)
// Keff(n,r)   := ( A_r / [(2r-1)!! n^r] )^{1/r}
// K-STABILITY: Kcross(n) <= Keff(n/2)  =>  if A_r(n/2) <= Keff(n/2)^r Wick(n/2) then A_r(n) <= Keff(n/2)^r Wick(n).
// Report at depth r ~ ln q (the optimal r* and a window around it), peak over r, across n and beta. Multiple primes.

use std::f64::consts::PI;
use std::thread; use std::sync::Arc;
fn mpow(a:u64,mut e:u64,p:u64)->u64{let mut r=1u128;let mut a2=a as u128;let pp=p as u128;while e>0{if e&1==1{r=r*a2%pp;}a2=a2*a2%pp;e>>=1;}r as u64}
fn isp(n:u64)->bool{if n<2{return false}if n%2==0{return n==2}let mut d=3;while d*d<=n{if n%d==0{return false}d+=2}true}
fn primes(n:u64,lo:u64,k:usize)->Vec<u64>{let mut o=vec![];let mut p=lo+((1+n-lo%n)%n);if p<=2{p+=n}loop{if p>2&&p%n==1&&isp(p){o.push(p);if o.len()>=k{break}}p+=n}o}
fn proot(p:u64)->u64{let mut m=p-1;let mut fs=vec![];let mut d=2;while d*d<=m{if m%d==0{fs.push(d);while m%d==0{m/=d}}d+=1}if m>1{fs.push(m)}let mut g=2;loop{if fs.iter().all(|&f|mpow(g,(p-1)/f,p)!=1){return g}g+=1}}
fn ldfact(r:i64)->f64{if r<=0{return 0.0}let mut v=0.0;let mut k=r;while k>0{v+=(k as f64).ln();k-=2;}v} // ln(2r-1)!!

// returns ln A_r for r=1..rmax, where A_r = (1/p) sum_{b!=0} eta_b^{2r}, eta_b real period of subgroup gen by `hgen`, size `sz`.
fn ln_ar(hgen:u64,sz:u64,p:u64,rmax:usize,nth:usize)->Vec<f64>{
    let mu:Vec<u64>=(0..sz).map(|j|mpow(hgen,j,p)).collect();
    let mu=Arc::new(mu);
    // b ranges over ALL nonzero residues 1..p-1 (full nonprincipal set). group by cosets of mu? No: sum over ALL b!=0.
    // That's p-1 terms * sz cos each = (p-1)*sz. For p~1e8 too big. Instead: eta_b depends only on coset of b under mu_n (largest group)?
    // eta_b for subgroup G: eta_b = sum_{x in G} cos(2pi b x/p). As b ranges over a coset of G, the multiset {bx} is the same coset, so eta_b constant on cosets of G. So distinct eta values = (p-1)/|G| cosets, each repeated |G| times.
    // We must use the LARGEST relevant group to coset-reduce. For mu_n use cosets of mu_n; for mu_{n/2} its eta is constant on cosets of mu_{n/2}. To keep a COMMON enumeration we sum over coset reps of the FINEST group = mu_{n/2}, weight = |mu_{n/2}|.
    // Simpler & exact: sum over all b!=0 by iterating coset reps of mu_n (size sz_n) won't align for the half. Use coset reps of the subgroup itself with its own multiplicity.
    let g=proot(p); let m=(p-1)/sz; // number of cosets of THIS subgroup
    let gn=mpow(g,sz,p); // generator of the quotient: coset reps g^0,g^1,...,g^{m-1} times subgroup
    let chunk=(m+nth as u64-1)/nth as u64;
    let mut handles=vec![];
    for t in 0..nth as u64{
        let lo=t*chunk; let hi=((t+1)*chunk).min(m); if lo>=hi{continue}
        let mu=Arc::clone(&mu);
        handles.push(thread::spawn(move||{
            let mut s=vec![0.0f64;rmax+1];
            let mut b=mpow(gn,lo,p); let pp=p as u128; let inv=2.0*PI/p as f64;
            for _ in lo..hi{
                let mut re=0.0;
                for &x in mu.iter(){let tt=((b as u128*x as u128)%pp)as u64; re+=(inv*(tt as f64)).cos();}
                // this coset rep stands for `sz` values of b (the whole coset), each with the SAME eta?
                // NO: eta_{b} for b in coset c*G equals sum cos(2pi c*x'/p) over x'=g_c*G = same as eta for rep -> yes constant on cosets of G. multiplicity sz.
                let e2=re*re; let mut pw=1.0;
                for r in 1..=rmax{pw*=e2; s[r]+= (sz as f64)*pw;}
                b=((b as u128*gn as u128)%pp)as u64;
            }
            s
        }));
    }
    let mut tot=vec![0.0f64;rmax+1];
    for h in handles{let s=h.join().unwrap(); for r in 1..=rmax{tot[r]+=s[r];}}
    let lp=(p as f64).ln();
    (1..=rmax).map(|r| tot[r].ln()-lp).collect()
}

fn main(){
    let a:Vec<String>=std::env::args().collect();
    let beta:f64=if a.len()>1{a[1].parse().unwrap()}else{4.0};
    let nth:usize=if a.len()>2{a[2].parse().unwrap()}else{8};
    println!("############ wf-W5 Kcross (per-level induction load) beta={} ############",beta);
    println!("# Kcross(n,r)=(crossA_r/[(2r-1)!!(n^r-2(n/2)^r)])^1/r, crossA_r=A_r(n)-2A_r(n/2).");
    println!("# K-STABLE iff Kcross(n)<=Keff(n/2). r* = round(ln q /2).");
    let ns=[8u64,16,32,64,128,256];
    for &n in &ns{
        let lo=((n as f64).powf(beta))as u64;
        let ps=primes(n,lo,2);
        for &p in &ps{
            let g=proot(p); let h=mpow(g,(p-1)/n,p); let h2=mpow(h,2,p); // gen of mu_{n/2}=squares
            let lnq=(p as f64).ln(); let rstar=(lnq/2.0).round().max(2.0)as usize;
            let rmax=(rstar+5).min(28);
            let lnA_n=ln_ar(h,n,p,rmax,nth);
            let lnA_h=ln_ar(h2,n/2,p,rmax,nth);
            let nf=n as f64; let hf=(n/2)as f64;
            let mut peak_keff=0.0f64; let mut pkr=0;
            let mut peak_keff_h=0.0f64;
            let mut peak_kcross=0.0f64; let mut pkcr=0;
            let mut kcross_rstar=f64::NAN; let mut keff_rstar=f64::NAN;
            for r in 1..=rmax{
                let lnwick=ldfact(2*r as i64-1)+r as f64*nf.ln();
                let lnwickh=ldfact(2*r as i64-1)+r as f64*hf.ln();
                let ar=lnA_n[r-1].exp(); let arh=lnA_h[r-1].exp();
                let keff=((lnA_n[r-1]-lnwick)/r as f64).exp();
                if keff>peak_keff{peak_keff=keff;pkr=r;}
                let kh=((lnA_h[r-1]-lnwickh)/r as f64).exp();
                if kh>peak_keff_h{peak_keff_h=kh;}
                let crossa=ar-2.0*arh;
                let denom=lnwick.exp()-2.0*lnwickh.exp(); // (2r-1)!!(n^r-2(n/2)^r); EXACTLY 0 at r=1 (n-2(n/2)=0) so exclude r<=1
                if r>=2 && denom>0.0 && crossa>0.0{
                    let kc=(crossa/denom).powf(1.0/r as f64);
                    if kc>peak_kcross{peak_kcross=kc;pkcr=r;}
                    if r==rstar{kcross_rstar=kc;}
                }
                if r==rstar{keff_rstar=keff;}
            }
            let stable= peak_kcross<=peak_keff_h+1e-9;
            println!("n={:3} p={:11} beta={:.2} lnq={:.1} r*={:2} | Keff={:.4}@r{} Keff(n/2)={:.4} | Kcross(peak)={:.4}@r{} Kcross(r*)={:.4} | STABLE={}",
                n,p,(p as f64).ln()/nf.ln(),lnq,rstar, peak_keff,pkr, peak_keff_h, peak_kcross,pkcr, kcross_rstar, stable);
        }
    }
}
