// probe_wfH47_sieve_largeset_structure.rs  (#444 lane L2, angle H47)
//
// QUESTION (Selberg / Gallagher larger-sieve precondition test):
//   A Gallagher larger sieve can cap |A| ONLY if the set A occupies FEW residue classes
//   mod many small primes l (a congruence/multiplicative-structure hypothesis). The large
//   sieve / Selberg sieve give upper bounds on COUNTS / L2 averages, never on the SUP.
//   For the prize, M(n) = max_b |eta_b|. The relevant "set" a sieve could try to cap is
//       A_T = { b in F_p^* : |eta_b| > T }
//   We TEST whether A_T has the congruence structure a larger sieve needs:
//     (1) Does A_T occupy few residue classes b mod l for small primes l ? (larger-sieve input)
//     (2) Is A_T a union of few cosets of mu_n / structured multiplicatively?
//   If A_T is EQUIDISTRIBUTED in residue classes mod l (occupies ~ (|A_T|/l)*l = all-ish
//   classes proportionally), the larger sieve gives NO nontrivial cap: nu(l) ~ l, and
//   the Gallagher bound |A| <= (log scale) degenerates to trivial.
//
//   NB: eta_b is coset-constant on mu_n (eta_{ub}=eta_b, u in mu_n), so A_T is a UNION OF
//   FULL mu_n-COSETS by construction. The sieve question is whether the SET OF COSETS that
//   are large has residue structure mod l, where l is a prime UNRELATED to n.
//
// EXACT: we rank cosets by |eta_b|^2 using f64 cos/sin at small primes (ranking is robust;
//   the STRUCTURAL conclusion = "no congruence structure of the large set" is the output,
//   and that conclusion is qualitative/distributional, not a fragile float threshold).
//   We additionally report, EXACTLY (integer), the residue-class occupancy counts.
//
// beta=4 regime (p ~ n^4), p = 1 mod n, n = 2-power.

use std::f64::consts::PI;

fn mpow(a:u64,mut e:u64,p:u64)->u64{let mut r=1u128;let mut a2=a as u128;let pp=p as u128;while e>0{if e&1==1{r=r*a2%pp;}a2=a2*a2%pp;e>>=1;} r as u64}
fn is_prime(n:u64)->bool{if n<2{return false;}let mut d=2;while d*d<=n{if n%d==0{return false;}d+=1;}true}
fn find_prime_cong1(n:u64,lo:u64)->u64{let mut p=lo+((1+n-lo%n)%n);if p<=2{p+=n;}loop{if p>2&&p%n==1&&is_prime(p){return p;}p+=n;}}
fn primitive_root(p:u64)->u64{let mut m=p-1;let mut fs=vec![];let mut d=2;while d*d<=m{if m%d==0{fs.push(d);while m%d==0{m/=d;}}d+=1;}if m>1{fs.push(m);}let mut g=2;loop{if fs.iter().all(|&f|mpow(g,(p-1)/f,p)!=1){return g;}g+=1;}}

fn main(){
    let args:Vec<String>=std::env::args().collect();
    let ns:Vec<u64>= if args.len()>1 { args[1..].iter().map(|x|x.parse().unwrap()).collect() }
                     else { vec![16,32,64,128] };
    println!("# H47: Gallagher/Selberg larger-sieve precondition test on A_T = {{b : |eta_b| > T}}");
    println!("# A_T is a union of mu_n-cosets (eta coset-constant). We test residue structure of the");
    println!("# LARGE cosets mod small primes l. larger sieve needs nu(l)<<l; we measure nu(l).");
    for &n in &ns {
        let target = (n as f64).powf(4.0) as u64;
        let p = find_prime_cong1(n, target.max(200003));
        let g = primitive_root(p);
        let h = mpow(g,(p-1)/n,p);
        let mu:Vec<u64>=(0..n).map(|j|mpow(h,j,p)).collect();
        let m=(p-1)/n;
        // coset reps b_j = g^j, j=0..m-1.  Compute |eta_{b_j}|^2 (f64) and keep b_j (exact u64).
        let gn = mpow(g,n,p);
        let mut vals:Vec<(f64,u64)> = Vec::with_capacity(m as usize);
        let mut b=1u64;
        for _ in 0..m {
            let mut re=0.0f64; let mut im=0.0f64;
            for &x in &mu {
                let t=((b as u128 * x as u128)%p as u128) as u64;
                let ang=2.0*PI*(t as f64)/(p as f64);
                re+=ang.cos(); im+=ang.sin();
            }
            vals.push((re*re+im*im, b));
            b=((b as u128 * gn as u128)%p as u128) as u64;
        }
        // sort descending by |eta|^2
        vals.sort_by(|a,c| c.0.partial_cmp(&a.0).unwrap());
        let mmax = vals[0].0.sqrt();
        let cconst = mmax/(((n as f64)*((p as f64/n as f64).ln())).sqrt());
        // Define A_T as the top tau-fraction of cosets (tau = 1%, 5%, 10%).
        // The larger-sieve question: do the b in A_T avoid residue classes mod small l?
        // If A_T occupies ~ all l classes (nu(l) ~ min(|A_T|, l)), the sieve is vacuous.
        println!("\n## n={} p={} (beta={:.3}) m={} cosets   M={:.3}  C={:.4}",
                 n, p, (p as f64).ln()/(n as f64).ln(), m, mmax, cconst);
        let small_primes:Vec<u64>=vec![3,5,7,11,13,17,19,23].into_iter().filter(|&l| l!=n%l || true).collect();
        for &tau_pct in &[1u64,5,10] {
            let k = ((m as f64)*(tau_pct as f64/100.0)).ceil() as usize;
            let k = k.max(1).min(m as usize);
            let topset:Vec<u64> = vals[..k].iter().map(|&(_,b)|b).collect();
            print!("  A_T (top {:>2}% = {:>5} cosets):", tau_pct, k);
            for &l in &small_primes {
                // nu(l) = number of DISTINCT residue classes b mod l hit by A_T (exact integer)
                let mut occ = vec![false; l as usize];
                for &b in &topset { occ[(b % l) as usize] = true; }
                let nu = occ.iter().filter(|&&x|x).count();
                let full = (l as usize).min(k);          // max classes A_T could occupy
                // ratio nu/full close to 1 => no avoidance => sieve vacuous
                print!("  l={}:nu/{}={}/{}", l, full, nu, full);
            }
            println!();
        }
    }
    println!("\n# READ: if nu(l)/min(l,|A_T|) ~ 1 for all l (A_T hits ~every residue class mod l),");
    println!("#   Gallagher larger sieve gives nu(l)~l => NO nontrivial cap on |A_T|. And even a");
    println!("#   sharp cap on |A_T| (the COUNT) says nothing about M (the SUP value). PARITY-LIKE");
    println!("#   obstruction: the sieve sees cardinality/L2-average, never the pointwise sup.");
}
