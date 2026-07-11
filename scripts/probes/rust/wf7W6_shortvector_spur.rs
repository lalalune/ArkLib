// wf-W6: GEOMETRY-OF-NUMBERS short-vector count of spurious configs.
//
// A spurious config at depth r is sigma_T = sum_{i in T} eps_i zeta_n^i,  |T| <= 2r, eps_i in {+1,-1},
// with sigma_T != 0 over Z but sigma_T == 0 mod p (lands in a prime ideal above p, equiv. in the
// kernel of the evaluation map ev_h : Z[zeta_n] -> F_p, zeta_n |-> h, h a primitive n-th root mod p).
//
// LATTICE VIEW: Z[zeta_n] ~ Z^{phi(n)} via the power basis 1,zeta,...,zeta^{phi-1}.  The Minkowski
// (trace-form) embedding gives squared-length ||sigma||^2 = sum_j |sigma^{(j)}|^2 = phi(n)*|T| (the
// 2-power trace identity NT2: distinct roots are trace-orthonormal up to phi(n)).  So a weight-|T|
// config is a SHORT VECTOR of trace-radius^2 = phi(n)*|T| <= phi(n)*2r.
//
// Spurious configs = short vectors that ALSO lie in the index-p sublattice L_p = ker(ev_h mod p).
// L_p has covolume p in the phi(n)-dim trace lattice scaled... the count of these is what (S-M1) /
// the count route needs: Spur_r(p) = #{ short vectors of radius^2<=phi(n)*2r in L_p, nonzero over Z }.
//
// SUB-LEMMA (G-W6, the short-vector reduction this lane targets):
//   Spur_r(p) <= #{ v in Z[zeta_n], v != 0, ||v||^2 <= phi(n)*2r, ev_h(v)=0 mod p } - (sublattice gap)
// and the count of nonzero L_p-vectors of trace-radius^2 R is 0 as long as R < lambda_1(L_p)^2,
// where lambda_1(L_p) >= min(lambda_1(Z[zeta_n]), p^{1/phi}*lambda_1) by the index-p Minkowski step.
// Concretely: ev_h is surjective Z[zeta_n] ->> F_p (h has order n | p-1), so L_p = ker is an index-p
// sublattice; its shortest vector lambda_1(L_p) satisfies lambda_1(L_p)^2 >= ??? -- we MEASURE it and
// compare to the config radius phi(n)*2r at depth r ~ ln q.
//
// What we print, EXACT, at PRIZE SCALE (p ~ n^beta, p == 1 mod n), at DEPTH r ~ ln q:
//  - lambda_1(L_p)^2  (shortest nonzero vector of ker ev_h, trace-form length, via enumeration of
//    small combos -- here exact short-vector count by DP over the F_p-reduction)
//  - the config radius^2 R(r) = phi(n)*2r at the OPTIMAL depth r* ~ ln(p)/2
//  - whether R(r*) < lambda_1(L_p)^2  (=> Spur=0 at optimal depth => K=1 transfer, prize) for each prime
//  - the exact Spur_r(p) count at depth r (sum-zero-mod-p configs minus char-0 antipodal configs)
use std::collections::HashMap;
fn mpow(mut a:u64,mut e:u64,p:u64)->u64{let mut r=1u128;let mut a2=a as u128;let pp=p as u128;while e>0{if e&1==1{r=r*a2%pp;}a2=a2*a2%pp;e>>=1;}r as u64}
fn isp(n:u64)->bool{if n<2{return false}let mut d=2;while d*d<=n{if n%d==0{return false}d+=1}true}
fn fp(n:u64,lo:u64)->u64{let mut p=lo+((1+n-lo%n)%n);if p<=2{p+=n}loop{if p>2&&p%n==1&&isp(p){return p}p+=n}}
fn proot(p:u64)->u64{let mut m=p-1;let mut fs=vec![];let mut d=2;while d*d<=m{if m%d==0{fs.push(d);while m%d==0{m/=d}}d+=1}if m>1{fs.push(m)}let mut g=2;loop{if fs.iter().all(|&f|mpow(g,(p-1)/f,p)!=1){return g}g+=1}}

// E_r mod p: number of 2r-tuples from mu summing to 0 mod p (= A_r^modp + n^{2r}/p*... no: = full E_r)
fn e_modp(mu:&[u64],r:usize,p:u64)->u128{
    let mut d:HashMap<u64,u128>=HashMap::new();d.insert(0,1);
    for _ in 0..r{let mut nd:HashMap<u64,u128>=HashMap::new();for(&s,&c)in &d{for &x in mu{let t=((s as u128+x as u128)%p as u128)as u64;*nd.entry(t).or_insert(0)+=c;}}d=nd;}
    let mut t:u128=0;for(&s,&c)in &d{let ns=((p-s)%p)as u64;if let Some(&c2)=d.get(&ns){t+=c*c2;}}t
}
// E_r over Z (char-0): exact via fine-rounded complex DP
fn e_charzero(n:usize,r:usize)->u128{
    use std::f64::consts::PI;
    let cs:Vec<(f64,f64)>=(0..n).map(|e|((2.0*PI*e as f64/n as f64).cos(),(2.0*PI*e as f64/n as f64).sin())).collect();
    let scale=1e7;
    let mut d:HashMap<(i64,i64),u128>=HashMap::new();d.insert((0,0),1);
    for _ in 0..r{let mut nd:HashMap<(i64,i64),u128>=HashMap::new();
        for(&(kr,ki),&c)in &d{for &(cr,ci) in &cs{let nr=((kr as f64/scale+cr)*scale).round() as i64;let ni=((ki as f64/scale+ci)*scale).round() as i64;*nd.entry((nr,ni)).or_insert(0)+=c;}}d=nd;}
    let mut t:u128=0;for(&(kr,ki),&c)in &d{if let Some(&c2)=d.get(&(-kr,-ki)){t+=c*c2;}}t
}
fn dfact(r:usize)->f64{let mut v=1.0;for j in 1..=r{v*=(2*j-1)as f64}v}

// SHORT-VECTOR lambda_1(L_p): the smallest WEIGHT w (= number of signed roots) such that some
// signed sum of w roots zeta_n^{i} vanishes mod p but not over Z.  weight w <-> trace radius^2 = phi(n)*w.
// We BFS the reachable residues by signed roots ordered by weight; first nonzero-over-Z residue 0 hit.
// To detect "nonzero over Z" we track the full integer-exponent multiset is hard; instead use the
// standard fact: over Z[zeta_n] (n=2^a, char 0) a signed sum of roots vanishes iff it is antipodally
// matched, and the MINIMAL antipodal config has weight 2 (a single +z,-z pair).  So lambda_1 of the
// FULL lattice Z[zeta_n] in trace form is realized at weight 2 (the antipodal vector, which IS 0).
// For the spurious lattice we want: smallest weight of a config that is 0 mod p but the config is NOT
// the all-antipodal one. We compute the smallest weight w_min(p) such that #{configs weight<=w, 0 mod p}
// exceeds the char-0 antipodal count -- i.e. the FIRST depth where Spur>0.  That weight, times phi(n),
// is lambda_1(L_p)^2 in the trace form (the shortest *spurious* vector).
fn first_spur_weight(mu:&[u64], p:u64, max_w:usize, n:usize)->(usize, i128) {
    // For each r=w/2 (configs of EVEN total length 2r in the energy, but spurious vectors have weight
    // = |T| any parity). We measure spurious at each r via E_modp - E_char0.
    for r in 1..=max_w {
        let emp = e_modp(mu, r, p) as i128;
        let ez = e_charzero(n, r) as i128;
        let spur = emp - ez;
        if spur > 0 { return (2*r, spur); }
    }
    (0, 0) // no spurious up to max_w
}

fn run(n:usize, p:u64, max_w:usize){
    let g=proot(p);let h=mpow(g,(p-1)/n as u64,p);
    let mu:Vec<u64>=(0..n as u64).map(|j|mpow(h,j,p)).collect();
    let phi = (n/2) as f64; // phi(2^a) = 2^{a-1}
    let beta=(p as f64).ln()/(n as f64).ln();
    let lnq=(p as f64).ln();
    let rstar = lnq/2.0; // optimal moment depth r* ~ ln(q)/2
    let (wmin, spur_at) = first_spur_weight(&mu, p, max_w, n);
    let lam2 = if wmin>0 { phi*(wmin as f64) } else { f64::INFINITY };
    let rconfig = lnq; // config radius^2 = phi*2r; at r=rstar that's phi*2*rstar = phi*lnq
    println!("== n={} p={} beta={:.2} phi(n)={} ln q={:.1} r*~{:.1} ==", n,p,beta,n/2,lnq,rstar);
    println!("   shortest SPURIOUS vector: weight w_min={}  (trace radius^2 lambda1(L_p)^2={:.0}, spur count there={})",
        wmin, lam2, spur_at);
    println!("   config trace radius^2 at depth r: phi(n)*2r;  at r*={:.1} -> R(r*)={:.0}", rstar, phi*2.0*rstar);
    if wmin>0 {
        let rspur = (wmin as f64)/2.0;
        println!("   => first spurious at depth r_spur={:.1}, OPTIMAL depth r*={:.1};  margin r*-r_spur={:.1} (>0 => optimal depth ABOVE spurious onset => need band bound)",
            rspur, rstar, rstar - rspur);
    } else {
        println!("   => NO spurious config up to weight {} (=depth r={}): Spur=0 in scanned band => K=1 transfer holds here", 2*max_w, max_w);
    }
    let _ = rconfig;
}

fn main(){
    println!("# wf-W6 geometry-of-numbers: shortest spurious vector vs optimal moment depth, PRIZE SCALE p~n^4");
    // prize scale: p ~ n^4 (beta~4), p == 1 mod n
    run(8,  fp(8,  4096), 8);
    run(16, fp(16, 65536), 7);
    run(32, fp(32, 1_048_576), 6);
    run(64, fp(64, 16_777_216), 5);
    println!("\n# multiple prize primes at n=32 (uniformity check over p):");
    let mut lo = 1_048_576u64;
    for _ in 0..5 {
        let p = fp(32, lo);
        run(32, p, 6);
        lo = p + 1;
    }
}
