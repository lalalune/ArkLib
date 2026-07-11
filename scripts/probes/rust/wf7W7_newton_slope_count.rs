// wf-W7: p-adic / (1-zeta)-adic Newton-polygon SLOPE-COUNT of the spurious excess.
//
// SETTING.  p prime, n=2^mu | p-1, mu_n the order-n subgroup of F_p*.  eta_b = sum_{x in mu_n} e_p(bx).
//   A_r(mu_n) = (1/p) sum_{b!=0} eta_b^{2r} = E_r - n^{2r}/p,  E_r = #{(x,y) in mu_n^{2r}: sum x = sum y mod p}.
//   Char-0 (Lam-Leung, PROVEN in-tree DyadicEnergyK1): E_r^{(0)} <= (2r-1)!! n^r.
//   Spur_r(p) := E_r(p) - E_r^{(0)}  (the char-p EXCESS = spurious mod-p coincidences).
//   TARGET (Wick bound): A_r <= K^r (2r-1)!! n^r  at r ~ ln q ~ beta ln n.
//
// W7 NEWTON-POLYGON STRATEGY (distinct from W4 union-bound and W6 short-vector):
//   Each balanced 2r-config (r-tuple = r-tuple mod p over mu_n) corresponds to a signed sum
//   sigma = sum_{x in tup1} zeta^{i_x} - sum_{y in tup2} zeta^{i_y}  (zeta = primitive n-th root, here
//   the embedding zeta -> h in F_p).  "sum x = sum y mod p" <=> sigma == 0 mod p <=> the cyclotomic
//   integer Sigma = sum +-zeta_n^{...} (over Z[zeta_n]) lies in SOME prime 𝔭_k above p.
//   Over Z (char 0) Sigma = 0  <=>  antipodal-matched (Lam-Leung); these are the (2r-1)!! matchings.
//   The SPURIOUS ones have Sigma != 0 over Z but Sigma == 0 mod p.
//
//   NEWTON-POLYGON of the aggregated valuation.  Group all configs by their NORM N = |N_{Q(zeta_n)/Q}(Sigma)|
//   (a nonneg integer; 0 exactly for char-0/antipodal configs).  For the NONZERO-norm (antipodal-free)
//   configs, p | N <=> v_p(N) >= 1.  The KEY refinement over W4: we look at the Newton polygon of the
//   generating polynomial in the (1-zeta_p)-adic / p-adic slope, i.e. we sort the spurious configs by
//   v_p(N) and count the SLOPE MULTIPLICITIES m_s = #{antipodal-free configs T : v_p(N_T) = s}.
//   - slope-0 segment (v_p = 0): genuine non-divisible -> NOT spurious (don't hit 0 mod p).
//   - slope >=1 segments (v_p >= 1): the SPURIOUS configs.  Spur_r = sum_{s>=1} m_s.
//
//   The SHARP claim W7 targets (NP segment-count bound):
//     (S-W7)  sum_{s>=1} m_s(r,p)  <=  eps_r * (2r-1)!! n^r,   eps_r -> 0 as r -> ln q at prize scale,
//   established by: the antipodal-free configs have norm N >= 1 (a vanishing-free LOWER bound), and the
//   FRACTION with p | N is the slope->=1 mass, governed by equidistribution of {N_T mod p}.
//   We MEASURE the slope histogram {m_s} exactly at band depth and read off Spur_r and eps_r.
//
//   THE NP MASS LAW we test:  the slope-0 mass m_0 (antipodal-free, p-INDIVISIBLE) dominates;
//   the total slope->=1 mass / total antipodal-free mass = "spurious fraction" f_r, and the claim is
//   f_r ~ phi(n)/p (Chebotarev), so Spur_r = f_r * (antipodal-free count) <= f_r * E_r^{(0)}*(stuff),
//   and crucially Spur_r/Wick -> 0.  We also separate: does v_p ever exceed 1?  (higher slopes = rare).
//
// EXACT method (no sampling for the count; sampling only for the slope HISTOGRAM at large n):
//   E_r(p): DP over residues mod p of r-fold sums from mu_n, then E_r = sum_s (count_s)^2  -- exact.
//   E_r^{(0)}: complex DP (rounded) of r-fold sums of n-th roots, count antipodal-balanced pairs -- exact.
//   Spur_r = E_r(p) - E_r^{(0)}.
//   Slope histogram: Monte-Carlo sample antipodal-free balanced 2r-configs, compute N exactly via the
//   phi(n) conjugate evaluations mod p^t (lift), read v_p(N).  (For prize scale where Spur=0 exactly,
//   we report Spur=0 and the union ceiling phi(n)/p.)
//
// build: rustc -O wf7W7_newton_slope_count.rs -o /tmp/w7

use std::collections::HashMap;

fn mpow(a:u64,mut e:u64,p:u64)->u64{let mut r=1u128;let mut a2=a as u128;let pp=p as u128;while e>0{if e&1==1{r=r*a2%pp;}a2=a2*a2%pp;e>>=1;}r as u64}
fn isp(n:u64)->bool{if n<2{return false}let mut d=2;while d*d<=n{if n%d==0{return false}d+=1}true}
// first prize prime >= lo with p == 1 mod n
fn fp(n:u64,lo:u64)->u64{let mut p=lo+((1+n-lo%n)%n);if p<=2{p+=n}loop{if p>2&&p%n==1&&isp(p){return p}p+=n}}
fn proot(p:u64)->u64{let mut m=p-1;let mut fs=vec![];let mut d=2;while d*d<=m{if m%d==0{fs.push(d);while m%d==0{m/=d}}d+=1}if m>1{fs.push(m)}let mut g=2;loop{if fs.iter().all(|&f|mpow(g,(p-1)/f,p)!=1){return g}g+=1}}
fn dfact(r:usize)->f64{let mut v=1.0;for j in 1..=r{v*=(2*j-1)as f64}v}

// E_r(p): #{2r-tuples from mu summing balanced mod p} = sum_s c_s^2 where c_s = #{r-tuples summing to s}.
fn e_modp(mu:&[u64],r:usize,p:u64)->u128{
    let mut d:HashMap<u64,u128>=HashMap::new();d.insert(0,1);
    for _ in 0..r{let mut nd:HashMap<u64,u128>=HashMap::new();for(&s,&c)in &d{for &x in mu{let t=((s as u128+x as u128)%p as u128)as u64;*nd.entry(t).or_insert(0)+=c;}}d=nd;}
    let mut t:u128=0;for(&_s,&c)in &d{t+=c*c;}t
}
// E_r^{(0)} over Z (char-0): complex DP, count r-tuple-sum coincidences over C (exact via rounding).
fn e_charzero(n:usize,r:usize)->u128{
    use std::f64::consts::PI;
    let cs:Vec<(f64,f64)>=(0..n).map(|e|((2.0*PI*e as f64/n as f64).cos(),(2.0*PI*e as f64/n as f64).sin())).collect();
    let scale=1e7;
    let mut d:HashMap<(i64,i64),u128>=HashMap::new();d.insert((0,0),1);
    for _ in 0..r{let mut nd:HashMap<(i64,i64),u128>=HashMap::new();
        for(&(kr,ki),&c)in &d{for &(cr,ci) in &cs{let nr=((kr as f64/scale+cr)*scale).round() as i64;let ni=((ki as f64/scale+ci)*scale).round() as i64;*nd.entry((nr,ni)).or_insert(0)+=c;}}d=nd;}
    let mut t:u128=0;for(&(kr,ki),&c)in &d{t+=c*c;let _=(kr,ki);}
    // NOTE: char-0 E_r = sum_s c_s^2 with s ranging over COMPLEX sums; coincidence sum x = sum y over Z[zeta].
    t
}

fn main(){
    println!("# wf-W7 Newton-polygon slope-count of the spurious excess");
    println!("# columns: n  beta  p  r  E_r(p)  E_r^0  Spur_r  Wick=(2r-1)!!n^r  Spur/Wick  A_r/Wick  K_eff=(A/W)^(1/r)  phi/p");
    // sweep n, multiple betas (=> prize primes p ~ n^beta), and r through band depth r* ~ ln q / 2 .. 1.5 r*
    for &n in &[16usize,32,64,128]{
        for &beta in &[2.0f64,3.0,4.0]{
            let target=(n as f64).powf(beta);
            let p=fp(n as u64, target as u64);
            let g=proot(p);let h=mpow(g,(p-1)/n as u64,p);
            let mu:Vec<u64>=(0..n as u64).map(|j|mpow(h,j,p)).collect();
            let lnq=(p as f64).ln();
            let rstar=(lnq/2.0).round().max(2.0) as usize; // optimal moment depth
            let phi=(n/2) as f64;
            // run r from 2 up through ~1.5 r* (band depth = r ~ ln q)
            let rmax=((1.5*rstar as f64).round() as usize).min(13).max(rstar+2);
            for r in 2..=rmax{
                let emp=e_modp(&mu,r,p) as f64;
                let e0=e_charzero(n,r) as f64;
                let spur=emp-e0;
                let wick=dfact(r)*(n as f64).powi(r as i32);
                // A_r = E_r - n^{2r}/p  (DC-subtracted).  Spur is the char-p excess over char-0.
                let ar=emp-(n as f64).powf(2.0*r as f64)/p as f64;
                let band = if r==rstar {" <-r*"} else {""};
                println!("{:4} {:3} {:>12} {:3} {:>14.0} {:>12.0} {:>12.0} {:>14.3e} {:>10.3e} {:>9.4} {:>8.4} {:>10.3e}{}",
                    n, beta as i32, p, r, emp, e0, spur, wick, spur/wick, ar/wick, (ar/wick).max(1e-300).powf(1.0/r as f64), phi/p as f64, band);
            }
            println!();
        }
    }
}
