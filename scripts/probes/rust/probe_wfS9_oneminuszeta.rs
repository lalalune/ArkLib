// wf-S9b: the (1 - zeta)-adic / 2-adic ramified valuation of a spurious config sigma_T.
//
// SETUP.  K = Q(zeta_n), n = 2^mu, d = phi(n) = n/2. The prime 2 is TOTALLY RAMIFIED:
//   (2) = (1 - zeta)^{phi(n)},  lambda := 1 - zeta the unique prime above 2, e = phi(n) = n/2.
//   So  v_lambda(2) = phi(n),  v_lambda = phi(n) * v_2  on rationals, and for any algebraic
//   integer x in Z[zeta],  v_2(N_{K/Q}(x)) = v_lambda(x)   (residue degree f = 1 for lambda,
//   so each unit of lambda-valuation contributes exactly one factor of 2 to the absolute norm:
//   N(lambda) = +-2).
//
// THE 2-ADIC HANDLE ON THE SPURIOUS MASS (distinct from the split-p side of probe_wfS9_vp).
//   spur config  <=>  p | N(sigma_T)  with p the SPLIT prize prime (odd, p == 1 mod n).
//   v_2(N(sigma_T)) is then an ODD-prime-INDEPENDENT invariant of the config: it never sees p.
//   But it is exactly the lambda-adic valuation v_lambda(sigma_T), computable in Z[zeta] by
//   repeated division by (1 - zeta). KEY: a config of ODD weight w has N(sigma_T) ODD
//   (v_2 = 0) because sigma_T == w (mod lambda) and w odd => unit mod lambda. A config of EVEN
//   weight has v_lambda >= 1. This SPLITS configs by weight-parity in a p-free way:
//     - odd-weight configs: N is odd, so the only odd-prime divisibility is "generic";
//     - even-weight configs: N is even, v_2 = v_lambda >= 1, a 2-adic floor.
//   GROSS-KOBLITZ shape: v_lambda(sigma_T) = sum of digit-carries; the Stickelberger element
//   theta sum acts, and v_lambda is bounded below by the weight's 2-adic profile.
//
// WHAT WE MEASURE (exact, integer arithmetic in Z[zeta] = Z[x]/(x^d + 1), d = n/2):
//   (a) v_lambda(sigma_T) for every antipodal-free weight-w config  (= v_2 of the abs norm).
//   (b) the per-weight DISTRIBUTION of v_lambda, and its dependence on weight-parity.
//   (c) the floor:  min over weight-w configs of v_lambda  (a p-FREE lower bound on v_2(N)),
//       and whether it MATCHES the 2-adic valuation of the char-0 energy normalizer.
//   (d) the SHARP question: is v_lambda(sigma_T) determined by the weight alone (a clean
//       2-adic law), or does it depend on the support pattern? If a clean law: it gives a
//       p-free, weight-graded constraint the spurious mass must obey -- sharper than the
//       archimedean house which is parity-blind.
//
// build: rustc -O probe_wfS9_oneminuszeta.rs -o /tmp/s9b
// run:   /tmp/s9b <n> <wcap>

// We work in R = Z[x]/(x^d + 1), d = n/2.  zeta = x.  lambda = 1 - x.
// Represent a ring element as a degree-(d-1) integer vector (coeffs of 1, x, ..., x^{d-1}),
// reducing x^d = -1.
// v_lambda(elt) = number of times (1 - x) divides elt in R.  We compute by mapping to the
// chain of residues: R / lambda = F_2, and dividing.  Concretely: an element f(x) is
// divisible by (1 - x) iff f(1) == 0 ... but x has order 2d here, and (1-x) is the ramified
// prime over 2.  The clean computation: v_lambda(f) = v_2-adic order via the norm tower.
// Simplest exact route: compute the absolute norm N(f) = Res(f(x), x^d + 1) as an integer
// (= prod over the d complex roots), and read v_2(N) = v_lambda(f) (since f=1 for lambda).
// We get N(f) exactly via resultant = det of the d x d circulant-like Sylvester-free form:
// N(f) = prod_{k} f(zeta_k), zeta_k = exp(i pi (2k+1)/d) the primitive 2d-th... we instead
// use the integer resultant via the companion-matrix determinant over Z (exact, big-int).

// Big integer (signed) minimal impl via i128 fallback + checked; for n<=64, weights small,
// |N| <= house^d with house ~ 2 sqrt d, d<=32 -> |N| <= (2*5.6)^32 ~ 1e35 -> need bigint.
// Use a tiny bigint (Vec<u64> base 1e18) signed.

#[derive(Clone)]
struct Big { neg: bool, mag: Vec<u128> } // base 2^64 limbs, little-endian
impl Big {
    fn zero() -> Big { Big{neg:false, mag:vec![]} }
    fn from_i64(v: i64) -> Big {
        if v == 0 { return Big::zero() }
        Big{ neg: v < 0, mag: vec![ (v.unsigned_abs()) as u128 ] }
    }
    fn is_zero(&self) -> bool { self.mag.iter().all(|&l| l==0) }
    fn norm(&mut self){ while self.mag.len()>0 && *self.mag.last().unwrap()==0 { self.mag.pop(); } if self.mag.is_empty(){ self.neg=false; } }
    fn cmp_mag(a:&Big,b:&Big)->std::cmp::Ordering{
        if a.mag.len()!=b.mag.len(){ return a.mag.len().cmp(&b.mag.len()); }
        for i in (0..a.mag.len()).rev(){ if a.mag[i]!=b.mag[i]{ return a.mag[i].cmp(&b.mag[i]); } }
        std::cmp::Ordering::Equal
    }
    fn add_mag(a:&[u128],b:&[u128])->Vec<u128>{
        let mut r=vec![]; let mut carry=0u128; let n=a.len().max(b.len());
        for i in 0..n { let s = a.get(i).copied().unwrap_or(0) + b.get(i).copied().unwrap_or(0) + carry;
            r.push(s & ((1u128<<64)-1)); carry = s >> 64; }
        if carry>0 { r.push(carry); } r
    }
    fn sub_mag(a:&[u128],b:&[u128])->Vec<u128>{ // a>=b
        let mut r=vec![]; let mut borrow=0i128;
        for i in 0..a.len(){ let mut d = a[i] as i128 - b.get(i).copied().unwrap_or(0) as i128 - borrow;
            if d<0 { d += 1i128<<64; borrow=1;} else { borrow=0; } r.push(d as u128); }
        r
    }
    fn add(a:&Big,b:&Big)->Big{
        if a.neg==b.neg { let mut r=Big{neg:a.neg, mag:Big::add_mag(&a.mag,&b.mag)}; r.norm(); r }
        else {
            match Big::cmp_mag(a,b){
                std::cmp::Ordering::Equal=>Big::zero(),
                std::cmp::Ordering::Greater=>{ let mut r=Big{neg:a.neg, mag:Big::sub_mag(&a.mag,&b.mag)}; r.norm(); r }
                std::cmp::Ordering::Less=>{ let mut r=Big{neg:b.neg, mag:Big::sub_mag(&b.mag,&a.mag)}; r.norm(); r }
            }
        }
    }
    fn mul(a:&Big,b:&Big)->Big{
        if a.is_zero()||b.is_zero(){ return Big::zero(); }
        let mut r=vec![0u128; a.mag.len()+b.mag.len()];
        for i in 0..a.mag.len(){
            let mut carry=0u128;
            for j in 0..b.mag.len(){
                let cur = r[i+j] + a.mag[i]*( b.mag[j] & ((1u128<<32)-1)) ; // split to avoid overflow
                // do full 64x64 -> 128 via splitting
                let _ = cur;
                let (lo,hi) = mul64(a.mag[i] as u64, b.mag[j] as u64);
                let s = r[i+j] + lo as u128 + carry;
                r[i+j] = s & ((1u128<<64)-1);
                carry = (s>>64) + hi as u128;
            }
            let mut k=i+b.mag.len();
            while carry>0 { let s=r[k]+carry; r[k]=s&((1u128<<64)-1); carry=s>>64; k+=1; }
        }
        let mut res=Big{ neg: a.neg!=b.neg, mag:r }; res.norm(); res
    }
    // divide by 2, return quotient; assumes even (we only call when v_2 step valid). returns (q, rem_bit)
    fn divmod2(&self)->(Big,u8){
        let mut q=vec![0u128; self.mag.len()]; let mut rem=0u128;
        for i in (0..self.mag.len()).rev(){
            let cur = (rem<<64) | self.mag[i];
            q[i] = cur >> 1; rem = cur & 1;
        }
        let mut bq=Big{neg:self.neg, mag:q}; bq.norm(); (bq, rem as u8)
    }
}
fn mul64(a:u64,b:u64)->(u64,u64){ let p=(a as u128)*(b as u128); (p as u64, (p>>64) as u64) }

// Norm N(f) = resultant(f(x), x^d+1) = prod_{k=0}^{d-1} f(zeta_k), zeta_k primitive 2d-th roots
// that are roots of x^d+1.  Compute exactly as the determinant of the multiplication-by-f map
// on R = Z[x]/(x^d+1) (a d x d integer matrix), via fraction-free Bareiss.
fn norm_via_resultant(coeffs:&Vec<i64>, d:usize)->Big{
    // multiplication matrix M: column j = x^j * f(x) mod (x^d+1), as coeff vector.
    // (M)_{i,j} = coeff of x^i in x^j * f.
    let mut m = vec![vec![Big::zero(); d]; d];
    for j in 0..d {
        // x^j * f : shift coeffs by j, reduce x^d=-1
        for i in 0..d {
            if coeffs[i]==0 { continue; }
            let mut deg = i + j;
            let mut sign = 1i64;
            while deg >= d { deg -= d; sign = -sign; }
            let add = Big::from_i64(sign*coeffs[i]);
            m[deg][j] = Big::add(&m[deg][j], &add);
        }
    }
    // Bareiss fraction-free determinant
    let mut prev = Big::from_i64(1);
    for k in 0..d {
        // pivot must be nonzero; if zero, find swap (sign flip)
        if m[k][k].is_zero() {
            let mut sw=None;
            for r in k+1..d { if !m[r][k].is_zero() { sw=Some(r); break; } }
            match sw { None=>return Big::zero(), Some(r)=>{ m.swap(k,r); /* sign flips; fix at end via parity */
                // track sign by negating row
                for c in 0..d { m[k][c].neg = !m[k][c].neg; m[k][c].norm(); }
            }}
        }
        for i in k+1..d {
            for j in k+1..d {
                let t1=Big::mul(&m[i][j], &m[k][k]);
                let t2=Big::mul(&m[i][k], &m[k][j]);
                let mut num = Big::add(&t1, &Big{neg:!t2.neg, mag:t2.mag});
                // divide by prev exactly
                num = big_exact_div(&num, &prev);
                m[i][j]=num;
            }
            m[i][k]=Big::zero();
        }
        prev = m[k][k].clone();
    }
    m[d-1][d-1].clone()
}
// exact division a / b (b divides a), via long division base 2^64 — but Bareiss divisor can be
// large; implement schoolbook exact division by repeated subtraction in base. For our sizes use
// a simple binary long division.
fn big_exact_div(a:&Big, b:&Big)->Big{
    if a.is_zero(){ return Big::zero(); }
    if b.mag.len()==1 && b.mag[0]==1 { let mut r=a.clone(); r.neg = a.neg!=b.neg; r.norm(); return r; }
    // binary long division of magnitudes
    let neg = a.neg != b.neg;
    let bb = Big{neg:false, mag:b.mag.clone()};
    let mut rem = Big::zero();
    let abits = a.mag.len()*64;
    let mut q = vec![0u128; a.mag.len()];
    for bit in (0..abits).rev(){
        // rem <<= 1; rem |= bit of a
        rem = shl1(&rem);
        let abit = (a.mag[bit/64] >> (bit%64)) & 1;
        if abit==1 { rem.mag.get_mut(0).map(|v|*v|=1).unwrap_or_else(||{rem.mag=vec![1];}); if rem.mag.is_empty(){rem.mag=vec![1];} else {rem.mag[0]|=1;} }
        rem.norm();
        if Big::cmp_mag(&rem,&bb)!=std::cmp::Ordering::Less {
            rem = Big{neg:false, mag:Big::sub_mag(&rem.mag,&bb.mag)}; rem.norm();
            q[bit/64] |= 1u128 << (bit%64);
        }
    }
    let mut res=Big{neg, mag:q}; res.norm(); res
}
fn shl1(a:&Big)->Big{
    let mut r=vec![]; let mut carry=0u128;
    for &l in &a.mag { let s=(l<<1)|carry; r.push(s & ((1u128<<64)-1)); carry = l>>63; }
    if carry>0 { r.push(carry); }
    let mut b=Big{neg:a.neg, mag:r}; b.norm(); b
}
fn v2_of(b:&Big)->u32{
    if b.is_zero(){ return 9999; }
    let mut x=b.clone(); let mut v=0;
    loop { let (q,r)=x.divmod2(); if r==1 { break; } x=q; v+=1; if x.is_zero(){break;} }
    v
}

fn main(){
    let args:Vec<String>=std::env::args().collect();
    let n:usize = if args.len()>1 { args[1].parse().unwrap() } else { 16 };
    let wcap:usize = if args.len()>2 { args[2].parse().unwrap() } else { 8 };
    let d = n/2;
    println!("== wf-S9b (1-zeta)-adic / 2-adic valuation of spurious configs: n={} d=phi={} ==", n, d);
    println!("   (2) = lambda^{}, lambda = 1 - zeta;  v_2(N(sigma_T)) = v_lambda(sigma_T) [f=1].", d);
    println!("   p-FREE invariant (never sees the split prize prime). per-weight v_2(N) distribution:\n");

    // enumerate antipodal-free configs on power basis: a in {-1,0,1}^d, a[0]=1 fixed (gauge), weight<=wcap
    let mut histo: Vec<std::collections::BTreeMap<u32,u64>> = vec![Default::default(); wcap+1];
    let mut minv = vec![u32::MAX; wcap+1];
    let mut total = vec![0u64; wcap+1];
    let mut a = vec![0i64; d]; a[0]=1;
    fn rec(a:&mut Vec<i64>, pos:usize, d:usize, used:usize, wcap:usize,
           histo:&mut Vec<std::collections::BTreeMap<u32,u64>>, minv:&mut Vec<u32>, total:&mut Vec<u64>){
        if pos==d {
            let w=used; if w==0 {return;}
            total[w]+=1;
            let nrm = norm_via_resultant(a, d);
            let v = v2_of(&nrm);
            *histo[w].entry(v).or_insert(0)+=1;
            if v<minv[w]{minv[w]=v;}
            return;
        }
        a[pos]=0; rec(a,pos+1,d,used,wcap,histo,minv,total);
        if used<wcap {
            a[pos]=1; rec(a,pos+1,d,used+1,wcap,histo,minv,total);
            a[pos]=-1; rec(a,pos+1,d,used+1,wcap,histo,minv,total);
            a[pos]=0;
        }
    }
    rec(&mut a,1,d,1,wcap,&mut histo,&mut minv,&mut total);

    println!("   w | total | min v_2(N) | parity | v_2 histogram (v2:count)");
    for w in 1..=wcap {
        if total[w]==0 { continue; }
        print!("  {:2} | {:>9} | {:>3} | {} |", w, total[w], if minv[w]==u32::MAX {9999} else {minv[w]},
               if w%2==1 {"ODD "} else {"EVEN"});
        for (v,c) in &histo[w]{ print!(" {}:{}", v, c); }
        println!();
    }
    println!("\n   LAW CHECK: odd-weight configs should ALL have v_2=0 (N odd, sigma==w==1 mod lambda).");
    let mut odd_all_zero=true; let mut even_floor_ge1=true;
    for w in 1..=wcap {
        if total[w]==0 {continue;}
        if w%2==1 { if histo[w].keys().any(|&v| v!=0) { odd_all_zero=false; } }
        else { if minv[w]<1 { even_floor_ge1=false; } }
    }
    println!("     odd-weight => v_2=0 ALWAYS: {}", odd_all_zero);
    println!("     even-weight => v_2>=1 ALWAYS (2-adic floor): {}", even_floor_ge1);
    println!("   CONSEQUENCE: a spur config (p|N, p odd) of ODD weight has N odd; the 2-adic part is");
    println!("     EMPTY there, so the p-divisibility is purely odd-cyclotomic. Even-weight configs");
    println!("     carry a forced 2-adic floor v_2>=1 independent of p -- a p-free weight-parity law.");
}
