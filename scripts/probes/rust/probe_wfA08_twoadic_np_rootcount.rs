// wf-A08: 2-adic Newton polygon ROOT COUNT of the period/relation generating polynomial.
//
// SETUP. K = Q(zeta_n), n = 2^mu, d = phi(n) = n/2. The prime 2 is TOTALLY RAMIFIED:
//   (2) = lambda^d, lambda = 1 - zeta, e = d, residue degree f = 1, so for x in Z[zeta]:
//       v_2(N_{K/Q}(x)) = v_lambda(x).
//
// THE NEWTON-POLYGON ANGLE (genuinely fresh, manifesto route 3):
//   A char-0 vanishing-sum relation among 2^mu-th roots is, by Lam-Leung, a union of
//   antipodal pairs (zeta^i + zeta^{i+d} = 0). The SPURIOUS configs are the antipodal-free
//   sigma_T = sum_{i in T} eps_i zeta^i (eps_i in {+1,-1}) that vanish mod p but NOT over Z.
//
//   We study the 2-adic (lambda-adic) Newton polygon of sigma_T as an element of Z[zeta] =
//   Z[x]/(x^d+1). Write sigma_T in the lambda-adic filtration: v_lambda(sigma_T) tells which
//   NP "slope segment" the config sits in. The KEY question: does the lambda-adic valuation
//   give a SHARPER count of the spurious mass than Mann's archimedean weight floor (w >= p^{2/n})?
//
//   Mann/archimedean: bounds w (the weight) -> w >= p^{2/n}, VACUOUS at prize n.
//   2-adic NP: counts configs by v_lambda. The fresh metric:
//     #{ antipodal-free configs of weight w : v_lambda(sigma_T) >= V }
//   vs the total #{ weight w } = C(d, ...) * 2^...   (the archimedean-blind count).
//   If the v_lambda >= V slice is a STRICT, computable fraction, that fraction is a 2-adic
//   refinement Mann cannot see.
//
// WHAT WE MEASURE (exact bigint resultant N(sigma_T), v_2 = v_lambda):
//   (a) For each weight w: full histogram of v_lambda over antipodal-free configs.
//   (b) The NP "slope profile": cumulative count #{v_lambda >= V} for V = 0,1,2,...
//   (c) The CEILING law: max v_lambda at weight w, and whether it = (w-1) or d-1 etc.
//   (d) The KEY comparison: at the weight that Mann would need (w ~ p^{2/n}, here just the
//       max even weight d), how concentrated is v_lambda? Does v_lambda max out at d-1
//       (the "fully ramified" extreme = the all-distinct-power balanced config)?
//   (e) NEW: the lambda-adic valuation of sigma_T as a function of the BINARY weight w:
//       conjecture v_lambda(sigma_T) >= f(w) where f tracks 2-adic carries.

#[derive(Clone)]
struct Big { neg: bool, mag: Vec<u128> }
impl Big {
    fn zero() -> Big { Big{neg:false, mag:vec![]} }
    fn from_i64(v: i64) -> Big {
        if v == 0 { return Big::zero() }
        Big{ neg: v < 0, mag: vec![ v.unsigned_abs() as u128 ] }
    }
    fn is_zero(&self) -> bool { self.mag.iter().all(|&l| l==0) }
    fn norm(&mut self){ while self.mag.last()==Some(&0){ self.mag.pop(); } if self.mag.is_empty(){ self.neg=false; } }
    fn cmp_mag(a:&Big,b:&Big)->std::cmp::Ordering{
        if a.mag.len()!=b.mag.len(){ return a.mag.len().cmp(&b.mag.len()); }
        for i in (0..a.mag.len()).rev(){ if a.mag[i]!=b.mag[i]{ return a.mag[i].cmp(&b.mag[i]); } }
        std::cmp::Ordering::Equal
    }
    fn add_mag(a:&Vec<u128>,b:&Vec<u128>)->Vec<u128>{
        let mut r=vec![]; let mut carry=0u128; let n=a.len().max(b.len());
        for i in 0..n{ let x=*a.get(i).unwrap_or(&0); let y=*b.get(i).unwrap_or(&0);
            // base 2^64 to avoid overflow in mul; here add in base 2^64
            let s=x+y+carry; r.push(s & ((1u128<<64)-1)); carry=s>>64; }
        if carry>0{ r.push(carry); } r
    }
    fn sub_mag(a:&Vec<u128>,b:&Vec<u128>)->Vec<u128>{ // a>=b
        let mut r=vec![]; let mut borrow=0i128; 
        for i in 0..a.len(){ let x=a[i] as i128; let y=*b.get(i).unwrap_or(&0) as i128;
            let mut s=x-y-borrow; if s<0 { s+= 1i128<<64; borrow=1;} else {borrow=0;} r.push(s as u128); }
        r
    }
    fn add(a:&Big,b:&Big)->Big{
        if a.neg==b.neg{ let mut r=Big{neg:a.neg,mag:Big::add_mag(&a.mag,&b.mag)}; r.norm(); r }
        else {
            match Big::cmp_mag(a,b){
                std::cmp::Ordering::Equal=>Big::zero(),
                std::cmp::Ordering::Greater=>{ let mut r=Big{neg:a.neg,mag:Big::sub_mag(&a.mag,&b.mag)}; r.norm(); r }
                std::cmp::Ordering::Less=>{ let mut r=Big{neg:b.neg,mag:Big::sub_mag(&b.mag,&a.mag)}; r.norm(); r }
            }
        }
    }
    fn mul(a:&Big,b:&Big)->Big{
        if a.is_zero()||b.is_zero(){ return Big::zero(); }
        let mut r=vec![0u128; a.mag.len()+b.mag.len()];
        for i in 0..a.mag.len(){ let mut carry=0u128;
            for j in 0..b.mag.len(){
                let cur = r[i+j] + (a.mag[i]*b.mag[j] & ((1u128<<64)-1)) + carry;
                // need full 128 product; split
                let prod = a.mag[i].wrapping_mul(b.mag[j]); // low 128 only -> NOT enough for 64x64
                let _ = prod;
                let _ = cur;
                // do proper 64x64->128 using u64
                let lo = (a.mag[i] as u64) as u128 * (b.mag[j] as u64) as u128; // <=2^128
                let s = r[i+j] + (lo & ((1u128<<64)-1)) + carry;
                r[i+j] = s & ((1u128<<64)-1);
                carry = (s>>64) + (lo>>64);
            }
            r[i+b.mag.len()] += carry;
        }
        let mut res=Big{neg: a.neg!=b.neg, mag:r}; res.norm(); res
    }
    // v_2 of a Big (number of trailing zero bits / treated as integer)
    fn v2(&self)->u32{
        if self.is_zero(){ return u32::MAX; }
        let mut v=0u32;
        for (i,&limb) in self.mag.iter().enumerate(){
            if limb==0 { v += 64; }
            else { v += (limb as u64).trailing_zeros(); break; }
            let _ = i;
        }
        v
    }
}

// Polynomial over Big mod (x^d + 1): coeffs length d.
fn poly_mul_mod(a:&Vec<Big>, b:&Vec<Big>, d:usize)->Vec<Big>{
    let mut r=vec![Big::zero(); d];
    for i in 0..d{ if a[i].is_zero(){continue;}
        for j in 0..d{ if b[j].is_zero(){continue;}
            let prod=Big::mul(&a[i],&b[j]);
            let k=i+j;
            if k<d { r[k]=Big::add(&r[k],&prod); }
            else { // x^k = -x^{k-d}
                let mut neg=prod.clone(); neg.neg=!neg.neg; if neg.mag.is_empty(){neg.neg=false;}
                r[k-d]=Big::add(&r[k-d],&neg);
            }
        }
    }
    r
}

// N(sigma_T) = Res(sigma_T(x), x^d+1) = prod over roots = det of mult-by-sigma_T map on Z[zeta].
// We compute it as the resultant via: N = prod_{k=0}^{d-1} sigma_T(zeta_k) where zeta_k are the
// 2d-th roots of unity that are primitive... but exactly: the absolute norm of an element of
// Z[x]/(x^d+1) equals the determinant of the multiplication matrix. Cheaper exact route for v_2:
// v_2(N) = v_lambda(sigma_T). We instead use: in Z[x]/(x^d+1), reduce mod 2 chain.
// CLEANEST exact: compute N via the multiplication-matrix determinant over Z (Bareiss), big.
// For our purposes (v_2 only), use the lambda-adic division algorithm directly:
//   lambda = 1 - x. v_lambda(f) = number of times (1-x) | f in Z[x]/(x^d+1).
//   But Z[x]/(x^d+1) is not a UFD-friendly setting for naive division.
// Use the embedding: v_lambda(f) = v_2(N(f)) and compute N(f) by repeated norm-down the 2-power tower:
//   N_{Q(zeta_{2^mu})/Q} via successive relative norms over the subfields. Simpler: directly
//   evaluate the integer determinant of the d x d circulant-(negacyclic) matrix of sigma_T.
// We do negacyclic-matrix determinant via fraction-free Bareiss with Big.

fn det_negacyclic(coeffs:&Vec<i64>, d:usize)->Big{
    // matrix M[i][j] = coeff at (j - i mod d) with sign: x^d=-1 negacyclic
    // row i represents x^i * sigma_T reduced. M[i][k] = contribution to x^k.
    let mut m=vec![vec![Big::zero(); d]; d];
    for i in 0..d{
        for t in 0..d{ // sigma has coeff coeffs[t] at x^t; row i: x^i * x^t = x^{i+t}
            if coeffs[t]==0 { continue; }
            let k=i+t;
            let val = Big::from_i64(coeffs[t]);
            if k<d { m[i][k]=Big::add(&m[i][k],&val); }
            else { let mut nv=val.clone(); nv.neg=!nv.neg; if nv.mag.is_empty(){nv.neg=false;} m[i][k-d]=Big::add(&m[i][k-d],&nv); }
        }
    }
    // Bareiss fraction-free determinant
    let mut prev=Big::from_i64(1);
    for p in 0..d{
        // find pivot
        if m[p][p].is_zero(){
            let mut sw=None;
            for r in p+1..d{ if !m[r][p].is_zero(){ sw=Some(r); break; } }
            match sw { Some(r)=>{ m.swap(p,r); /* det sign flips */ for c in 0..d{ m[p][c].neg=!m[p][c].neg; if m[p][c].mag.is_empty(){m[p][c].neg=false;} } }, None=>return Big::zero() }
        }
        for r in p+1..d{
            for c in p+1..d{
                let t1=Big::mul(&m[r][c],&m[p][p]);
                let t2=Big::mul(&m[r][p],&m[p][c]);
                let mut num=Big::add(&t1,&Big{neg:!t2.neg,mag:t2.mag.clone()});
                // divide by prev exactly
                m[r][c]=big_div_exact(&num,&prev);
                num=m[r][c].clone(); let _=num;
            }
            m[r][p]=Big::zero();
        }
        prev=m[p][p].clone();
    }
    m[d-1][d-1].clone()
}

// exact division a / b (b | a) for Big via long division base 2^64
fn big_div_exact(a:&Big,b:&Big)->Big{
    if a.is_zero(){ return Big::zero(); }
    // schoolbook: since exact, do repeated subtraction in base 2^64 from top - use simple algorithm
    // Convert to base-2^32 for simplicity of division
    let neg = a.neg != b.neg;
    let q = big_div_mag(&a.mag,&b.mag);
    let mut r=Big{neg, mag:q}; r.norm(); r
}
fn big_div_mag(a:&Vec<u128>,b:&Vec<u128>)->Vec<u128>{
    // base 2^32 long division
    let to32=|v:&Vec<u128>|->Vec<u64>{ let mut o=vec![]; for &l in v{ o.push((l & 0xffffffff) as u64); o.push(((l>>32)&0xffffffff) as u64);} while o.last()==Some(&0){o.pop();} o };
    let mut na=to32(a); let nb=to32(b);
    if nb.is_empty(){ return vec![]; }
    // simple: use u128 accumulation long division digit by digit in base 2^32
    let mut quo=vec![0u64; na.len()];
    // We'll do binary long division on the 32-bit limbs treating as big number. For exactness with
    // b|a, do schoolbook division: find quotient by binary search per shift. Simpler: use the fact
    // that values fit: convert to f? no. Use repeated knuth? Implement basic base-2^32 division.
    // Represent as big-endian for division:
    na.reverse();
    let mut nb_be=nb.clone(); nb_be.reverse();
    // long division
    let mut rem:Vec<u64>=vec![];
    let mut q_be:Vec<u64>=vec![];
    let cmp=|x:&Vec<u64>,y:&Vec<u64>|->std::cmp::Ordering{
        let xx:Vec<u64>=x.iter().cloned().skip_while(|&v|v==0).collect();
        let yy:Vec<u64>=y.iter().cloned().skip_while(|&v|v==0).collect();
        if xx.len()!=yy.len(){return xx.len().cmp(&yy.len());}
        for i in 0..xx.len(){ if xx[i]!=yy[i]{return xx[i].cmp(&yy[i]);} }
        std::cmp::Ordering::Equal
    };
    let sub=|x:&Vec<u64>,y:&Vec<u64>|->Vec<u64>{ // x-y big-endian, x>=y
        let mut xr:Vec<u64>=x.iter().cloned().rev().collect();
        let yr:Vec<u64>=y.iter().cloned().rev().collect();
        let mut borrow=0i64;
        for i in 0..xr.len(){ let yi=*yr.get(i).unwrap_or(&0) as i64; let mut s=xr[i] as i64 - yi - borrow;
            if s<0{s+=1i64<<32; borrow=1;}else{borrow=0;} xr[i]=s as u64; }
        let mut o:Vec<u64>=xr.into_iter().rev().collect(); while o.len()>1 && o[0]==0 {o.remove(0);} o
    };
    let mul1=|y:&Vec<u64>,f:u64|->Vec<u64>{ let mut o=vec![]; let mut carry=0u64;
        for &v in y.iter().rev(){ let p=v as u128 * f as u128 + carry as u128; o.push((p & 0xffffffff) as u64); carry=(p>>32) as u64; }
        while carry>0{ o.push((carry & 0xffffffff) as u64); carry>>=32; }
        o.reverse(); while o.len()>1 && o[0]==0 {o.remove(0);} o
    };
    for &digit in &na {
        rem.push(digit);
        while rem.len()>1 && rem[0]==0 { rem.remove(0); }
        // find largest f in [0,2^32) with nb_be*f <= rem
        let mut lo=0u64; let mut hi=(1u64<<32)-1; let mut f=0u64;
        while lo<=hi{ let mid=(lo+hi)/2; let prod=mul1(&nb_be,mid);
            if cmp(&prod,&rem)!=std::cmp::Ordering::Greater { f=mid; if mid==hi{break;} lo=mid+1; } else { if mid==0{break;} hi=mid-1; } }
        let prod=mul1(&nb_be,f);
        rem=sub(&rem,&prod);
        q_be.push(f);
    }
    // q_be big-endian base 2^32 -> base 2^64 little-endian
    while q_be.len()>1 && q_be[0]==0 { q_be.remove(0); }
    let mut q_le32:Vec<u64>=q_be.into_iter().rev().collect();
    if q_le32.len()%2==1{ q_le32.push(0); }
    let mut out=vec![];
    for i in (0..q_le32.len()).step_by(2){ out.push(q_le32[i] as u128 | ((q_le32[i+1] as u128)<<32)); }
    while out.last()==Some(&0){out.pop();}
    out
}

fn main(){
    let args:Vec<String>=std::env::args().collect();
    let n:u64 = if args.len()>1 { args[1].parse().unwrap() } else { 16 };
    let wcap:usize = if args.len()>2 { args[2].parse().unwrap() } else { (n/2) as usize };
    let d=(n/2) as usize;
    println!("== wf-A08 2-adic Newton polygon root count: n={} d=phi={} ==", n, d);
    println!("   v_lambda(sigma_T) = v_2(N), lambda=1-zeta, (2)=lambda^{}, e={}", d, d);
    println!("   ANGLE: #{{configs : v_lambda >= V}} = 2-adic NP slice (Mann-blind)");
    println!();
    // enumerate antipodal-free signed configs on power basis x^0..x^{d-1}, coeff in {-1,0,1}, c[0]=1
    // (antipodal pair zeta^i, zeta^{i+d}=-zeta^i already collapsed onto the d power-basis indices)
    let mut histo:Vec<std::collections::BTreeMap<u32,u64>>=vec![Default::default();wcap+1];
    let mut maxv=vec![0u32;wcap+1];
    let mut total=vec![0u64;wcap+1];
    // recursion over coeffs[1..d] in {-1,0,1}, coeffs[0]=1
    let mut coeffs=vec![0i64;d]; coeffs[0]=1;
    fn rec(coeffs:&mut Vec<i64>,pos:usize,d:usize,used:usize,wcap:usize,
           histo:&mut Vec<std::collections::BTreeMap<u32,u64>>,maxv:&mut Vec<u32>,total:&mut Vec<u64>){
        if used>wcap { return; }
        if pos==d{
            let w=used; if w==0||w>wcap{return;}
            let nrm=det_negacyclic(coeffs,d);
            let v=nrm.v2();
            total[w]+=1;
            *histo[w].entry(v).or_insert(0)+=1;
            if v!=u32::MAX && v>maxv[w]{maxv[w]=v;}
            return;
        }
        for c in [0i64,1,-1]{
            coeffs[pos]=c;
            rec(coeffs,pos+1,d,used+ if c!=0 {1} else {0},wcap,histo,maxv,total);
        }
        coeffs[pos]=0;
    }
    rec(&mut coeffs,1,d,1,wcap,&mut histo,&mut maxv,&mut total);
    println!("   w | total | maxV | parity | v_lambda histogram (V:count)");
    for w in 1..=wcap{
        if total[w]==0{continue;}
        let par= if w%2==0 {"EVEN"} else {"ODD "};
        let h:Vec<String>=histo[w].iter().map(|(v,c)| if *v==u32::MAX {format!("INF:{}",c)} else {format!("{}:{}",v,c)}).collect();
        println!("   {} | {:>6} | {:>4} | {} | {}", w, total[w], maxv[w], par, h.join(" "));
    }
    // NP slice: cumulative #{v_lambda >= V} summed over all weights
    println!();
    println!("   NP cumulative slice over ALL weights: #{{v_lambda >= V}}");
    let mut allhist:std::collections::BTreeMap<u32,u64>=Default::default();
    let mut grand=0u64;
    for w in 1..=wcap{ for (v,c) in &histo[w]{ if *v!=u32::MAX{ *allhist.entry(*v).or_insert(0)+=c; grand+=c; } } }
    let maxV=*allhist.keys().max().unwrap_or(&0);
    let mut cum=grand;
    for V in 0..=maxV{
        let here=*allhist.get(&V).unwrap_or(&0);
        println!("      V={:2}: #{{=V}}={:>7}  #{{>=V}}={:>7}  frac>=V={:.5}", V, here, cum, cum as f64/grand as f64);
        cum-=here;
    }
}
