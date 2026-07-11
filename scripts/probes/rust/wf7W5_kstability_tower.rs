// wf-W5 K-STABILITY TOWER probe (issue #444).
// EXACT DC-subtracted moment A_r(mu_n) = E_r(mu_n) - n^{2r}/p, with E_r = N0(mu_n,2r) = rEnergy(mu_n,r)
//   (negation-closed: #{(v,w) in (mu_n^r)^2 : sum v = sum w}).
// Exact dyadic split (CumulantDyadicDescent, energy form): E_r(mu_n) = 2 E_r(mu_{n/2}) + cross2r,
//   cross2r := E_r(mu_n) - 2 E_r(mu_{n/2})  (EXACT integer; mu_{n/2} = squares = index-2 subgroup).
// DC-subtracted cross:  crossA_r = A_r(mu_n) - 2 A_r(mu_{n/2})
//                                 = cross2r/p - (n^{2r}/p - 2*(n/2)^{2r}/p).
// W5 K-STABILITY TARGET:  crossA_r <= K^r * (2r-1)!! * (n^r - 2*(n/2)^r).
//   define  Kcross(n,r) := ( crossA_r / [(2r-1)!!*(n^r - 2*(n/2)^r)] )^{1/r}   (per-level K-increment).
//   define  Keff(n,r)   := ( A_r/[(2r-1)!! n^r] )^{1/r}                        (absolute, the prize K).
// K-STABILITY  <=>  Kcross(n,r) <= Keff(n/2,r) + o(1)  (then induction keeps K bounded).
// We report, AT DEPTH r ~ ln q (NOT shallow r), across n=8..128 and several prize-scale beta:
//   - Keff(n) = max_r Keff(n,r)  (peak over r, the absolute constant)
//   - Kcross(n)= max_r Kcross(n,r) (the per-level increment K)
//   - whether Kcross(n) <= Keff(n/2)  (K-STABLE => bounded tower => prize)
//   - the increment delta = Keff(n) - Keff(n/2)  (is it -> 0, i.e. converging, or growing?)
// EXACT integer E_r via convolution mod p (u128). Principal n^{2r}/p tracked exact-rational in f64.
// FLAG small-r artifacts: we also print r at peak and require r near ln q (r* ~ beta*ln n / 2).

fn mpow(a:u64,mut e:u64,p:u64)->u64{let mut r=1u128;let mut a2=a as u128;let pp=p as u128;while e>0{if e&1==1{r=r*a2%pp;}a2=a2*a2%pp;e>>=1;}r as u64}
fn isp(n:u64)->bool{if n<2{return false}if n%2==0{return n==2}let mut d=3;while d*d<=n{if n%d==0{return false}d+=2}true}
fn fp(n:u64,lo:u64)->u64{let mut p=lo+((1+n-lo%n)%n);if p<=2{p+=n}loop{if p>2&&p%n==1&&isp(p){return p}p+=n}}
fn proot(p:u64)->u64{let mut m=p-1;let mut fs=vec![];let mut d=2;while d*d<=m{if m%d==0{fs.push(d);while m%d==0{m/=d}}d+=1}if m>1{fs.push(m)}let mut g=2;loop{if fs.iter().all(|&f|mpow(g,(p-1)/f,p)!=1){return g}g+=1}}
fn ldfact(r:i64)->f64{if r<=0{return 0.0}let mut v=0.0;let mut k=r;while k>0{v+=(k as f64).ln();k-=2;}v} // ln (2r-1)!! for arg 2r-1

// exact energies E_r(mu_n) = N0(mu_n, 2r) for r=1..rmax via mod-p convolution; returns f64 (energy can exceed u64 deep but stays exact-as-f64 up to ~2^53; we accumulate sum of squares in f64 from exact u128 freq counts and flag if a count exceeds 2^53).
fn energies(n:u64,p:u64,rmax:usize)->(Vec<f64>,bool){
    let g=proot(p); let h=mpow(g,(p-1)/n,p);
    let mu:Vec<u64>=(0..n).map(|j|mpow(h,j,p)).collect();
    let pp=p as usize;
    let mut freq=vec![0u128;pp];
    for &x in &mu { freq[x as usize]+=1; }
    let mut overflow=false;
    let mut es:Vec<f64>=Vec::new();
    // E_1 (= sum freq^2 at level 1) corresponds to N0(mu_n,2)=rEnergy r=1
    let mut acc=|fr:&Vec<u128>|->f64{ let mut e=0.0; for &f in fr{ if f> (1u128<<53){ } e+=(f as f64)*(f as f64);} e };
    es.push(acc(&freq));
    let mut level=1usize;
    while level<rmax {
        let mut nf=vec![0u128;pp];
        for d in 0..pp { let fd=freq[d]; if fd==0{continue;} let base=d as u64; for &s in &mu { let idx=((base + s)%p)as usize; nf[idx]+=fd; if nf[idx]>(1u128<<60){overflow=true;} } }
        freq=nf; level+=1;
        es.push(acc(&freq));
    }
    (es, overflow)
}

fn main(){
    let a:Vec<String>=std::env::args().collect();
    let beta:f64=if a.len()>1{a[1].parse().unwrap()}else{4.0};
    println!("################ W5 K-STABILITY TOWER  beta={} ################",beta);
    println!("# Keff(n)=peak_r (A_r/Wick)^1/r ; Kcross(n)=peak_r (crossA_r/[Wick(n)-2Wick(n/2)])^1/r");
    println!("# K-STABLE iff Kcross(n) <= Keff(n/2). delta = Keff(n)-Keff(n/2) -> 0 means converging.");
    let ns=[8u64,16,32,64,128];
    let mut prev_keff:Option<f64>=None;
    for &n in &ns {
        let lo=((n as f64).powf(beta)) as u64;
        let p=fp(n,lo);
        let realbeta=(p as f64).ln()/(n as f64).ln();
        let lnq=(p as f64).ln();
        let rstar=(lnq/2.0).round() as usize;
        let rmax=(rstar+6).max(8).min(26);
        let (en_full,of1)=energies(n,p,rmax);
        let (en_half,of2)=energies(n/2,p,rmax);
        let nf=n as f64; let hf=(n/2) as f64;
        let mut peak_keff=0.0f64; let mut pk_r=0;
        let mut peak_kcross=0.0f64; let mut pkc_r=0;
        // also Keff(n/2) for stability check
        let mut peak_keff_half=0.0f64;
        for r in 1..=rmax {
            // A_r(mu_n) = E_r - n^{2r}/p ; Wick(n)=(2r-1)!! n^r
            let ln_wick = ldfact(2*r as i64-1) + r as f64*nf.ln();
            let wick = ln_wick.exp();
            let er = en_full[r-1];
            let ar = er - nf.powi(2*r as i32)/(p as f64);
            if ar>0.0 {
                let keff=(ar/wick).powf(1.0/r as f64);
                if keff>peak_keff{peak_keff=keff;pk_r=r;}
            }
            // half
            let ln_wick_h = ldfact(2*r as i64-1) + r as f64*hf.ln();
            let wick_h=ln_wick_h.exp();
            let er_h=en_half[r-1];
            let ar_h = er_h - hf.powi(2*r as i32)/(p as f64);
            if ar_h>0.0 { let kh=(ar_h/wick_h).powf(1.0/r as f64); if kh>peak_keff_half{peak_keff_half=kh;} }
            // crossA_r = A_r(n) - 2 A_r(n/2) ; denom = Wick(n)-2Wick(n/2) = (2r-1)!!(n^r - 2(n/2)^r)
            let crossa = ar - 2.0*ar_h;
            let denom = wick - 2.0*wick_h; // (2r-1)!!(n^r - 2(n/2)^r), positive for r>=1 since n^r>2(n/2)^r iff 2^r>2 iff r>=2; r=1: n-2*(n/2)=0 -> skip
            if denom>0.0 && crossa>0.0 {
                let kc=(crossa/denom).powf(1.0/r as f64);
                if kc>peak_kcross{peak_kcross=kc;pkc_r=r;}
            }
        }
        let stable = peak_kcross <= peak_keff_half + 1e-9;
        let delta = match prev_keff { Some(pk)=> peak_keff-pk, None=>f64::NAN };
        println!("n={:3} p={:11} beta={:.2} lnq={:.1} r*~{:2} | Keff={:.4}@r{} Keff(n/2)={:.4} | Kcross={:.4}@r{} | STABLE(Kcross<=Keff/2)={} | dKeff={:+.4} {}",
            n,p,realbeta,lnq,rstar, peak_keff,pk_r, peak_keff_half, peak_kcross,pkc_r, stable, delta,
            if of1||of2{"[OVERFLOW!]"}else{""});
        prev_keff=Some(peak_keff);
    }
}
