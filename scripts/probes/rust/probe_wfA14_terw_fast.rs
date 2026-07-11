// A14 fast confirmation: Terwilliger dim of Cay(F_p,mu_n) for n=4,8 (beta~4 prize regime),
// plus the analytic closed-form check  dim T ?= 1 + 2*m + m*(p-1)/(?)...
// We just measure dim T and fit it against p, m, and m*p.
//
// Optimization: closure done with a hard cap and early-out; primes kept small (p<=73).

fn mpow(mut _a:u64, mut e:u64, p:u64)->u64{let mut r=1u128;let mut a2=_a as u128;let pp=p as u128;while e>0{if e&1==1{r=r*a2%pp;}a2=a2*a2%pp;e>>=1;}r as u64}
fn is_prime(n:u64)->bool{if n<2{return false;}let mut d=2;while d*d<=n{if n%d==0{return false;}d+=1;}true}
fn primitive_root(p:u64)->u64{let mut m=p-1;let mut fs=vec![];let mut d=2;while d*d<=m{if m%d==0{fs.push(d);while m%d==0{m/=d;}}d+=1;}if m>1{fs.push(m);}let mut g=2;loop{if fs.iter().all(|&f|mpow(g,(p-1)/f,p)!=1){return g;}g+=1;}}

const L: u64 = 2_000_000_011;
fn minv(a:u64)->u64{ mpow(a, L-2, L) }

fn rank_rows(mut rows: Vec<Vec<u64>>, dim: usize) -> usize {
    let mut r = 0usize; let mut col = 0usize; let nrows = rows.len();
    while col < dim && r < nrows {
        let mut piv = None;
        for i in r..nrows { if rows[i][col]!=0 { piv=Some(i); break; } }
        if let Some(pi)=piv {
            rows.swap(r, pi);
            let inv = minv(rows[r][col]);
            for c in col..dim { rows[r][c] = (rows[r][c] as u128 * inv as u128 % L as u128) as u64; }
            for i in 0..nrows {
                if i!=r && rows[i][col]!=0 {
                    let f = rows[i][col];
                    for c in col..dim {
                        let sub = (rows[r][c] as u128 * f as u128 % L as u128) as u64;
                        rows[i][c] = (rows[i][c] + L - sub) % L;
                    }
                }
            }
            r += 1;
        }
        col += 1;
    }
    r
}
fn flat(m:&Vec<Vec<u64>>, p:usize)->Vec<u64>{
    let mut v=vec![0u64; p*p];
    for i in 0..p { for j in 0..p { v[i*p+j]=m[i][j]; } } v
}
fn matmul(a:&Vec<Vec<u64>>, b:&Vec<Vec<u64>>, p:usize)->Vec<Vec<u64>>{
    let mut c=vec![vec![0u64;p];p];
    for i in 0..p { for k in 0..p { let aik=a[i][k]; if aik==0 {continue;}
        for j in 0..p { if b[k][j]!=0 { c[i][j]=( (c[i][j] as u128 + aik as u128 * b[k][j] as u128) % L as u128) as u64; } } } }
    c
}

fn terw(n:u64,p:u64)->usize{
    let pu=p as usize; let g=primitive_root(p);
    let m=((p-1)/n) as usize;
    let mut dlog=vec![0usize;pu]; let mut x=1u64;
    for e in 0..(p-1){ dlog[x as usize]=e as usize; x=(x as u128*g as u128%p as u128) as u64; }
    let coset=|d:u64|->usize{ dlog[d as usize]%m };
    let mut a_rel:Vec<Vec<Vec<u64>>>=vec![vec![vec![0u64;pu];pu];m];
    for y in 0..pu { for z in 0..pu { if y==z {continue;} let d=(y as u64+p-z as u64)%p; a_rel[coset(d)][y][z]=1; } }
    let mut estar:Vec<Vec<Vec<u64>>>=Vec::new();
    { let mut d=vec![vec![0u64;pu];pu]; d[0][0]=1; estar.push(d); }
    for i in 0..m { let mut d=vec![vec![0u64;pu];pu]; for y in 1..pu { if dlog[y]%m==i { d[y][y]=1; } } estar.push(d); }
    let mut gens:Vec<Vec<Vec<u64>>>=Vec::new();
    { let mut id=vec![vec![0u64;pu];pu]; for i in 0..pu { id[i][i]=1; } gens.push(id); }
    for a in &a_rel { gens.push(a.clone()); }
    for e in &estar { gens.push(e.clone()); }
    // incremental row-echelon: keep reduced pivot rows; a new matrix increases dim iff its
    // reduced residual is nonzero. echelon rows stored sparsely as (pivot_col -> full row).
    let dim2 = pu*pu;
    let mut ech: Vec<(usize, Vec<u64>)> = Vec::new(); // sorted by pivot col
    let mut basis:Vec<Vec<Vec<u64>>>=Vec::new();
    // returns true if mtx is independent of current span (and updates echelon)
    let reduce_and_add = |mtx:&Vec<Vec<u64>>, ech:&mut Vec<(usize,Vec<u64>)>, basis:&mut Vec<Vec<Vec<u64>>>| -> bool {
        let mut v = flat(mtx, pu);
        for &(pc, ref row) in ech.iter() {
            if v[pc]!=0 {
                let f = v[pc];
                for c in pc..dim2 {
                    if row[c]!=0 {
                        let sub=(row[c] as u128 * f as u128 % L as u128) as u64;
                        v[c]=(v[c]+L-sub)%L;
                    }
                }
            }
        }
        // find new pivot
        let mut pc=None;
        for c in 0..dim2 { if v[c]!=0 { pc=Some(c); break; } }
        if let Some(p0)=pc {
            let inv=minv(v[p0]);
            for c in p0..dim2 { v[c]=(v[c] as u128*inv as u128%L as u128) as u64; }
            ech.push((p0, v));
            ech.sort_by_key(|x|x.0);
            basis.push(mtx.clone());
            true
        } else { false }
    };
    for gm in &gens { reduce_and_add(gm,&mut ech,&mut basis); }
    let mut changed=true; let mut it=0;
    while changed && it<15 { changed=false; it+=1;
        let snap:Vec<Vec<Vec<u64>>>=basis.clone();
        for b in &snap { for gm in &gens {
            let pr=matmul(b,gm,pu); if reduce_and_add(&pr,&mut ech,&mut basis){changed=true;}
            let pr2=matmul(gm,b,pu); if reduce_and_add(&pr2,&mut ech,&mut basis){changed=true;}
        }}
    }
    ech.len()
}

fn main(){
    eprintln!("# n  p  beta  m=(p-1)/n  dimT  dimT/p  (1+2m+m*(p-2))? ");
    let cases:Vec<(u64,u64)>=vec![(4,13),(4,29),(4,37),(4,53),(8,17),(8,41),(8,73)];
    for &(n,p) in &cases {
        if !is_prime(p)||(p-1)%n!=0 {continue;}
        let t=terw(n,p);
        let m=((p-1)/n) as usize;
        let beta=(p as f64).ln()/(n as f64).ln();
        // candidate analytic form for a Schurian translation scheme:
        // T spanned by E*_i A_R E*_j nonzero. quick descriptive fit value:
        let fit = 1 + 2*m + m*(p as usize -2);
        eprintln!("{:3} {:5} {:5.2}  {:4}   {:5}  {:6.3}  fit={}", n,p,beta,m,t,t as f64/p as f64, fit);
    }
}
