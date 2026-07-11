// For each n, find the SMALLEST prime p=1 mod n with spur(n)>0 (first short antipodal-free relation
// of n-th roots mod p). Compare to n^4 (prize), 2^n (exact-energy threshold), and (2r)^{n/2}=4^{n/2}.
fn mpow(a:u64,mut e:u64,p:u64)->u64{let mut r=1u128;let mut a2=a as u128;let pp=p as u128;while e>0{if e&1==1{r=r*a2%pp;}a2=a2*a2%pp;e>>=1;}r as u64}
fn isp(n:u64)->bool{if n<2{return false}if n%2==0{return n==2}let mut d=3;while d*d<=n{if n%d==0{return false}d+=2}true}
fn proot(p:u64)->u64{let mut m=p-1;let mut fs=vec![];let mut d=2;while d*d<=m{if m%d==0{fs.push(d);while m%d==0{m/=d}}d+=1}if m>1{fs.push(m)}let mut g=2;loop{if fs.iter().all(|&f|mpow(g,(p-1)/f,p)!=1){return g}g+=1}}
use std::collections::HashMap;
fn e2(hgen:u64,sz:u64,p:u64)->u128{let mu:Vec<u64>=(0..sz).map(|j|mpow(hgen,j,p)).collect();let mut c:HashMap<u64,u128>=HashMap::new();for &x in &mu{for &y in &mu{*c.entry((x+y)%p).or_insert(0)+=1;}}let mut e=0u128;for(_,&v)in &c{e+=v*v;}e}
fn main(){
    println!("# smallest prime p=1 mod n with spur(n)>0 vs n^4 (prize) and 2^n (exact thresh)");
    for &n in &[4u64,8,16,32,64,128,256]{
        let mut p = 1+n;
        let mut first=0u64;
        while p < (1u64<<40) {
            if isp(p) {
                let g=proot(p); let h=mpow(g,(p-1)/n,p);
                let en=e2(h,n,p) as i128;
                let sp=en-(3*(n as i128)*(n as i128)-3*(n as i128));
                if sp>0 { first=p; break; }
            }
            p+=n;
        }
        let n4=(n as f64).powf(4.0);
        let twon = if n<=40 {(2f64).powf(n as f64)} else {f64::INFINITY};
        println!("n={:4}: first spur>0 prime = {:12} | n^4={:.2e} 2^n={:.2e} | spur-prime/n^4 = {:.2}",
            n, first, n4, twon, first as f64/n4);
    }
}
