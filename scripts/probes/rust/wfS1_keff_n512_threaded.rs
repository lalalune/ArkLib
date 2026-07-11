// Threaded K_eff at n=512 (beta=4): does (E_r/Wick)^{1/r} stay ~0.64?
use std::f64::consts::PI; use std::sync::Arc; use std::thread;
fn mpow(a:u64,mut e:u64,p:u64)->u64{let mut r=1u128;let mut b=a as u128;let pp=p as u128;while e>0{if e&1==1{r=r*b%pp}b=b*b%pp;e>>=1}r as u64}
fn isp(n:u64)->bool{if n<2{return false}let mut d=2u64;while (d as u128)*(d as u128)<=n as u128{if n%d==0{return false}d+=1}true}
fn fp(n:u64,lo:u64)->u64{let mut p=lo+((1+n-lo%n)%n);if p<=2{p+=n}loop{if p>2&&p%n==1&&isp(p){return p}p+=n}}
fn proot(p:u64)->u64{let mut m=p-1;let mut fs=vec![];let mut d=2;while d*d<=m{if m%d==0{fs.push(d);while m%d==0{m/=d}}d+=1}if m>1{fs.push(m)}let mut g=2;loop{if fs.iter().all(|&f|mpow(g,(p-1)/f,p)!=1){return g}g+=1}}
fn v2(mut x:u64)->u32{let mut v=0;while x&1==0{v+=1;x>>=1}v}
fn lpf(mut x:u64)->u64{let mut l=1;let mut d=2;while d*d<=x{while x%d==0{l=d;x/=d}d+=1}if x>1{l=x}l}
fn dfact(r:usize)->f64{let mut v=1.0;for j in 1..=r{v*=(2*j-1)as f64}v}
const RS:[usize;9]=[2,3,5,8,12,16,20,24,28];
fn run(n:u64,p:u64,tag:&str){
    let g=proot(p); let h=mpow(g,(p-1)/n,p);
    let mu:Arc<Vec<u64>>=Arc::new((0..n).map(|j|mpow(h,j,p)).collect());
    let m=(p-1)/n; let gn=mpow(g,n,p);
    let nth=10u64; let pp=p;
    let mut hs=vec![];
    for t in 0..nth {
        let mu=mu.clone();
        hs.push(thread::spawn(move||{
            let mut acc=[0.0f64;9];
            // b starts at g^(n*t), step g^(n*nth)
            let mut b=mpow(gn,t,pp);
            let step=mpow(gn,nth,pp);
            let mut idx=t;
            while idx<m {
                let mut re=0.0; for &x in mu.iter(){let prod=((b as u128*x as u128)%pp as u128)as u64; re+=(2.0*PI*(prod as f64)/pp as f64).cos();}
                let e2=re*re; let mut pw=1.0;
                // accumulate re^{2r} for r in RS
                for (k,&r) in RS.iter().enumerate(){ acc[k]+=re.powi(2*r as i32); }
                let _=(e2,pw);
                b=((b as u128*step as u128)%pp as u128)as u64; idx+=nth;
            }
            acc
        }));
    }
    let mut sum=[0.0f64;9]; for hnd in hs{let a=hnd.join().unwrap(); for k in 0..9{sum[k]+=a[k];}}
    print!("{} n={} p={} v2={} lpf={} beta={:.2} | Keff_Wick: ",tag,n,p,v2(p-1),lpf((p-1)/n),(p as f64).ln()/(n as f64).ln());
    let mut maxk=0.0f64;
    for (k,&r) in RS.iter().enumerate(){let er=sum[k]/(p as f64); let kk=(er/(dfact(r)*(n as f64).powi(r as i32))).powf(1.0/r as f64); if kk>maxk{maxk=kk} print!("r{}={:.2} ",r,kk);}
    println!("| MAXK={:.3}",maxk);
}
fn main(){
    println!("== n=512, beta=4 (threaded) ==");
    run(512, fp(512, 68719476736), "good ");
    let mut p=fp(512,68719476736); for _ in 0..8000 { let q=fp(512,p+1); if v2(q-1)>=18 {run(512,q,"hi-v2"); break;} p=q; }
}
