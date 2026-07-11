export const meta = {
  name: 'review-444-comments',
  description: 'Review all 283 #444 comments, extract findings, verify key claims, synthesize the dossier update',
  phases: [
    { title: 'Extract', detail: 'one agent per comment chunk — structured findings' },
    { title: 'Verify', detail: 'adversarially re-check the high-value + suspicious claims (prize-regime)' },
    { title: 'Synthesize', detail: 'merge into the master findings ledger' },
  ],
}

const CHUNKDIR = '/tmp/issue444/chunks'
const ROOT = '/Users/shawwalters/ethereumroadmap/upstream/lean-research/ArkLib'

// 21 chunk files
const CHUNKS = Array.from({length: 21}, (_, i) => `chunk${String(i+1).padStart(2,'0')}.md`)

const FINDING_SCHEMA = {
  type:'object', additionalProperties:false,
  required:['chunk','openAvenues','goodResults','badResults','suspicious','propsToSolve','summary'],
  properties:{
    chunk:{type:'string'},
    openAvenues:{type:'array', items:{type:'object', additionalProperties:false,
      required:['title','detail','prizeRegime'],
      properties:{title:{type:'string'}, detail:{type:'string'},
        prizeRegime:{type:'string', description:'is it tested/testable in the prize regime? untested/promising/testable/not-applicable'},
        commentId:{type:'string'}}}},
    goodResults:{type:'array', items:{type:'object', additionalProperties:false,
      required:['title','detail','holdsInPrizeRegime'],
      properties:{title:{type:'string'}, detail:{type:'string'},
        holdsInPrizeRegime:{type:'boolean'}, commentId:{type:'string'}}}},
    badResults:{type:'array', items:{type:'object', additionalProperties:false,
      required:['title','whyFailed','retestableInPrizeRegime'],
      properties:{title:{type:'string'}, whyFailed:{type:'string'},
        retestableInPrizeRegime:{type:'string', description:'could this be re-tested/salvaged in the prize regime, and how? or definitively dead'},
        commentId:{type:'string'}}}},
    suspicious:{type:'array', items:{type:'object', additionalProperties:false,
      required:['claim','concern'],
      properties:{claim:{type:'string'},
        concern:{type:'string', description:'laundered/lied value, bug, cannot-be-true, vacuous, circular, unverified'},
        commentId:{type:'string'}}}},
    propsToSolve:{type:'array', items:{type:'object', additionalProperties:false,
      required:['name','statement'],
      properties:{name:{type:'string'}, statement:{type:'string'}, commentId:{type:'string'}}}},
    summary:{type:'string'},
  },
}

const EXTRACT_GUIDE = `You are reviewing a chunk of GitHub comments from issue #444 (the ArkLib RS proximity-gap
prize, proving δ* — the mutual-correlated-agreement / list-decoding threshold for explicit dyadic
Reed-Solomon codes in the prize regime n=2^μ~2^30, q=n^β, ε*=2^-128, window interior between
Johnson 1-√ρ and capacity 1-ρ). The comments are live research notes by the user (lalalune) and
agents (0xSolace et al). Many results are deep; some are refuted; some are buried; some may have
errors or overclaimed/laundered values.

Read your assigned chunk file carefully and EXTRACT, with the comment id for traceability:
1. openAvenues — every avenue NOT fully tried/tested, promising-but-missed, or buried. For each,
   note whether it was tested in the PRIZE REGIME (n=2^μ thin, β≈4-5) or only a toy/proxy regime.
2. goodResults — solid results that HOLD. Flag which hold specifically in the PRIZE REGIME. Examples
   to watch for: di Benedetto beat (subgroup char-sum exponent improvement), exact δ* values, the
   asymptotic δ* curve / cascade, p-INDEPENDENCE of δ*, orbit-count crossing law, FFT-graded
   recursion, monomial-worst, determinantal/Plücker bound, BCHKS-1.12 reduction.
3. badResults — refuted/failed approaches. For EACH, judge: could it be RE-TESTED or salvaged in the
   PRIZE REGIME (and how), or is it definitively dead? The user specifically wants bad results
   double-checked for prize-regime testability.
4. suspicious — any claim that looks laundered/lied (a value asserted without computation, a number
   that changed silently, a "proven" that isn't), a BUG, something that cannot be true, a vacuous/
   circular/overclaimed statement, or an unverified-but-cited result. Be skeptical and specific.
5. propsToSolve — any named Prop / axiom / open obligation / conjecture stated that we should solve.

Be precise and cite comment ids. Do not invent; only extract what is in the chunk. If the chunk has
little of value, say so honestly (short arrays are fine).`

function chunk(a,n){const o=[];for(let i=0;i<a.length;i+=n)o.push(a.slice(i,i+n));return o}
async function waved(items, mk, label, width){
  let acc=[]
  for (const [i,w] of chunk(items, width||6).entries()){
    log(`${label} wave ${i+1}/${Math.ceil(items.length/(width||6))} (${w.length} items)`)
    acc=acc.concat(await pipeline(w, mk))
  }
  return acc
}

phase('Extract')
const extracted = await waved(CHUNKS, (cf) => agent(
  `${EXTRACT_GUIDE}

Your chunk file: ${CHUNKDIR}/${cf}
Read it with the Read tool (it is ~45K, read the whole thing). Return the structured findings for chunk ${cf}.`,
  {label:`extract:${cf}`, phase:'Extract', schema:FINDING_SCHEMA}
), 'Extract', 6)

// flatten all findings
const all = extracted.filter(Boolean)
const allGood = all.flatMap(r => (r.goodResults||[]).map(g=>({...g, chunk:r.chunk})))
const allOpen = all.flatMap(r => (r.openAvenues||[]).map(o=>({...o, chunk:r.chunk})))
const allBad = all.flatMap(r => (r.badResults||[]).map(b=>({...b, chunk:r.chunk})))
const allSus = all.flatMap(r => (r.suspicious||[]).map(s=>({...s, chunk:r.chunk})))
const allProps = all.flatMap(r => (r.propsToSolve||[]).map(p=>({...p, chunk:r.chunk})))
log(`Extracted: ${allGood.length} good, ${allOpen.length} open avenues, ${allBad.length} bad, ${allSus.length} suspicious, ${allProps.length} props`)

// Pick the highest-value claims to adversarially verify: prize-regime good results + ALL suspicious +
// bad results flagged re-testable. Cap to keep it bounded.
const prizeGood = allGood.filter(g => g.holdsInPrizeRegime).slice(0, 24)
const retestable = allBad.filter(b => /test|salvage|prize|could|yes|maybe/i.test(b.retestableInPrizeRegime||'')).slice(0, 16)
const susTop = allSus.slice(0, 24)

const VERIFY_SCHEMA = {
  type:'object', additionalProperties:false,
  required:['claim','verdict','reason'],
  properties:{
    claim:{type:'string'},
    kind:{type:'string'},
    verdict:{type:'string', enum:['CONFIRMED','REFUTED','UNVERIFIABLE','OVERCLAIMED','RETEST_WORTHWHILE','LAUNDERED']},
    reason:{type:'string'},
    prizeRegimeStatus:{type:'string', description:'precise: holds in prize regime / only in toy / untested / numerically out of reach'},
  },
}

const VERIFY_GUIDE = `You are an ADVERSARIAL verifier for the #444 prize program (ArkLib, dir ${ROOT}).
You have a claim extracted from the issue comments. Determine if it is TRUE and whether it holds in
the PRIZE REGIME (thin dyadic μ_n, n=2^μ, q=n^β β≈4-5, ε*=2^-128). Tools: read the relevant Lean
bricks under ArkLib/Data/CodingTheory/ProximityGap/ (and Frontier/_Bridge*, _Core*, _Close*), the
docs/kb dossiers, run scripts/probes/probe_*.py or scripts/rust-pg binaries for exact small-n
computation, and #print axioms via scripts/pg-iterate.sh for any cited Lean result. Memory of the
project says ~all analytic routes reduce to the BGK/BCHKS wall; the genuinely-established results
are: di Benedetto exponent beat for 2-power subgroups (0.9892→0.9583), δ* p-INDEPENDENCE (exact
incidence identical across primes p>n^4), exact δ* pins (F5, F17, granularity ladder), the
orbit-count crossing law, and the complete TIGHT reduction prize⟺BCHKS-1.12. Be skeptical: confirm
numbers by computation where feasible; flag any laundered/overclaimed value. Verdicts:
CONFIRMED / REFUTED / OVERCLAIMED / LAUNDERED (value asserted w/o basis) / UNVERIFIABLE /
RETEST_WORTHWHILE (a bad result that genuinely deserves a prize-regime re-test).`

phase('Verify')
const toVerify = [
  ...prizeGood.map(g => ({kind:'prize-good', text:`${g.title}: ${g.detail}`})),
  ...retestable.map(b => ({kind:'retest-bad', text:`${b.title} (failed: ${b.whyFailed}). Re-testable? ${b.retestableInPrizeRegime}`})),
  ...susTop.map(s => ({kind:'suspicious', text:`${s.claim} — CONCERN: ${s.concern}`})),
]
const verified = await waved(toVerify, (v) => agent(
  `${VERIFY_GUIDE}

CLAIM TO VERIFY [${v.kind}]:
${v.text}

Investigate with the tools, then return your verdict.`,
  {label:`verify:${v.kind}`, phase:'Verify', schema:VERIFY_SCHEMA}
), 'Verify', 6)

phase('Synthesize')
const vv = verified.filter(Boolean)
return {
  counts:{good:allGood.length, open:allOpen.length, bad:allBad.length, suspicious:allSus.length, props:allProps.length, verified:vv.length},
  goodResults: allGood,
  openAvenues: allOpen,
  badResults: allBad,
  suspicious: allSus,
  propsToSolve: allProps,
  verifications: vv,
  perChunkSummaries: all.map(r=>({chunk:r.chunk, summary:r.summary})),
}
