import { Section } from "@/components/Section";
import { MiningRig } from "@/components/MiningRig";
import { Frontier } from "@/components/Frontier";
import { Campaign } from "@/components/Campaign";
import { Prove } from "@/components/Prove";
import { Moat } from "@/components/Moat";
import { M } from "@/components/Math";

const DELTASTAR = "https://deltastar.computer";
const CONTACT = "mailto:shadow@shad0w.xyz?subject=Commission%20a%20Truth%20Mining%20campaign";

export default function Page() {
  return (
    <main className="relative">
      {/* ============================ NAV ============================ */}
      <header className="col flex items-center justify-between pt-7 pb-2 relative z-10">
        <div className="flex items-center gap-2.5">
          <span
            className="inline-block rounded-[3px]"
            style={{
              width: "0.85rem",
              height: "0.85rem",
              background: "var(--ok)",
              boxShadow: "0 0 16px -2px var(--ok-glow)",
            }}
          />
          <span className="mono text-[0.82rem]" style={{ letterSpacing: "0.02em" }}>
            truth&#8202;mining
          </span>
        </div>
        <nav className="hidden sm:flex items-center gap-7 mono text-[0.74rem]" style={{ color: "var(--ink-2)" }}>
          <a className="link" href="#proof" style={{ textDecorationColor: "transparent" }}>
            the proof
          </a>
          <a className="link" href="#campaign" style={{ textDecorationColor: "transparent" }}>
            the campaign
          </a>
          <a className="link" href="#prove" style={{ textDecorationColor: "transparent" }}>
            what we prove
          </a>
          <a className="btn btn-ghost" href={CONTACT}>
            commission
          </a>
        </nav>
      </header>

      {/* ============================ HERO ============================ */}
      <section className="relative col" style={{ paddingTop: "clamp(3.5rem, 9vw, 7rem)", paddingBottom: "clamp(3rem, 7vw, 5rem)" }}>
        <div className="field-grid" style={{ height: "120%" }} />
        <div className="relative grid lg:grid-cols-[1.15fr_0.85fr] gap-12 lg:gap-16 items-center">
          <div>
            <p className="eyebrow rise d1 mb-6">formal verification, mined</p>
            <h1
              className="display rise d2"
              style={{ fontSize: "clamp(2.7rem, 7vw, 5rem)" }}
            >
              Spend compute
              <br />
              to prove what&#8217;s{" "}
              <span style={{ color: "var(--ok)" }}>true.</span>
            </h1>
            <p
              className="rise d3 mt-7 measure text-[1.12rem]"
              style={{ color: "var(--ink-2)", lineHeight: 1.55 }}
            >
              An agent fleet mines a hard formal target against a cheap
              trustless verifier. What comes back is not{" "}
              <span style={{ color: "var(--ink)" }}>probably right</span>. It is
              kernel-certified. We mined a 25-year-open problem this way. Now we
              do it on commission, for crypto code.
            </p>
            <div className="rise d4 mt-9 flex flex-wrap items-center gap-3">
              <a className="btn btn-primary" href={CONTACT}>
                commission a campaign →
              </a>
              <a className="btn btn-ghost" href={DELTASTAR}>
                read the δ* proof
              </a>
            </div>
            <p className="rise d5 mono text-[0.7rem] mt-7" style={{ color: "var(--ink-3)" }}>
              first mined truth · 25-year-open problem · ~150 kernel-checked bricks · one night
            </p>
          </div>

          <div className="rise d3">
            <MiningRig />
          </div>
        </div>
      </section>

      <div className="col">
        <hr className="rule" />
      </div>

      {/* ========================= THE EXISTENCE PROOF ========================= */}
      <Section id="proof" eyebrow="01 / the existence proof · this happened">
        <div className="grid lg:grid-cols-[1.1fr_0.9fr] gap-10 lg:gap-16 items-start">
          <div>
            <h2 style={{ fontSize: "clamp(1.7rem, 3.8vw, 2.6rem)", lineHeight: 1.06 }}>
              In one night, an agent fleet mined a{" "}
              <span style={{ color: "var(--ok)" }}>25-year-open</span> problem.
            </h2>
            <p className="mt-6 measure text-[1.06rem]" style={{ color: "var(--ink-2)" }}>
              The target was <M>{"\\delta^*"}</M>, the
              mutual-correlated-agreement threshold for Reed&#8211;Solomon
              proximity testing. The open question behind a{" "}
              <span style={{ color: "var(--ink)" }}>$1M</span> Ethereum
              Foundation prize.
            </p>
            <p className="mt-4 measure text-[1.06rem]" style={{ color: "var(--ink-2)" }}>
              ~150 commits of Lean 4: kernel-checked theorems, honest
              refutations, an audit-guard that caught its own false positives.
              When the kernel rejected a claim, the fleet reversed it. Every
              accepted result typechecked.
            </p>

            <a
              className="link mono text-[0.82rem] inline-flex items-center gap-2 mt-7"
              href={DELTASTAR}
            >
              the first mined truth → deltastar.computer
            </a>
          </div>

          {/* proven vs lead magnet, the honesty split */}
          <div className="grid gap-4">
            <div className="brick brick-ok p-6">
              <span className="chip chip-ok mb-4">
                <span className="dot" /> proven
              </span>
              <p className="text-[1.0rem]" style={{ color: "var(--ink)" }}>
                Point an agent fleet at a hard formal problem with a cheap
                trustless verifier, and the results come back kernel-certified,
                not &ldquo;probably right.&rdquo; The verifier cannot be fooled.
              </p>
            </div>
            <div className="brick p-6">
              <span className="chip chip-no mb-4">
                <span className="dot" /> the lead magnet
              </span>
              <p className="text-[0.98rem]" style={{ color: "var(--ink-2)" }}>
                The prize is how you find us. The business is the same engine
                pointed at code that has to be correct.
              </p>
            </div>
          </div>
        </div>
      </Section>

      <div className="col">
        <hr className="rule" />
      </div>

      {/* ========================= THE PRINCIPLE ========================= */}
      <Section id="principle" eyebrow="02 / the principle">
        <div className="grid lg:grid-cols-[0.9fr_1.1fr] gap-10 lg:gap-16">
          <div>
            <h2 style={{ fontSize: "clamp(1.7rem, 3.6vw, 2.5rem)", lineHeight: 1.08 }}>
              Proof-of-work, where the work is real.
            </h2>
            <div
              className="mt-7 p-5 rounded-lg hidden lg:block"
              style={{ border: "1px solid var(--rule)", background: "var(--bg-raised)" }}
            >
              <p className="mono text-[0.7rem] mb-3" style={{ color: "var(--ink-3)" }}>
                not Bittensor for research. the inverse.
              </p>
              <div className="grid grid-cols-2 gap-px mono text-[0.78rem]">
                <div className="pr-4">
                  <p style={{ color: "var(--ink-3)" }}>validator</p>
                  <p className="mt-1" style={{ color: "var(--no)" }}>a vote</p>
                </div>
                <div className="pl-4" style={{ borderLeft: "1px solid var(--rule)" }}>
                  <p style={{ color: "var(--ink-3)" }}>validator</p>
                  <p className="mt-1" style={{ color: "var(--ok)" }}>a kernel</p>
                </div>
                <div className="pr-4 mt-3">
                  <p style={{ color: "var(--ink-3)" }}>incentive</p>
                  <p className="mt-1" style={{ color: "var(--no)" }}>to fake</p>
                </div>
                <div className="pl-4 mt-3" style={{ borderLeft: "1px solid var(--rule)" }}>
                  <p style={{ color: "var(--ink-3)" }}>incentive</p>
                  <p className="mt-1" style={{ color: "var(--ok)" }}>nothing to fake</p>
                </div>
              </div>
            </div>
          </div>
          <div className="measure">
            <p className="text-[1.06rem]" style={{ color: "var(--ink-2)" }}>
              Bitcoin burns energy to produce a number that proves only that
              energy was burned. A Lean proof has the same shape, for free:
              expensive to produce, trivial to verify, impossible to fake. No
              partial credit, no social consensus, no oracle to bribe.
            </p>

            <div
              className="brick mt-7 p-6"
              style={{ borderColor: "var(--rule)" }}
            >
              <p className="text-[1.04rem]" style={{ color: "var(--ink)" }}>
                You cannot forge a proof past the kernel any more than you can
                forge a hash past SHA-256.
              </p>
              <p className="mono text-[0.74rem] mt-3" style={{ color: "var(--ink-3)" }}>
                the kernel is the consensus mechanism and the trust layer
              </p>
            </div>

            <p className="mt-6 text-[1.06rem]" style={{ color: "var(--ink-2)" }}>
              Bittensor&#8217;s hardest problem is trusting a miner when quality
              is subjective. Math erases it. The bounty is the block reward, the
              kernel is the gate, and the block is a theorem someone wanted.
            </p>
          </div>
        </div>
      </Section>

      <div className="col">
        <hr className="rule" />
      </div>

      {/* ========================= THE CAMPAIGN (the product) ========================= */}
      <Section id="campaign" eyebrow="03 / the product is a campaign">
        <div className="grid lg:grid-cols-[0.85fr_1.15fr] gap-10 lg:gap-14 mb-10 items-end">
          <h2 style={{ fontSize: "clamp(1.7rem, 3.8vw, 2.6rem)", lineHeight: 1.06 }}>
            Set the bar before we run. Then run the command.
          </h2>
          <p className="measure text-[1.04rem]" style={{ color: "var(--ink-2)" }}>
            A campaign is the unit of delivery. You give a formal target, an
            acceptance criterion frozen in advance, and a fee. You get back a
            Lean repo and a one-command re-verify. You trust nothing about us.
          </p>
        </div>
        <Campaign />
      </Section>

      <div className="col">
        <hr className="rule" />
      </div>

      {/* ========================= WHAT WE PROVE (the market) ========================= */}
      <Section id="prove" eyebrow="04 / what we prove, for money">
        <div className="grid lg:grid-cols-[0.85fr_1.15fr] gap-10 lg:gap-14 mb-10 items-end">
          <h2 style={{ fontSize: "clamp(1.7rem, 3.8vw, 2.6rem)", lineHeight: 1.06 }}>
            The prize is the lead magnet. The business is crypto code.
          </h2>
          <p className="measure text-[1.04rem]" style={{ color: "var(--ink-2)" }}>
            Buyers already pay human FV shops to verify ZK circuits and
            contracts. A kernel-checked proof is a better artifact than a PDF of
            findings, and cheaper to produce.
          </p>
        </div>
        <Prove />
      </Section>

      <div className="col">
        <hr className="rule" />
      </div>

      {/* ========================= THE MOAT ========================= */}
      <Section id="moat" eyebrow="05 / the moat is not the miners">
        <div className="grid lg:grid-cols-[0.85fr_1.15fr] gap-10 lg:gap-14 mb-10 items-end">
          <h2 style={{ fontSize: "clamp(1.7rem, 3.6vw, 2.5rem)", lineHeight: 1.08 }}>
            The edge is the guard and the frontier.
          </h2>
          <p className="measure text-[1.04rem]" style={{ color: "var(--ink-2)" }}>
            The kernel makes a proof trustless. The audit-guard makes sure it
            proves the thing you asked for. The miners are rented and
            replaceable, and we say so.
          </p>
        </div>
        <Moat />
      </Section>

      <div className="col">
        <hr className="rule" />
      </div>

      {/* ========================= THE FRONTIER ========================= */}
      <Section id="frontier" eyebrow="06 / the verifier frontier · the roadmap">
        <div className="grid lg:grid-cols-[0.85fr_1.15fr] gap-10 lg:gap-14 mb-10 items-end">
          <h2 style={{ fontSize: "clamp(1.7rem, 3.6vw, 2.5rem)", lineHeight: 1.08 }}>
            The verifier is the whole game.
          </h2>
          <p className="measure text-[1.04rem]" style={{ color: "var(--ink-2)" }}>
            Any domain with a cheap trustless verifier is mineable. Math is
            perfect, the beachhead. Crypto is the commercial step. Empirical
            science is off the frontier, and naming that boundary is the
            credibility.
          </p>
        </div>
        <Frontier />
      </Section>

      {/* ============================ CTA ============================ */}
      <section
        id="contact"
        className="relative"
        style={{ paddingBlock: "clamp(4.5rem, 10vw, 8rem)" }}
      >
        <div className="field-grid" style={{ top: "auto", bottom: 0, height: "120%", transform: "scaleY(-1)" }} />
        <div className="col relative text-center">
          <p className="eyebrow mb-6">a false truth does not typecheck</p>
          <h2
            className="display mx-auto"
            style={{ fontSize: "clamp(2rem, 5.5vw, 3.6rem)", maxWidth: "18ch" }}
          >
            Commission a proof you can re-check yourself.
          </h2>
          <p
            className="mx-auto mt-6 text-[1.08rem]"
            style={{ color: "var(--ink-2)", maxWidth: "44ch" }}
          >
            Bring a circuit, a contract invariant, or a formal target. We mine
            it and ship a Lean repo with a one-command re-verify. You trust the
            kernel, not us.
          </p>
          <div className="mt-9 flex flex-wrap items-center justify-center gap-3">
            <a className="btn btn-primary" href={CONTACT}>
              commission a campaign →
            </a>
            <a className="btn btn-ghost" href={DELTASTAR}>
              read the δ* proof
            </a>
          </div>
        </div>
      </section>

      {/* ============================ FOOTER ============================ */}
      <footer className="col" style={{ paddingBottom: "clamp(3rem, 6vw, 5rem)" }}>
        <hr className="rule mb-7" />
        <div className="flex flex-col sm:flex-row items-start sm:items-center justify-between gap-4">
          <div className="flex items-center gap-2.5">
            <span
              className="inline-block rounded-[3px]"
              style={{ width: "0.7rem", height: "0.7rem", background: "var(--ok)" }}
            />
            <span className="mono text-[0.78rem]">truth&#8202;mining</span>
          </div>
          <p className="mono text-[0.72rem]" style={{ color: "var(--ink-3)" }}>
            the unit of work is a brick · one kernel-checked theorem or refutation
          </p>
          <a className="link mono text-[0.74rem]" href={DELTASTAR}>
            deltastar.computer
          </a>
        </div>
      </footer>
    </main>
  );
}
