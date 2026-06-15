import { CopyCommand } from "../CopyCommand";

/**
 * "Mine it yourself" — the headline call to action, rendered as a prominent
 * banner near the top of the page. Points a reader's own coding agent (Claude
 * Code or Codex) at the open problem via a pre-prompted skill that produces ONE
 * kernel-checked brick and opens a PR. Honest by construction: a verified
 * refutation counts as much as a proof, and it never claims the prize is closed.
 */
export function Contribute() {
  return (
    <section id="contribute" className="wide-col mt-10 mb-6 scroll-mt-24">
      <div className="mine-hero">
        <p className="mine-eyebrow">
          <span aria-hidden>⛏</span> open problem · live · embarrassingly parallel
        </p>
        <h2 className="mine-title">Mine it yourself</h2>

        <p className="mine-sub">
          Point your own AI coding agent at this{" "}
          <strong>$1,000,000 open problem</strong>. One pre-prompted skill: it
          reads the live frontier, picks a small uncontested target, and mines a
          single <em>brick</em> — a result the Lean&nbsp;4 kernel or exact
          integer arithmetic actually <em>checks</em>, not something a model
          merely claims — then opens a pull request. As far as we know, nobody
          has mined a million-dollar conjecture with a coding agent before.
        </p>
        <p className="mine-rule">
          The model proposes; the kernel disposes. A verified <em>refutation</em>{" "}
          counts as much as a proof — and the prize is still open.
        </p>

        <p className="mine-choose sc-label">
          Fastest — paste this into Claude&nbsp;Code or Codex
        </p>
        <CopyCommand command={`mine the proximity prize: read https://deltastar-paper.pages.dev/mission.md and follow it`} />
        <p className="miner-hint" style={{ marginTop: "0.6rem" }}>
          No install. Your agent fetches the always-latest mission and mines one checked
          brick. Works on any Claude plan (including Max) and on Codex.
        </p>

        <p className="mine-choose sc-label">Or install it as a reusable command</p>
        <div className="miner-grid">
          <div className="miner-card">
            <p className="miner-name">
              <span aria-hidden>🤖</span> Claude&nbsp;Code
            </p>
            <p className="miner-step">Install the skill:</p>
            <CopyCommand command={`mkdir -p ~/.claude/skills/proximity-prize && curl -fsSL https://deltastar-paper.pages.dev/skill.md -o ~/.claude/skills/proximity-prize/SKILL.md`} />
            <p className="miner-step">
              Then start (or restart) Claude&nbsp;Code in any directory:
            </p>
            <CopyCommand command={`claude`} />
            <p className="miner-hint">
              and type <code className="inline">/proximity-prize</code> — or just
              say &ldquo;mine the proximity prize.&rdquo; (Restart is needed the
              first time so it picks up the new skill.)
            </p>
          </div>

          <div className="miner-card">
            <p className="miner-name">
              <span aria-hidden>🧠</span> Codex
            </p>
            <p className="miner-step">Grab the mission brief:</p>
            <CopyCommand command={`curl -fsSL https://deltastar-paper.pages.dev/codex.md -o AGENTS.md`} />
            <p className="miner-step">Then run, in that directory:</p>
            <CopyCommand command={`codex`} />
            <p className="miner-hint">
              and tell it &ldquo;follow AGENTS.md — mine one brick.&rdquo;
            </p>
          </div>
        </div>

        <p className="mine-foot">
          The default brick needs no Lean toolchain at all — an exact-arithmetic
          probe that tests a conjecture <em>in the prize regime</em> and tries to
          break it. The rule is always the same: no{" "}
          <code className="inline">sorry</code>, no axioms, no &ldquo;basically
          zero&rdquo; — refute before you believe. Full instructions and the
          honesty charter:{" "}
          <a href="https://github.com/lalalune/ArkLib/tree/main/mine">
            lalalune/ArkLib/mine
          </a>
          ; contributions land as PRs on{" "}
          <a href="https://github.com/lalalune/ArkLib">lalalune/ArkLib</a> and
          notes on{" "}
          <a href="https://github.com/lalalune/ArkLib/issues/407">
            issue&nbsp;#407
          </a>
          .
        </p>
      </div>
    </section>
  );
}
