import { CopyCommand } from "../CopyCommand";

/**
 * "Mine it yourself" — the crowd-sourced call to action. Points a reader's own
 * coding agent (Claude Code or Codex) at the open problem via a pre-prompted
 * skill that produces ONE kernel-checked brick and opens a PR. Honest by
 * construction: a verified refutation counts as much as a verified proof, and
 * the page never claims the prize is closed.
 */
export function Contribute() {
  return (
    <section id="contribute" className="prose-col mt-20">
      <p className="sc-label text-[0.85rem] font-semibold" style={{ color: "var(--accent)" }}>
        Mine it yourself
      </p>
      <h2 className="text-[1.45rem] font-semibold leading-snug mb-5" style={{ letterSpacing: "-0.01em" }}>
        Point your own agent at the open core
      </h2>

      <p>
        The window is still open, and the search is embarrassingly parallel. You
        can aim your own AI coding agent at it with one pre-prompted skill: it
        reads the live frontier, picks a small uncontested target, and mines a
        single <em>brick</em> — a result the Lean&nbsp;4 kernel or exact integer
        arithmetic actually <em>checks</em>, not something a model merely claims.
        Then it opens a pull request. Nobody has mined a million-dollar
        conjecture with a coding agent before.
      </p>

      <p
        className="text-[0.95rem]"
        style={{ color: "var(--ink-secondary)" }}
      >
        The model proposes; the kernel disposes. A verified <em>refutation</em>{" "}
        counts as much as a verified proof — both narrow the map, and both get
        published. The skill is built to claim exactly what it checked and
        nothing more.
      </p>

      <h3 className="sc-label text-[0.85rem] font-semibold mt-9 mb-4">
        Choose your miner
      </h3>

      <div className="miner-grid">
        <div className="miner-card">
          <p className="miner-name">
            <span aria-hidden>🤖</span> Claude&nbsp;Code
          </p>
          <p className="miner-step">Install the skill:</p>
          <CopyCommand command={`mkdir -p ~/.claude/skills/proximity-prize && curl -fsSL https://raw.githubusercontent.com/lalalune/ArkLib/main/mine/claude/proximity-prize/SKILL.md -o ~/.claude/skills/proximity-prize/SKILL.md`} />
          <p className="miner-step">
            Then start (or restart) Claude Code in any directory:
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
          <CopyCommand command={`curl -fsSL https://raw.githubusercontent.com/lalalune/ArkLib/main/mine/codex/AGENTS.md -o AGENTS.md`} />
          <p className="miner-step">Then run, in that directory:</p>
          <CopyCommand command={`codex`} />
          <p className="miner-hint">
            and tell it &ldquo;follow AGENTS.md — mine one brick.&rdquo;
          </p>
        </div>
      </div>

      <p className="mt-7 text-[0.95rem]">
        The default brick needs no Lean toolchain at all: an exact-arithmetic
        probe that tests a conjecture <em>in the prize regime</em> and tries to
        break it. If you have <code className="inline">elan</code>/
        <code className="inline">lake</code> and the mathlib cache, the agent can
        instead prove a small axiom-clean lemma. Either way the rule is the same:
        no <code className="inline">sorry</code>, no axioms, no floating-point
        &ldquo;basically zero&rdquo; — refute before you believe.
      </p>

      <p className="mt-4 text-[0.88rem]" style={{ color: "var(--ink-faint)" }}>
        Full instructions, the honesty charter, and what stays inside the prize
        regime:{" "}
        <a href="https://github.com/lalalune/ArkLib/tree/main/mine">
          lalalune/ArkLib/mine
        </a>
        . Contributions land as pull requests on{" "}
        <a href="https://github.com/lalalune/ArkLib">lalalune/ArkLib</a> and as
        notes on{" "}
        <a href="https://github.com/lalalune/ArkLib/issues/389">issue&nbsp;#389</a>.
      </p>
    </section>
  );
}
