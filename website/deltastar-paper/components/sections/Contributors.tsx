const campaign: { user: string; name?: string; note?: string }[] = [
  {
    user: "lalalune",
    name: "Shaw (lalalune)",
    note: "campaign lead; the overwhelming majority of fleet commits",
  },
  { user: "NubsCarson" },
  { user: "lewistham9x", name: "lekt9" },
  { user: "2-A-M" },
  { user: "0xSolace", name: "Sol" },
  { user: "SYMBaiEX" },
  { user: "standujar" },
];

const foundation: { user: string }[] = [
  { user: "quangvdao" },
  { user: "alexanderlhicks" },
  { user: "ElijahVlasov" },
  { user: "katyhr" },
  { user: "Ferinko" },
  { user: "Julek" },
];

function Avatar({
  user,
  name,
  note,
}: {
  user: string;
  name?: string;
  note?: string;
}) {
  return (
    <a
      href={`https://github.com/${user}`}
      className="contrib"
      title={note ?? name ?? user}
    >
      <img
        src={`https://github.com/${user}.png?size=80`}
        alt={`${name ?? user} on GitHub`}
        width={40}
        height={40}
        loading="lazy"
      />
      <span className="mono contrib-name">{name ?? user}</span>
    </a>
  );
}

export function Contributors() {
  return (
    <section id="contributors" className="prose-col mt-20">
      <h2 className="text-[1.45rem] font-semibold mb-6">
        The humans and the machines
      </h2>
      <p
        className="text-[0.95rem]"
        style={{ color: "var(--ink-secondary)" }}
      >
        The proofs were written by an LLM agent fleet and checked by the
        Lean&nbsp;4 kernel; the humans below steered the campaign, reviewed the
        work, and built the formal foundation it stands on. The models did the
        proving. The kernel did the believing.
      </p>

      <h3 className="sc-label text-[0.85rem] font-semibold mt-8 mb-3">
        Campaign &middot;{" "}
        <a href="https://github.com/lalalune/ArkLib">lalalune/ArkLib</a>
      </h3>
      <div className="contrib-grid">
        {campaign.map((c) => (
          <Avatar key={c.user} {...c} />
        ))}
      </div>
      <p className="mt-2 text-[0.8rem]" style={{ color: "var(--ink-faint)" }}>
        lalalune carries the overwhelming majority of fleet commits.
      </p>

      <h3 className="sc-label text-[0.85rem] font-semibold mt-10 mb-3">
        Foundation &middot; built on{" "}
        <a href="https://github.com/Verified-zkEVM/ArkLib">
          Verified-zkEVM/ArkLib
        </a>
      </h3>
      <p
        className="text-[0.9rem] mb-4"
        style={{ color: "var(--ink-secondary)" }}
      >
        The campaign is a fork. Everything here composes against the formal
        foundation laid by the upstream ArkLib team:
      </p>
      <div className="contrib-grid">
        {foundation.map((c) => (
          <Avatar key={c.user} {...c} />
        ))}
      </div>
    </section>
  );
}
