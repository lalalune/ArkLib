import type { ReactNode } from "react";

export function Section({
  id,
  eyebrow,
  children,
}: {
  id?: string;
  eyebrow?: string;
  children: ReactNode;
}) {
  return (
    <section id={id} className="col" style={{ paddingBlock: "clamp(4rem, 9vw, 7rem)" }}>
      {eyebrow ? <p className="eyebrow mb-5">{eyebrow}</p> : null}
      {children}
    </section>
  );
}
