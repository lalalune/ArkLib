import type { ReactNode } from "react";

/**
 * Narrative lede: a short italic "documentary narrator" beat at the top of a
 * numbered section. Distinct register from the technical prose below it,
 * marked by an oxblood left rule. Two to three sentences, never more.
 */
export function Lede({ children }: { children: ReactNode }) {
  return (
    <div className="lede" role="doc-epigraph">
      <p>{children}</p>
    </div>
  );
}
