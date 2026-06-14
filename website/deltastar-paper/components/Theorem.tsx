import type { ReactNode } from "react";

const REPO = "https://github.com/lalalune/ArkLib/blob/main";
const PG = "ArkLib/Data/CodingTheory/ProximityGap";

export function Theorem({
  kind = "Theorem",
  name,
  file,
  decl,
  conditional,
  refuted,
  children,
}: {
  kind?: string;
  name: ReactNode;
  file: string;
  decl?: string;
  conditional?: string;
  refuted?: boolean;
  children: ReactNode;
}) {
  const path = file.includes("/") && !file.startsWith("BCIKS20")
    ? file
    : `${PG}/${file}`;
  return (
    <figure className={`thm${refuted ? " thm-refuted" : ""}`}>
      <div className="thm-head">
        <span className="thm-kind">{kind}</span>
        {name ? <span> ({name})</span> : null}
      </div>
      <div className="thm-body">{children}</div>
      <div className="thm-meta">
        <span className="badge-checked" title="Axiom census of the Lean proof">
          {refuted
            ? "machine-checked refutation"
            : conditional
              ? "machine-checked, conditional"
              : "machine-checked"}
        </span>
        <span>
          <a href={`${REPO}/${path}`}>
            <code>{file}</code>
          </a>
          {decl ? (
            <>
              {" "}&middot; <code>{decl}</code>
            </>
          ) : null}
        </span>
        <span>
          axioms: <code>propext, Classical.choice, Quot.sound</code>
          {conditional ? (
            <>
              {" "}&middot; modulo <code>{conditional}</code>
            </>
          ) : null}
        </span>
      </div>
    </figure>
  );
}
