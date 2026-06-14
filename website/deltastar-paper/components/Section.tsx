import type { ReactNode } from "react";

export function Section({
  id,
  num,
  title,
  children,
  wide,
}: {
  id: string;
  num?: string;
  title: ReactNode;
  children: ReactNode;
  wide?: boolean;
}) {
  return (
    <section id={id} className="mt-20 first:mt-0">
      <div className={wide ? "wide-col" : "prose-col"}>
        <h2
          className="text-[1.45rem] font-semibold leading-snug mb-6"
          style={{ letterSpacing: "-0.01em" }}
        >
          {num ? (
            <span
              className="mr-3 font-normal"
              style={{ color: "var(--ink-faint)" }}
            >
              {num}
            </span>
          ) : null}
          {title}
        </h2>
        {children}
      </div>
    </section>
  );
}

export function SubSection({
  id,
  num,
  title,
  children,
}: {
  id?: string;
  num?: string;
  title: ReactNode;
  children: ReactNode;
}) {
  return (
    <div id={id} className="mt-12">
      <h3 className="text-[1.13rem] font-semibold mb-4">
        {num ? (
          <span className="mr-2.5 font-normal" style={{ color: "var(--ink-faint)" }}>
            {num}
          </span>
        ) : null}
        {title}
      </h3>
      {children}
    </div>
  );
}
