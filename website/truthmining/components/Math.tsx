import katex from "katex";

export function M({ children }: { children: string }) {
  const html = katex.renderToString(children, {
    throwOnError: false,
    output: "html",
  });
  return <span dangerouslySetInnerHTML={{ __html: html }} />;
}

export function MD({ children }: { children: string }) {
  const html = katex.renderToString(children, {
    throwOnError: false,
    displayMode: true,
    output: "html",
  });
  return <div dangerouslySetInnerHTML={{ __html: html }} />;
}
