export function Cite({ id }: { id: string }) {
  return (
    <sup className="cite">
      <a href={`#ref-${id}`}>[{id}]</a>
    </sup>
  );
}
