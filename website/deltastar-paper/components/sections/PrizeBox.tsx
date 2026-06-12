import { M } from "../Math";

/**
 * "The Prize" callout: the real-world stakes box. Sober, sourced, distinct.
 */
export function PrizeBox() {
  return (
    <aside id="prize" className="prose-col mt-12" aria-label="The prize">
      <div className="prize-box">
        <p className="sc-label prize-label">The prize</p>
        <p className="prize-amount">
          $1,000,000
          <span className="prize-amount-sub">Ethereum Foundation Proximity Prize</span>
        </p>
        <p>
          In 2026 the Ethereum Foundation posted a{" "}
          <a href="https://proximityprize.org/">$1M prize</a> for resolving the
          proximity-gaps conjectures for Reed&ndash;Solomon codes, with the
          mutual correlated agreement variant studied here as the strengthened
          target. It sits alongside the $1M Poseidon Prize in the
          Foundation&rsquo;s program of buying down the open mathematical risk
          under its zk and post-quantum roadmap (
          <a href="https://verified-zkevm.org/">verified-zkevm.org</a>).
        </p>
        <p>
          The stakes are concrete. Every FRI- and WHIR-based SNARK in
          production rides on these soundness bounds, and today they all run on
          the conservative provable ones. Pinning{" "}
          <M>{String.raw`\delta^*`}</M> at the conjectured edge would cut
          verifier queries by an estimated <M>{String.raw`8\times`}</M>,
          compounding through every proof Ethereum verifies: cheaper proofs,
          faster finality, a lighter chain. A disproof at deployed parameters
          would force protocol redesigns. Either answer is worth the money.
        </p>
        <p className="prize-status">
          Status: <strong>open</strong>. The campaign reported on this page
          narrowed the map; it did not close the window.
        </p>
      </div>
    </aside>
  );
}
