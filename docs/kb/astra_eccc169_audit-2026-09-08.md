# ECCC TR26-169: concrete-budget audit

[Jeronimo's September preprint](https://eccc.weizmann.ac.il/report/2026/169/download)
claims fixed-slack capacity MCA over arbitrary prime-field evaluation domains,
with an effective polynomial exception bound (Theorem 1.2). Two agents
independently inspected its geometric cover and support descent. They found
no substantive gap in those inspected steps; this was not a full referee
review or Lean verification.

The same-support event matches ours when the agreement threshold is at least
the code dimension. However, Section 7's line bound has the form
`|E| + Delta * sum(a=0..r+1, n^a)`. Even the optimistic nonempty-cover choices
`|E|=0`, `Delta=1`, `r=0` give `n+1`, exceeding our exact budget `n`.
This concerns the bound's strength, not the true bad count.

Appendix B does not give numerical constants certifying an admissible
derivative order or length threshold for `n=2^30`. Sections 8.3–8.5 retain
separate length and field conditions. Consequently this new route does not
establish production safety or change our threshold bracket. The full paper
remains in ignored research scratch; no theorem from it was assumed by the
new Lean rational-list module.
