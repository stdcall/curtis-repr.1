#import "@preview/fletcher:0.5.8": diagram, edge, node

// Physical438/printed416, Proposition16.23. Four nodes, four straight
// solid single filled-arrow edges. Both downward d labels are physically
// left of their arrows; neither horizontal arrow has a label or hook.
#let decomposition-extension-diagram = block(width: 100%, align(center, diagram(
  spacing: (35mm, 14mm),
  node-inset: 2pt,
  node-defocus: 0,
  node((0, 0), $G_0 lr((K G))$),
  node((1, 0), $G_0 lr((K' G))$),
  node((0, 1), $G_0 lr((k G))$),
  node((1, 1), $G_0 lr((k' G)),$),
  edge((0, 0), (1, 0), "-|>"),
  edge((0, 0), (0, 1), $d$, "-|>", label-side: right),
  edge((1, 0), (1, 1), $d$, "-|>", label-side: right),
  edge((0, 1), (1, 1), "-|>"),
)))
