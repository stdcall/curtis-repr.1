#import "@preview/fletcher:0.5.8": diagram, edge, node

#let units-quotient-diagram = block(width: 100%, align(center, diagram(
  spacing: (22mm, 12mm),
  node-inset: 2pt,
  node-defocus: 0,
  node((0, 0), $A$),
  node((1, 0), $A slash I$),
  node((0, 1), $A slash "rad" A$),
  node((1, 1), $overline(A)$),
  edge((0, 0), (1, 0), "-|>"),
  edge((0, 0), (0, 1), "-|>"),
  edge((1, 0), (1, 1), $f$, "-|>", label-side: right),
  edge((0, 1), (1, 1), $g$, "-|>", label-side: left),
)))
