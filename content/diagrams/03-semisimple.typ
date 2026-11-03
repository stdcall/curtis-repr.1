#import "@preview/fletcher:0.5.8": diagram, edge, node

// One square: naturality is exactly equality of the two composites.
#let natural-transformation-diagram = block(width: 100%, align(center, diagram(
  spacing: (20mm, 12mm),
  node-inset: 2pt,
  node-defocus: 0,
  node((0, 0), $F(A_1)$),
  node((1, 0), $G(A_1)$),
  node((0, 1), $F(A_2)$),
  node((1, 1), $G(A_2)$),
  edge((0, 0), (1, 0), $tau_(A_1)$, "-|>", label-side: left),
  edge((0, 0), (0, 1), $F(f)$, "-|>", label-side: right),
  edge((1, 0), (1, 1), $G(f)$, "-|>", label-side: left),
  edge((0, 1), (1, 1), $tau_(A_2)$, "-|>", label-side: right),
)))
