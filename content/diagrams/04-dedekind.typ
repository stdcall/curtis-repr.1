#import "@preview/fletcher:0.5.8": diagram, edge, node

// Exercise1: alpha goes from the finite free module to J; beta returns.
#let ideal-splitting-diagram = block(width: 100%, align(center, diagram(
  spacing: (25mm, 12mm),
  node-inset: 2pt,
  node-defocus: 0,
  node((0, 0), $R^((n))$),
  node((1, 0), $J$),
  edge((0, 0), (1, 0), $alpha$, "-|>", shift: 3pt, label-side: left),
  edge((1, 0), (0, 0), $beta$, "-|>", shift: 3pt, label-side: left),
)))
