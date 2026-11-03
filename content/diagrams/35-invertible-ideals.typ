#import "@preview/fletcher:0.5.8": diagram, edge, node

#let invertible-associativity() = align(center, diagram(
  spacing: (11mm, 8mm),
  node-inset: 2pt,
  node-defocus: 0,
  node((0, 0), $M times.o_Delta N times.o_Lambda M$),
  node((1, 0), $Lambda times.o_Lambda M$),
  node((0, 1), $M times.o_Delta Delta$),
  node((1, 1), $M$),
  node((2, 0), $N times.o_Lambda M times.o_Delta N$),
  node((3, 0), $Delta times.o_Delta N$),
  node((2, 1), $N times.o_Lambda Lambda$),
  node((3, 1), $N$),
  edge((0, 0), (1, 0), "->"),
  edge((0, 0), (0, 1), "->"),
  edge((1, 0), (1, 1), "->"),
  edge((0, 1), (1, 1), "->"),
  edge((2, 0), (3, 0), "->"),
  edge((2, 0), (2, 1), "->"),
  edge((3, 0), (3, 1), "->"),
  edge((2, 1), (3, 1), "->"),
))
