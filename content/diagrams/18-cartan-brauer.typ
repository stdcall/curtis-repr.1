#import "@preview/fletcher:0.5.8": diagram, edge, node

#let cartan-brauer-triangle = block(width: 100%, align(center, diagram(
  spacing: (22mm, 15mm),
  node-inset: 2pt,
  node-defocus: 0,
  node((0, 0), $G_0 lr((K G))$),
  node((2, 0), $G_0 lr((k G))$),
  node((1, 1), $K_0 lr((k G)),$),
  edge((0, 0), (2, 0), $d$, "-|>", label-side: left),
  edge((1, 1), (0, 0), $e$, "-|>", label-side: left),
  edge((1, 1), (2, 0), $c$, "-|>", label-side: right),
)))

// Cartan maps take projective classes to all-module classes.
#let induction-cartan-square = block(width: 100%, align(center, diagram(
  spacing: (28mm, 18mm),
  node-inset: 2pt,
  node-defocus: 0,
  node((0, 0), $G_0 lr((K G))$),
  node((1, 0), $G_0 lr((k G))$),
  node((2, 0), $K_0 lr((k G))$),
  node((0, 1), $G_0 lr((K H))$),
  node((1, 1), $G_0 lr((k H))$),
  node((2, 1), $K_0 lr((k H)).$),
  edge((0, 0), (1, 0), $d$, "-|>", label-side: left),
  edge((2, 0), (1, 0), $c$, "-|>", label-side: right),
  edge((0, 1), (1, 1), $d$, "-|>", label-side: left),
  edge((2, 1), (1, 1), $c$, "-|>", label-side: right),
  edge((0, 1), (0, 0), $"ind"_H^G$, "-|>", label-side: left),
  edge((1, 1), (1, 0), $"ind"_H^G$, "-|>", label-side: left),
  edge((2, 1), (2, 0), $"ind"_H^G$, "-|>", label-side: left),
)))

