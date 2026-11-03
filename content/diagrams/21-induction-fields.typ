#import "@preview/fletcher:0.5.8": diagram, edge, node
#import "02-hom-tensor.typ": graph, view

// Both horizontal labels are above their arrows on these source pages.
#let field-square(a, b, c, d, top, west, east, bottom) = graph(
  (((0, 0), a), ((1, 0), b), ((0, 1), c), ((1, 1), d)),
  (
    ((0, 0), (1, 0), top, left),
    ((0, 0), (0, 1), west, right),
    ((1, 0), (1, 1), east, left),
    ((0, 1), (1, 1), bottom, left),
  ),
)

#let induction-cartan-triangle(punctuation: "") = view(diagram(
  spacing: (22mm, 15mm),
  node-inset: 2pt,
  node-defocus: 0,
  node((0, 0), $G_0(K G)$),
  node((2, 0), $G_0(k G)$),
  node((1, 1), [$K_0(k G)$#punctuation]),
  edge((0, 0), (2, 0), $d$, "-|>", label-side: left),
  edge((1, 1), (0, 0), $e$, "-|>", label-side: left),
  edge((1, 1), (2, 0), $c$, "-|>", label-side: right),
))

#let character-induction-square = view(field-square(
  $"ch" K H$,
  $"ch" K G$,
  $G_0(K H)$,
  $G_0(K G),$,
  $"ind"_H^G$,
  [],
  [],
  $"ind"_H^G$,
))

#let restriction-decomposition-square = view(field-square(
  $G_0(K G)$,
  $G_0(K H)$,
  $G_0(k G)$,
  $G_0(k H).$,
  $"res"_H^G$,
  $d$,
  $d$,
  $"res"_H^G$,
))

// Induction and decomposition homomorphisms for H and G.
#let induction-decomposition-square = view(field-square(
  $G_0(K H)$,
  $G_0(K G)$,
  $G_0(k H)$,
  $G_0(k G)$,
  $"ind"_H^G$,
  $d$,
  $d$,
  $"ind"_H^G$,
))

#let projective-character-extension-square(split: false) = view(diagram(
  spacing: (35mm, 18mm),
  node-inset: 2pt,
  node-defocus: 0,
  node((0, 0), $K_0(k' G)$),
  node((1, 0), $G_0(K' G)$),
  node((0, 1), $K_0(k G)$),
  node((1, 1), [$G_0(K G)$#if split { "." } else { "," }]),
  edge(
    (0, 0),
    (1, 0),
    $e'$,
    "-|>",
    shift: if split { 3pt } else { 0pt },
    label-side: left,
  ),
  edge((0, 1), (1, 1), $e$, "-|>", label-side: if split { right } else {
    left
  }),
  edge(
    (0, 1),
    (0, 0),
    $alpha$,
    "-|>",
    shift: if split { 3pt } else { 0pt },
    label-side: left,
  ),
  edge((1, 1), (1, 0), $beta$, "-|>", label-side: left),
  if split {
    edge((1, 0), (0, 0), $gamma$, "--|>", shift: 3pt, label-side: left)
    edge((0, 0), (0, 1), $delta$, "--|>", shift: 3pt, label-side: left)
  },
))

#let cartan-extension-snake-diagram = view(graph(
  (
    ((0, 0), $0$),
    ((1, 0), $K_0(k G)$),
    ((2, 0), $K_0(k' G)$),
    ((3, 0), $X$),
    ((4, 0), $0$),
    ((0, 1), $0$),
    ((1, 1), $G_0(k G)$),
    ((2, 1), $G_0(k' G)$),
    ((3, 1), $Y$),
    ((4, 1), $0,$),
  ),
  (
    ((0, 0), (1, 0), [], left),
    ((1, 0), (2, 0), $alpha$, left),
    ((2, 0), (3, 0), [], left),
    ((3, 0), (4, 0), [], left),
    ((0, 1), (1, 1), [], left),
    ((1, 1), (2, 1), $beta$, left),
    ((2, 1), (3, 1), [], left),
    ((3, 1), (4, 1), [], left),
    ((1, 0), (1, 1), $c$, right),
    ((2, 0), (2, 1), $c'$, right),
    ((3, 0), (3, 1), $f$, right),
  ),
  spacing: (22mm, 18mm),
))
