#import "@preview/fletcher:0.5.8": diagram, edge, node

// Coordinates and arrows follow the source objects, with relative sides
// explicit. Horizontal opposite arrows are straight parallel strokes.
#let graph(vertices, arrows, spacing: (18mm, 12mm)) = diagram(
  spacing: spacing,
  node-inset: 2pt,
  node-defocus: 0,
  ..vertices.map(v => node(v.at(0), v.at(1))),
  ..arrows.map(e => edge(
    e.at(0),
    e.at(1),
    e.at(2),
    e.at(4, default: "-|>"),
    label-side: e.at(3, default: left),
  )),
)
#let view(body) = block(width: 100%, align(center, body))

#let projective-quotient-isomorphism-diagram = view(graph(
  (((0, 0), $Q$), ((1, 0), $Q'$), ((0.5, 1), $X$)),
  (
    ((0, 0), (1, 0), $f$),
    ((0, 0), (0.5, 1), $j$, right),
    ((1, 0), (0.5, 1), $i$, left),
  ),
))

#let opposite-arrows(a, b, above, below) = view(diagram(
  spacing: (25mm, 12mm),
  node-inset: 2pt,
  node-defocus: 0,
  node((0, 0), a),
  node((1, 0), b),
  edge((0, 0), (1, 0), above, "-|>", shift: 3pt, label-side: left),
  edge((1, 0), (0, 0), below, "-|>", shift: 3pt, label-side: left),
))
#let stable-image-splitting-diagram = opposite-arrows(
  $M beta^t$,
  $M$,
  $i gamma^(-1)$,
  $gamma$,
)
#let krull-schmidt-splitting-diagram = opposite-arrows(
  $M_1$,
  $N_1$,
  $nu_1$,
  $phi^(-1)mu_1$,
)

#let projective-cover-uniqueness-diagram = view(graph(
  (((1, 0), $P$), ((0, 1), $P'$), ((1, 1), $M$)),
  (
    ((1, 0), (0, 1), $theta$, right, "--|>"),
    ((1, 0), (1, 1), $f$, left),
    ((0, 1), (1, 1), $f'$, right),
  ),
))

#let projective-cover-lifting-diagram = graph(
  (
    ((0, 0), $P$),
    ((1, 0), $P slash N P$),
    ((0, 1), $X$),
    ((1, 1), $X slash N X$),
  ),
  (
    ((0, 0), (1, 0), []),
    ((0, 0), (0, 1), $f$, right, "--|>"),
    ((1, 0), (1, 1), $h$, left),
    ((0, 1), (1, 1), []),
  ),
)

#let projective-socle-injection-diagram = view(graph(
  (((0, 0), $"soc" A e$), ((1, 0), $"soc" M$), ((0, 1), $A e$), ((1, 1), $M$)),
  (
    ((0, 0), (1, 0), $f'$),
    ((0, 0), (0, 1), []),
    ((1, 0), (1, 1), []),
    ((0, 1), (1, 1), $f$, left),
  ),
))

#let socle-injective-hull-diagram = view(graph(
  (
    ((0, 0), $"soc" N$),
    ((0.5, 0), $=$),
    ((1, 0), $"soc" X$),
    ((0, 1), $N$),
    ((0.5, 1), $subset.eq$),
    ((1, 1), $X$),
  ),
  (((0, 0), (0, 1), []), ((1, 0), (1, 1), [])),
  spacing: (7mm, 12mm),
))

#let injective-hull-decomposition-diagram = view(graph(
  (
    ((0, 0), $0$),
    ((1, 0), $N$),
    ((2, 0), $X$),
    ((3, 0), $M$),
    ((4, 0), $0$),
    ((0, 1), $0$),
    ((1, 1), $N_1 plus.o N_2$),
    ((2, 1), $X_1 plus.o X_2$),
    ((3, 1), $M_1 plus.o M_2$),
    ((4, 1), $0$),
  ),
  (
    ((0, 0), (1, 0), []),
    ((1, 0), (2, 0), []),
    ((2, 0), (3, 0), []),
    ((3, 0), (4, 0), []),
    ((0, 1), (1, 1), []),
    ((1, 1), (2, 1), []),
    ((2, 1), (3, 1), []),
    ((3, 1), (4, 1), []),
    ((1, 0), (1, 1), $alpha$, right),
    ((2, 0), (2, 1), $beta$, right),
    ((3, 0), (3, 1), $gamma$, right),
  ),
  spacing: (12mm, 12mm),
))

#let projective-module-lifting-diagram = view(graph(
  (
    ((0, 0), $P$),
    ((1, 0), $P slash I P$),
    ((2, 0), $P slash N P$),
    ((0, 1), $X$),
    ((1, 1), $X slash I X$),
    ((2, 1), $X slash N X$),
  ),
  (
    ((0, 0), (1, 0), []),
    ((1, 0), (2, 0), []),
    ((0, 1), (1, 1), []),
    ((1, 1), (2, 1), []),
    ((0, 0), (0, 1), $f$, right),
    ((1, 0), (1, 1), $g$, right),
    ((2, 0), (2, 1), $h$, right),
  ),
))
