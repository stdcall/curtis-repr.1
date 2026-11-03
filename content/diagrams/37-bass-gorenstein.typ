#import "@preview/fletcher:0.5.8": diagram, edge, node

// Source805: a partial extension diagram, not a completed triangle.
#let relative-injectivity-diagram() = block(width: 100%, align(center, diagram(
  spacing: (22mm, 12mm),
  node-inset: 2pt,
  node-defocus: 0,
  node((0, 0), $0$),
  node((1, 0), $M_1$),
  node((2, 0), $M$),
  node((1, 1), $L$),
  edge((0, 0), (1, 0), "-|>"),
  edge((1, 0), (2, 0), "-|>"),
  edge((1, 0), (1, 1), $f$, "-|>", label-side: right),
)))

// Source813 Exercise1: four ordinary horizontal arrows, f left of DOWN.
#let weak-injectivity-diagram() = block(width: 100%, align(center, diagram(
  spacing: (22mm, 12mm),
  node-inset: 2pt,
  node-defocus: 0,
  node((0, 0), $0$),
  node((1, 0), $M_1$),
  node((2, 0), $M$),
  node((3, 0), $M_2$),
  node((4, 0), $0$),
  node((1, 1), $L$),
  edge((0, 0), (1, 0), "-|>"),
  edge((1, 0), (2, 0), $mu$, "-|>"),
  edge((2, 0), (3, 0), "-|>"),
  edge((3, 0), (4, 0), "-|>"),
  edge((1, 0), (1, 1), $f$, "-|>", label-side: right),
)))

// Source814 Exercise2 Hint: no added extension arrow to I.
#let trace-injectivity-diagram() = block(width: 100%, align(center, diagram(
  spacing: (22mm, 12mm),
  node-inset: 2pt,
  node-defocus: 0,
  node((0, 0), $0$),
  node((1, 0), $M_1$),
  node((2, 0), $M^((n))$),
  node((3, 0), $M_2$),
  node((4, 0), $0$),
  node((1, 1), $L$),
  node((1, 2), $I$),
  edge((0, 0), (1, 0), "-|>"),
  edge((1, 0), (2, 0), "-|>"),
  edge((2, 0), (3, 0), "-|>"),
  edge((3, 0), (4, 0), "-|>"),
  edge((1, 0), (1, 1), $f$, "-|>", label-side: right),
  edge((1, 1), (1, 2), $i$, "-|>", label-side: right),
)))

// Source814 Exercise3 Hint: its first diagram is entirely solid.
#let summand-injectivity-diagram() = block(width: 100%, align(center, diagram(
  spacing: (22mm, 12mm),
  node-inset: 2pt,
  node-defocus: 0,
  node((0, 0), $0$),
  node((1, 0), $T_1$),
  node((2, 0), $T^((n))$),
  node((3, 0), $T_2$),
  node((4, 0), $0$),
  node((1, 1), $Q$),
  edge((0, 0), (1, 0), "-|>"),
  edge((1, 0), (2, 0), "-|>"),
  edge((2, 0), (3, 0), "-|>"),
  edge((3, 0), (4, 0), "-|>"),
  edge((1, 0), (1, 1), $f$, "-|>", label-side: right),
)))

// Source814: the extension g' points DOWN-LEFT and is dashed.
#let summand-injectivity-extension-diagram() = block(width: 100%, align(
  center,
  diagram(
    spacing: (22mm, 14mm),
    node-inset: 2pt,
    node-defocus: 0,
    node((0, 0), $0$),
    node((1, 0), $T_1 plus.o P^((n))$),
    node((2, 0), $T^((n)) plus.o P^((n))$),
    node((3, 0), $T_2$),
    node((4, 0), $0$),
    node((1, 1), $Q plus.o P$),
    edge((0, 0), (1, 0), "-|>"),
    edge((1, 0), (2, 0), "-|>"),
    edge((2, 0), (3, 0), "-|>"),
    edge((3, 0), (4, 0), "-|>"),
    edge((1, 0), (1, 1), $f'$, "-|>", label-side: right),
    edge((2, 0), (1, 1), $g'$, "--|>", label-side: left),
  ),
))
