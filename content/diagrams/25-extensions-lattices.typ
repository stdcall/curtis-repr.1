#import "@preview/fletcher:0.5.8": diagram, edge, node

// Extension equivalence: two exact rows and identity maps on the ends.
// Downward labels lie on the left of their arrows.
#let extension-equivalence-diagram(named: false) = block(width: 100%, align(
  center,
  diagram(
    spacing: (19mm, 13mm),
    node-inset: 2pt,
    node-defocus: 0,
    node((0, 0), if named { $xi_1:0$ } else { $0$ }),
    node((1, 0), $M$),
    node((2, 0), if named { $X_1$ } else { $X$ }),
    node((3, 0), $N$),
    node((4, 0), $0$),
    node((0, 1), if named { $xi_2:0$ } else { $0$ }),
    node((1, 1), $M$),
    node((2, 1), if named { $X_2$ } else { $X'$ }),
    node((3, 1), $N$),
    node((4, 1), $0$),
    edge((0, 0), (1, 0), "-|>"),
    edge((1, 0), (2, 0), "-|>"),
    edge((2, 0), (3, 0), "-|>"),
    edge((3, 0), (4, 0), "-|>"),
    edge((0, 1), (1, 1), "-|>"),
    edge((1, 1), (2, 1), "-|>"),
    edge((2, 1), (3, 1), "-|>"),
    edge((3, 1), (4, 1), "-|>"),
    edge((1, 0), (1, 1), $1$, "-|>", label-side: right),
    edge((2, 0), (2, 1), $phi$, "-|>", label-side: right),
    edge((3, 0), (3, 1), $1$, "-|>", label-side: right),
  ),
))
