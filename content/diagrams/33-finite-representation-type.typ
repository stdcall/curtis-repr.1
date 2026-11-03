#import "@preview/fletcher:0.5.8": diagram, edge, node

// Physical715: two distinct reduction squares. Horizontal relations are
// bare inclusions, not arrows. Only the four downward arrows are drawn.
#let dade-reduction-diagrams() = grid(
  columns: (1fr, 2fr),
  align: center + horizon,
  diagram(
    spacing: (18mm, 12mm),
    node-inset: 2pt,
    node-defocus: 0,
    node((0, 0), $Lambda_0$),
    node((1, 0), $Lambda'$),
    node((0, 1), $D$),
    node((1, 1), $D^((4))$),
    node((0.5, 0), $subset.eq$),
    node((0.5, 1), $subset.eq$),
    edge((0, 0), (0, 1), "-|>"),
    edge((1, 0), (1, 1), "-|>"),
  ),
  diagram(
    spacing: (25mm, 12mm),
    node-inset: 2pt,
    node-defocus: 0,
    node((0, 0), $M$),
    node((1, 0), $M'=Lambda' dot M$),
    node((0, 1), $W$),
    node((1, 1), $V^((4))=D^((4))W$),
    node((0.5, 0), $subset.eq$),
    node((0.5, 1), $subset.eq$),
    edge((0, 0), (0, 1), "-|>"),
    edge((1, 0), (1, 1), $phi$, "-|>", label-side: right),
  ),
)

// Physical723 native decode: exactly five arrows; no top horizontal edges.
// mu0 is dashed. All three downward labels lie physically left.
#let lattice-cover-morphism-diagram() = block(width: 100%, align(
  center,
  diagram(
    spacing: (35mm, 12mm),
    node-inset: 2pt,
    node-defocus: 0,
    node((0, 0), $X_1$),
    node((1, 0), $M_1 slash I M_1$),
    node((2, 0), $M'_1 slash I M'_1$),
    node((0, 1), $X_2$),
    node((1, 1), $M_2 slash I M_2$),
    node((2, 1), $M'_2 slash I M'_2$),
    edge((0, 0), (0, 1), $mu_0$, "--|>", label-side: right),
    edge((1, 0), (1, 1), $mu_1$, "-|>", label-side: right),
    edge((2, 0), (2, 1), $mu_2$, "-|>", label-side: right),
    edge((0, 1), (1, 1), "-|>"),
    edge((1, 1), (2, 1), "-|>"),
  ),
))

// Physical724: both arrows from the upper-left pullback are dashed.
#let lattice-reconstruction-diagram() = block(width: 100%, align(
  center,
  diagram(
    spacing: (33mm, 12mm),
    node-inset: 2pt,
    node-defocus: 0,
    node((0, 0), $M$),
    node((1, 0), $M'$),
    node((0, 1), $f(X)$),
    node((1, 1), $M' slash I M'=Y$),
    edge((0, 0), (1, 0), "--|>"),
    edge((0, 0), (0, 1), "--|>"),
    edge((1, 0), (1, 1), "-|>"),
    edge((0, 1), (1, 1), "-|>"),
  ),
))

// Physical724: six objects, four right arrows, three downward arrows.
#let triple-morphism-diagram() = block(width: 100%, align(center, diagram(
  spacing: (25mm, 12mm),
  node-inset: 2pt,
  node-defocus: 0,
  node((0, 0), $X_1$),
  node((1, 0), $f_1 lr((X_1))$),
  node((2, 0), $Y_1$),
  node((0, 1), $X_2$),
  node((1, 1), $f_2 lr((X_2))$),
  node((2, 1), $Y_2$),
  edge((0, 0), (1, 0), "-|>"),
  edge((1, 0), (2, 0), "-|>"),
  edge((0, 1), (1, 1), "-|>"),
  edge((1, 1), (2, 1), "-|>"),
  edge((0, 0), (0, 1), $alpha$, "-|>", label-side: right),
  edge((1, 0), (1, 1), "-|>"),
  edge((2, 0), (2, 1), $beta$, "-|>", label-side: right),
)))

// Physical730: ordinary solid pullback square, psi above lower arrow.
#let single-branch-pullback-diagram() = block(width: 100%, align(
  center,
  diagram(
    spacing: (35mm, 12mm),
    node-inset: 2pt,
    node-defocus: 0,
    node((0, 0), $M$),
    node((1, 0), $S_2=Lambda'e_2$),
    node((0, 1), $Delta$),
    node((1, 1), $S_2 slash P_2^(n_2)$),
    edge((0, 0), (1, 0), "-|>"),
    edge((0, 0), (0, 1), "-|>"),
    edge((1, 0), (1, 1), "-|>"),
    edge((0, 1), (1, 1), $psi$, "-|>"),
  ),
))

// Physical732 Exercise5 hint: seven ordinary solid arrows, no hidden hooks.
#let quotient-triple-lifting-diagram() = block(width: 100%, align(
  center,
  diagram(
    spacing: (25mm, 12mm),
    node-inset: 2pt,
    node-defocus: 0,
    node((0, 0), $X$),
    node((1, 0), $W$),
    node((2, 0), $Y$),
    node((0, 1), $overline(X)$),
    node((1, 1), $overline(W)$),
    node((2, 1), $overline(Y)$),
    edge((0, 0), (1, 0), $f$, "-|>"),
    edge((1, 0), (2, 0), $psi$, "-|>"),
    edge((0, 1), (1, 1), $overline(f)$, "-|>"),
    edge((1, 1), (2, 1), "-|>"),
    edge((0, 0), (0, 1), $pi$, "-|>", label-side: right),
    edge((1, 0), (1, 1), $sigma$, "-|>", label-side: right),
    edge((2, 0), (2, 1), $rho$, "-|>", label-side: right),
  ),
))
