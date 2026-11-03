#import "@preview/fletcher:0.5.8": diagram, edge, node

// Source644: two exact rows, eight right arrows and two downward arrows.
// The theta lift is dashed; theta and barred theta lie physically left.
#let projectivity-reduction-diagram() = block(width: 100%, align(
  center,
  diagram(
    spacing: (18mm, 13mm),
    node-inset: 2pt,
    node-defocus: 0,
    node((0, 0), $0$),
    node((1, 0), $F$),
    node((2, 0), $F$),
    node((3, 0), $overline(F)$),
    node((4, 0), $0$),
    node((0, 1), $0$),
    node((1, 1), $M$),
    node((2, 1), $M$),
    node((3, 1), $overline(M)$),
    node((4, 1), $0$),
    edge((0, 0), (1, 0), "-|>"),
    edge((1, 0), (2, 0), $pi$, "-|>"),
    edge((2, 0), (3, 0), "-|>"),
    edge((3, 0), (4, 0), "-|>"),
    edge((0, 1), (1, 1), "-|>"),
    edge((1, 1), (2, 1), $pi$, "-|>"),
    edge((2, 1), (3, 1), "-|>"),
    edge((3, 1), (4, 1), "-|>"),
    edge((2, 0), (2, 1), $theta$, "--|>", label-side: right),
    edge((3, 0), (3, 1), $overline(theta)$, "-|>", label-side: right),
  ),
))

// Source644: ten nodes, eight right arrows, three unlabeled down arrows.
#let projectivity-kernel-diagram() = block(width: 100%, align(center, diagram(
  spacing: (18mm, 13mm),
  node-inset: 2pt,
  node-defocus: 0,
  node((0, 0), $0$),
  node((1, 0), $N$),
  node((2, 0), $F$),
  node((3, 0), $M$),
  node((4, 0), $0$),
  node((0, 1), $0$),
  node((1, 1), $overline(N)$),
  node((2, 1), $overline(F)$),
  node((3, 1), $overline(M)$),
  node((4, 1), $0$),
  edge((0, 0), (1, 0), "-|>"),
  edge((1, 0), (2, 0), $rho$, "-|>"),
  edge((2, 0), (3, 0), $theta$, "-|>"),
  edge((3, 0), (4, 0), "-|>"),
  edge((0, 1), (1, 1), "-|>"),
  edge((1, 1), (2, 1), $overline(rho)$, "-|>"),
  edge((2, 1), (3, 1), $overline(theta)$, "-|>"),
  edge((3, 1), (4, 1), "-|>"),
  edge((1, 0), (1, 1), "-|>"),
  edge((2, 0), (2, 1), "-|>"),
  edge((3, 0), (3, 1), "-|>"),
)))

// Source644: four nodes, opposing horizontal pairs and two down arrows.
// rho/barred rho above right arrows; psi-prime/psi below left arrows.
#let projectivity-splitting-diagram() = block(width: 100%, align(
  center,
  diagram(
    spacing: (30mm, 14mm),
    node-inset: 2pt,
    node-defocus: 0,
    node((0, 0), $N$),
    node((1, 0), $F$),
    node((0, 1), $overline(N)$),
    node((1, 1), $overline(F)$),
    edge((0, 0), (1, 0), $rho$, "-|>", shift: 2pt),
    edge((1, 0), (0, 0), $psi'$, "-|>", shift: 2pt, label-side: left),
    edge((0, 1), (1, 1), $overline(rho)$, "-|>", shift: 2pt),
    edge((1, 1), (0, 1), $psi$, "-|>", shift: 2pt, label-side: left),
    edge((0, 0), (0, 1), "-|>"),
    edge((1, 0), (1, 1), "-|>"),
  ),
))

// Source646: no top horizontal edge. The lower arrow phi points right.
#let maranda-reduction-diagram() = block(width: 100%, align(center, diagram(
  spacing: (25mm, 12mm),
  node-inset: 2pt,
  node-defocus: 0,
  node((0, 0), $M$),
  node((1, 0), $N$),
  node((0, 1), $M_k$),
  node((1, 1), $N_k$),
  edge((0, 0), (0, 1), "-|>"),
  edge((1, 0), (1, 1), "-|>"),
  edge((0, 1), (1, 1), $phi$, "-|>"),
)))

// Source662: both fibre products have four unlabeled ordinary arrows.
#let cyclotomic-dyad-diagram() = block(width: 100%, align(center, diagram(
  spacing: (18mm, 13mm),
  node-inset: 2pt,
  node-defocus: 0,
  node((0, 0), $Lambda$),
  node((1, 0), [$R=hat(ZZ)_p[epsilon]$, $epsilon=$ primitive $p$-th root of
    $1$]),
  node((0, 1), $hat(ZZ)_p$),
  node((1, 1), $overline(ZZ)=ZZ slash p ZZ$),
  edge((0, 0), (1, 0), "-|>"),
  edge((0, 0), (0, 1), "-|>"),
  edge((1, 0), (1, 1), "-|>"),
  edge((0, 1), (1, 1), "-|>"),
)))

#let general-dyad-diagram() = block(width: 100%, align(center, diagram(
  spacing: (22mm, 12mm),
  node-inset: 2pt,
  node-defocus: 0,
  node((0, 0), $Lambda$),
  node((1, 0), $R_1$),
  node((0, 1), $R_2$),
  node((1, 1), $k$),
  edge((0, 0), (1, 0), "-|>"),
  edge((0, 0), (0, 1), "-|>"),
  edge((1, 0), (1, 1), "-|>"),
  edge((0, 1), (1, 1), "-|>"),
)))
