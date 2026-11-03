#import "@preview/fletcher:0.5.8": diagram, edge, node

// Nodes are (grid coordinate, mathematical content); edges carry their
// source, target, exact label, side and solid/dashed arrow specification.
#let graph(vertices, arrows, spacing: (14mm, 10mm)) = diagram(
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
#let raw-square(a, b, c, d, top, west, east, bottom) = graph(
  (((0, 0), a), ((1, 0), b), ((0, 1), c), ((1, 1), d)),
  (
    ((0, 0), (1, 0), top, left),
    ((0, 0), (0, 1), west, right),
    ((1, 0), (1, 1), east, left),
    ((0, 1), (1, 1), bottom, right),
  ),
)
#let commutative-square(..args) = view(raw-square(..args))
#let commutative-triangle(a, b, c, top, east, diagonal) = view(graph(
  (((0, 0), a), ((1, 0), b), ((1, 1), c)),
  (
    ((0, 0), (1, 0), top, left),
    ((1, 0), (1, 1), east, left),
    ((0, 0), (1, 1), diagonal, right),
  ),
))
#let covariant-triangle = view(graph(
  (((0, 0), $X$), ((0, 1), $M$), ((1, 1), $N$)),
  (
    ((0, 0), (0, 1), $alpha$, right),
    ((0, 1), (1, 1), $f$, right),
    ((0, 0), (1, 1), $f_* alpha$, left),
  ),
))
#let hom-regular-naturality = commutative-square(
  $op("Hom")_A lr((A,M))$,
  $M$,
  $op("Hom")_A lr((A,N))$,
  $N$,
  $theta_M$,
  $h_*$,
  $h$,
  $theta_N$,
)
#let pushout-diagram = raw-square(
  $T$,
  $M_1$,
  $M_2$,
  $X$,
  $f_1$,
  $f_2$,
  $g_1$,
  $g_2$,
)
#let pullback-diagram = raw-square(
  $Y$,
  $M_1$,
  $M_2$,
  $U$,
  $g_1$,
  $g_2$,
  $f_1$,
  $f_2$,
)
#let ideal-fibre-product = raw-square(
  $frac(A, I inter J)$,
  $frac(A, I)$,
  $frac(A, J)$,
  $frac(A, I+J)$,
  [],
  [],
  $f_1$,
  $f_2$,
)
#let inclusion-fibre-product = raw-square(
  $A$,
  $B$,
  $frac(A, I)$,
  $frac(B, I)$,
  [],
  [],
  $f_1$,
  $f_2$,
)
#let exact-functor-diagram = view(graph(
  (
    ((0, 1), $0$),
    ((1, 1), $op("ker") alpha$),
    ((2, 1), $A_1$),
    ((3, 1), $op("im") alpha$),
    ((4, 1), $0$),
    ((3, 0), $0$),
    ((3, 2), $A_2$),
    ((3, 3), $op("im") beta$),
    ((3, 4), $0$),
    ((2, 3), $0$),
    ((4, 3), $A_3$),
    ((5, 3), $op("cok") beta$),
    ((6, 3), $0$),
  ),
  (
    ((0, 1), (1, 1), []),
    ((1, 1), (2, 1), $i$),
    ((2, 1), (3, 1), $alpha$),
    ((3, 1), (4, 1), []),
    ((3, 0), (3, 1), []),
    ((3, 1), (3, 2), $i$, right),
    ((2, 1), (3, 2), $alpha$, right),
    ((3, 2), (3, 3), $beta$, right),
    ((3, 3), (3, 4), []),
    ((2, 3), (3, 3), []),
    ((3, 3), (4, 3), $i$, right),
    ((3, 2), (4, 3), $beta$),
    ((4, 3), (5, 3), []),
    ((5, 3), (6, 3), []),
  ),
  spacing: (6mm, 8mm),
))
#let projective-lifting = view(graph(
  (((0, 1), $X$), ((1, 1), $Y$), ((2, 1), $0$), ((1, 0), $P$)),
  (
    ((0, 1), (1, 1), $g$, right),
    ((1, 1), (2, 1), []),
    ((1, 0), (1, 1), $f$),
    ((1, 0), (0, 1), $h$, right, "--|>"),
  ),
))
#let injective-extension = view(graph(
  (((0, 0), $0$), ((1, 0), $X$), ((2, 0), $Y$), ((1, 1), $Q$)),
  (
    ((0, 0), (1, 0), []),
    ((1, 0), (2, 0), $f$),
    ((1, 0), (1, 1), $g$, right),
    ((2, 0), (1, 1), $h$, left, "--|>"),
  ),
))
#let ideal-extension = view(graph(
  (((0, 0), $0$), ((1, 0), $I$), ((2, 0), $A$), ((1, 1), $E$)),
  (((0, 0), (1, 0), []), ((1, 0), (2, 0), $i$), ((1, 0), (1, 1), $g$, right)),
))
#let ideal-extension-lifted = view(graph(
  (((0, 0), $0$), ((1, 0), $I$), ((2, 0), $A$), ((1, 1), $E$)),
  (
    ((0, 0), (1, 0), []),
    ((1, 0), (2, 0), $i$),
    ((1, 0), (1, 1), $g$, right),
    ((2, 0), (1, 1), $p g'$, left, "--|>"),
  ),
))
#let injectivity-pushout = view(graph(
  (
    ((0, 0), $0$),
    ((1, 0), $I$),
    ((2, 0), $A$),
    ((3, 0), $A slash I$),
    ((4, 0), $0$),
    ((0, 1), $0$),
    ((1, 1), $E$),
    ((2, 1), $X$),
    ((3, 1), $A slash I$),
    ((4, 1), $0$),
  ),
  (
    ((0, 0), (1, 0), []),
    ((1, 0), (2, 0), $i$),
    ((2, 0), (3, 0), []),
    ((3, 0), (4, 0), []),
    ((0, 1), (1, 1), []),
    ((1, 1), (2, 1), $i'$),
    ((2, 1), (3, 1), []),
    ((3, 1), (4, 1), []),
    ((1, 0), (1, 1), $g$, right),
    ((2, 0), (2, 1), $g'$),
    ((3, 0), (3, 1), $1$),
  ),
  spacing: (9mm, 12mm),
))
#let flat-summand-diagram = view(graph(
  (
    ((0, 0), $L times.o F$),
    ((1, 0), $M times.o F$),
    ((2, 0), $N times.o F$),
    ((0, 1), $L times.o X plus.o L times.o X'$),
    ((1, 1), $M times.o X plus.o M times.o X'$),
    ((2, 1), $N times.o X plus.o N times.o X'$),
  ),
  (
    ((0, 0), (1, 0), $f times.o 1_F$),
    ((1, 0), (2, 0), $g times.o 1_F$),
    ((0, 0), (0, 1), []),
    ((1, 0), (1, 1), []),
    ((2, 0), (2, 1), []),
    ((0, 1), (1, 1), $phi$, right),
    ((1, 1), (2, 1), $psi$, right),
  ),
  spacing: (5mm, 12mm),
))
#let snake-diagram = view(graph(
  (
    ((1, 0), $A$),
    ((2, 0), $B$),
    ((3, 0), $C$),
    ((4, 0), $0$),
    ((0, 1), $0$),
    ((1, 1), $A'$),
    ((2, 1), $B'$),
    ((3, 1), $C'$),
  ),
  (
    ((1, 0), (2, 0), $rho$),
    ((2, 0), (3, 0), []),
    ((3, 0), (4, 0), []),
    ((0, 1), (1, 1), []),
    ((1, 1), (2, 1), []),
    ((2, 1), (3, 1), $sigma$, right),
    ((1, 0), (1, 1), $alpha$, right),
    ((2, 0), (2, 1), $beta$, right),
    ((3, 0), (3, 1), $gamma$),
  ),
))
#let pushout-universal = view(graph(
  (
    ((0, 0), $T$),
    ((1, 0), $M_1$),
    ((0, 1), $M_2$),
    ((1, 1), $X$),
    ((1.5, 2), $V$),
  ),
  (
    ((0, 0), (1, 0), []),
    ((0, 0), (0, 1), []),
    ((1, 0), (1, 1), []),
    ((0, 1), (1, 1), []),
    ((1, 0), (1.5, 2), $h_1$),
    ((0, 1), (1.5, 2), $h_2$, right),
    ((1, 1), (1.5, 2), $h$),
  ),
))
#let pullback-universal = view(graph(
  (
    ((0, 0), $W$),
    ((0.5, 1), $Y$),
    ((1.5, 1), $M_1$),
    ((0.5, 2), $M_2$),
    ((1.5, 2), $U$),
  ),
  (
    ((0, 0), (1.5, 1), $h_1$),
    ((0, 0), (0.5, 2), $h_2$, right),
    ((0, 0), (0.5, 1), $h$, right),
    ((0.5, 1), (1.5, 1), $g_1$, right),
    ((0.5, 1), (0.5, 2), $g_2$, right),
    ((1.5, 1), (1.5, 2), $f_1$),
    ((0.5, 2), (1.5, 2), $f_2$, right),
  ),
))
#let factorization-initial = view(graph(
  (
    ((0, 0), $0$),
    ((1, 0), $L_1$),
    ((2, 0), $M_1$),
    ((3, 0), $N_1$),
    ((4, 0), $0$),
    ((0, 1), $0$),
    ((1, 1), $L_2$),
    ((2, 1), $M_2$),
    ((3, 1), $N_2$),
    ((4, 1), $0$),
  ),
  (
    ((0, 0), (1, 0), []),
    ((1, 0), (2, 0), $alpha_1$),
    ((2, 0), (3, 0), $beta_1$),
    ((3, 0), (4, 0), []),
    ((0, 1), (1, 1), []),
    ((1, 1), (2, 1), $alpha_2$),
    ((2, 1), (3, 1), $beta_2$),
    ((3, 1), (4, 1), []),
    ((1, 0), (1, 1), $lambda$, right),
    ((2, 0), (2, 1), $mu$, right),
    ((3, 0), (3, 1), $nu$),
  ),
  spacing: (9mm, 12mm),
))
#let factorization-refined = view(graph(
  (
    ((0, 0), $0$),
    ((1, 0), $L_1$),
    ((2, 0), $M_1$),
    ((3, 0), $N_1$),
    ((4, 0), $0$),
    ((0, 1), $0$),
    ((1, 1), $L_2$),
    ((2, 1), $X$),
    ((3, 1), $N_1$),
    ((4, 1), $0$),
    ((0, 2), $0$),
    ((1, 2), $L_2$),
    ((2, 2), $Y$),
    ((3, 2), $N_1$),
    ((4, 2), $0$),
    ((0, 3), $0$),
    ((1, 3), $L_2$),
    ((2, 3), $M_2$),
    ((3, 3), $N_2$),
    ((4, 3), $0$),
  ),
  (
    ((0, 0), (1, 0), []),
    ((1, 0), (2, 0), $alpha_1$),
    ((2, 0), (3, 0), $beta_1$),
    ((3, 0), (4, 0), []),
    ((0, 1), (1, 1), []),
    ((1, 1), (2, 1), []),
    ((2, 1), (3, 1), []),
    ((3, 1), (4, 1), []),
    ((0, 2), (1, 2), []),
    ((1, 2), (2, 2), []),
    ((2, 2), (3, 2), []),
    ((3, 2), (4, 2), []),
    ((0, 3), (1, 3), []),
    ((1, 3), (2, 3), $alpha_2$, right),
    ((2, 3), (3, 3), $beta_2$, right),
    ((3, 3), (4, 3), []),
    ((1, 0), (1, 1), $lambda$, right),
    ((1, 1), (1, 2), $1$, right),
    ((1, 2), (1, 3), $1$, right),
    ((2, 0), (2, 1), $mu_1$, right),
    ((2, 1), (2, 2), $mu_2$, right),
    ((2, 2), (2, 3), $mu_3$, right),
    ((3, 0), (3, 1), $1$),
    ((3, 1), (3, 2), $1$),
    ((3, 2), (3, 3), $nu$),
  ),
  spacing: (9mm, 10mm),
))
