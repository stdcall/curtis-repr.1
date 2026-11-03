#import "@preview/fletcher:0.5.8": diagram, edge, node

// Inclusion and projection of a homogeneous induced summand.
#let graded-summand-inclusion-projection = block(
  width: 100%,
  align(center, diagram(
    spacing: 35mm,
    node-inset: 2pt,
    node-defocus: 0,
    node((0, 0), $a_s times.o L$),
    node((1, 0), $L^A.$),
    edge((0, 0), (1, 0), $mu_s$, "-|>", shift: 1.5pt, label-side: left),
    edge((1, 0), (0, 0), $pi_s$, "-|>", shift: 1.5pt, label-side: left),
  )),
)
