#import "02-hom-tensor.typ": graph, view
#import "@preview/fletcher:0.5.8": diagram, edge, node

#let projective-quotient-sequence = view(graph(
  (
    ((0, 0), $0$),
    ((1, 0), $N$),
    ((2, 0), $P$),
    ((3, 0), $P slash N$),
    ((4, 0), $0$),
  ),
  (
    ((0, 0), (1, 0), []),
    ((1, 0), (2, 0), []),
    ((2, 0), (3, 0), []),
    ((3, 0), (4, 0), []),
  ),
))
#let projective-quotient-reduction = view(graph(
  (((0, 0), $phi:P$), ((1, 0), $P slash N$), ((2, 0), $overline(P slash N)$)),
  (((0, 0), (1, 0), []), ((1, 0), (2, 0), [])),
))
#let projective-summand-lifting = view(diagram(
  spacing: (14mm, 10mm),
  node-inset: 2pt,
  node-defocus: 0,
  node((0, 0), $P$),
  node((1, 0), $M$),
  node((0, 1), $overline(P)$),
  node((1, 1), $overline(M)$),
  edge((0, 0), (0, 1), $alpha$, "-|>", label-side: right),
  edge((1, 0), (1, 1), $beta$, "-|>", label-side: right),
  edge((0, 1), (1, 1), $i$, "-|>", shift: 2pt, label-side: left),
  edge((1, 1), (0, 1), $j$, "-|>", shift: 2pt, label-side: left),
))

#let green-character-table-h = block(breakable: false)[
  #align(center)[*Character Table of $H$*]
  #table(
    columns: (1fr, auto, auto, 2fr, 2fr),
    align: center + horizon,
    stroke: none,
    table.hline(y: 1, start: 1, end: 5, stroke: 0.5pt),
    table.hline(y: 2, start: 1, end: 5, stroke: 0.5pt),
    table.hline(y: 5, start: 1, end: 5, stroke: 0.5pt),
    table.vline(x: 2, start: 0, end: 8, stroke: 0.5pt),
    table.vline(x: 3, start: 0, end: 8, stroke: 0.5pt),
    table.vline(x: 4, start: 0, end: 8, stroke: 0.5pt),
    table.header(
      [], [], [$1$], [Classes of $p$-elements], [Classes of $p'$-elements]
    ),
    [], [$1_H$], [$1$], [], [],
    table.cell(rowspan: 3)[Characters nontrivial on $D$], [$psi_1$], [$e$],
    table.cell(rowspan: 3)[$upright(bold(A))$],
    table.cell(rowspan: 3)[$ast$],
    [$dots.v$], [$dots.v$],
    [$psi_n$], [$e$],
    table.cell(rowspan: 3)[Nonprincipal characters trivial on $D$],
    [$mu_1$], [$1$],
    table.cell(rowspan: 3)[$upright(bold(B))$],
    table.cell(rowspan: 3)[$ast$],
    [$dots.v$], [$dots.v$],
    [$mu_(e-1)$], [$1$],
  )
]

#let green-character-table-g = block(breakable: false)[
  #align(center)[*Character Table of $G$*]
  #table(
    columns: (auto, auto, 1fr, 1fr),
    align: center + horizon,
    stroke: none,
    table.hline(y: 1, stroke: 0.5pt),
    table.hline(y: 2, stroke: 0.5pt),
    table.hline(y: 5, stroke: 0.5pt),
    table.hline(y: 8, stroke: 0.5pt),
    table.vline(x: 1, start: 0, end: 11, stroke: 0.5pt),
    table.vline(x: 2, start: 0, end: 11, stroke: 0.5pt),
    table.vline(x: 3, start: 0, end: 11, stroke: 0.5pt),
    table.header(
      [], [$1$], [Classes of $p$-elements], [Classes of $p'$-elements]
    ),
    [$1_G$], [$1$], [], [],
    [$zeta_1$], [$plus.minus e (p)$],
    table.cell(rowspan: 3)[$epsilon upright(bold(A))$],
    table.cell(rowspan: 3)[
      $arrow.t$ \
      constant values on each class \
      $arrow.b$
    ],
    [$dots.v$], [$dots.v$],
    [$zeta_n$], [$plus.minus e (p)$],
    [$theta_1$], [$plus.minus 1 (p)$],
    table.cell(rowspan: 3)[$upright(bold(B))'$],
    table.cell(rowspan: 3)[$ast$],
    [$dots.v$], [$dots.v$],
    [$theta_(e-1)$], [$plus.minus 1 (p)$],
    [$chi_1$], [$equiv 0 (|D|)$],
    table.cell(rowspan: 3)[$0$],
    table.cell(rowspan: 3)[$ast$],
    [$dots.v$], [$dots.v$],
    [$chi_h$], [$equiv 0 (|D|)$],
  )
]

