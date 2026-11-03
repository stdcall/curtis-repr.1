#import "../main-defs.typ": *
#import "@preview/fletcher:0.5.8": diagram, edge, node

#let cyclic-extension-partition() = align(center, grid(
  columns: (auto, auto, auto),
  column-gutter: 0.2em,
  row-gutter: 0.25em,
  align: center,
  [$display(xi=vec(bold(F)_0, bold(F)_1, bold(F)_2, delim: "[")=)$],
  [$display(
    mat(
      delim: "[", bold(I), 0;
      bold(F)_(11), bold(F)_(12); bold(F)_(21), bold(F)_(22)
    )
  )$],
  [$display(vec(a, b, c, delim: #none))$],

  [], [$display(mat(a, s-a, delim: #none))$], [],
))

#let extension-rows(rows, verticals, horizontal-labels: ()) = {
  let vertices = ()
  let arrows = ()
  for (y, row) in rows.enumerate() {
    vertices.push(node((-0.65, y), row.at(0)))
    for (x, value) in (
      [$0$],
      row.at(1),
      row.at(2),
      row.at(3),
      [$0$],
    ).enumerate() {
      vertices.push(node((x, y), value))
    }
    for x in range(4) {
      let caption = horizontal-labels.find(it => it.at(0) == (x, y))
      if caption == none {
        arrows.push(edge((x, y), (x + 1, y), "->"))
      } else {
        arrows.push(edge((x, y), (x + 1, y), caption.at(1), "->"))
      }
    }
  }
  for arrow in verticals {
    if arrow.len() == 2 {
      arrows.push(edge(arrow.at(0), arrow.at(1), "->"))
    } else {
      arrows.push(edge(
        arrow.at(0),
        arrow.at(1),
        arrow.at(2),
        "->",
        label-side: if arrow.at(0).at(1) < arrow.at(1).at(1) { right } else {
          left
        },
      ))
    }
  }
  align(center, diagram(
    spacing: (13mm, 9mm),
    node-inset: 2pt,
    node-defocus: 0,
    ..vertices,
    ..arrows,
  ))
}

#let extension-isomorphism-initial() = extension-rows(
  (([$(xi)$], [$L$], [$M$], [$N$]), ([$(xi')$], [$L'$], [$M'$], [$N'$])),
  (((2, 0), (2, 1), [$phi$]),),
  horizontal-labels: (
    ((1, 0), [$alpha$]),
    ((1, 1), [$alpha'$]),
    ((2, 1), [$beta'$]),
  ),
)

#let extension-isomorphism-factorization() = extension-rows(
  (
    ([$(xi)$], [$L$], [$M$], [$N$]),
    ([$(eta_1)$], [$L'$], [$M_1$], [$N$]),
    ([$(eta_2)$], [$L'$], [$M_2$], [$N$]),
    ([$(xi')$], [$L'$], [$M'$], [$N'$]),
  ),
  (
    ((1, 0), (1, 1), [$lambda$]),
    ((2, 0), (2, 1)),
    ((3, 0), (3, 1), [$1$]),
    ((1, 1), (1, 2), [$1$]),
    ((2, 1), (2, 2)),
    ((3, 1), (3, 2), [$1$]),
    ((1, 2), (1, 3), [$1$]),
    ((2, 2), (2, 3)),
    ((3, 2), (3, 3), [$nu$]),
  ),
  horizontal-labels: (((1, 0), [$alpha$]), ((2, 3), [$beta'$])),
)

#let extension-standard-pushout() = extension-rows(
  (([$(xi)$], [$L$], [$M$], [$N$]), ([$(f xi)$], [$L'$], [$M_0$], [$N$])),
  (((1, 0), (1, 1), [$f$]), ((2, 0), (2, 1)), ((3, 0), (3, 1), [$1$])),
  horizontal-labels: (((1, 0), [$alpha$]),),
)

#let extension-standard-pullback() = extension-rows(
  (
    ([$(f xi)$], [$L'$], [$M_0$], [$N$]),
    ([$(f xi)g$], [$L'$], [$M'$], [$N'$]),
  ),
  (((1, 1), (1, 0), [$1$]), ((2, 1), (2, 0)), ((3, 1), (3, 0), [$g$])),
  horizontal-labels: (((2, 0), [$beta$]),),
)

#let extension-standard-change-kernel() = extension-rows(
  (([$(xi)$], [$L$], [$M$], [$N$]), ([$(f xi)$], [$L'$], [$M'$], [$N$])),
  (((1, 0), (1, 1), [$f$]), ((2, 0), (2, 1), [$g$]), ((3, 0), (3, 1), [$1$])),
)

#let extension-fibre-square() = align(center, diagram(
  spacing: (20mm, 10mm),
  node-inset: 2pt,
  node-defocus: 0,
  node((0, 0), $E$),
  node((1, 0), $ZZ$),
  node((0, 1), $R_1$),
  node((1, 1), $overline(ZZ)$),
  edge((0, 0), (1, 0), $mu_0$, "->"),
  edge((0, 0), (0, 1), $mu_1$, "->", label-side: right),
  edge((1, 0), (1, 1), "->"),
  edge((0, 1), (1, 1), "->"),
))

#let extension-unit-change() = extension-rows(
  (
    ([$1 plus.o lambda^k:$], [$ZZ plus.o E$], [$M$], [$R_2$]),
    ([$1 plus.o lambda^k overline(u):$], [$ZZ plus.o E$], [$M'$], [$R_2$]),
  ),
  (((1, 0), (1, 1), [$(1,u)$]), ((2, 0), (2, 1)), ((3, 0), (3, 1), [$1$])),
)

#let metacyclic-fibre-square() = align(center, diagram(
  spacing: (23mm, 10mm),
  node-inset: 2pt,
  node-defocus: 0,
  node((0, 0), $ZZ G$),
  node((1, 0), $R compose H$),
  node((0, 1), $ZZ H$),
  node((1, 1), $overline(ZZ)H$),
  edge((0, 0), (1, 0), "->"),
  edge((0, 0), (0, 1), "->"),
  edge((1, 0), (1, 1), "->"),
  edge((0, 1), (1, 1), "->"),
))

#let extension-exercise-isomorphism() = extension-rows(
  (
    ([], [$L^((r))$], [$M$], [$overline(ZZ)^((s))$]),
    ([], [$L^((r))$], [$M'$], [$overline(ZZ)^((s))$]),
  ),
  (
    ((1, 0), (1, 1), [$lambda$]),
    ((2, 0), (2, 1), [$mu$]),
    ((3, 0), (3, 1), [$nu$]),
  ),
)
