#import "02-hom-tensor.typ": graph, view

#let lifting-graph(full: false) = {
  let top = if full {
    (((0, 0), $1$), ((1, 0), $A$))
  } else { () }
  let arrows = if full {
    (((0, 0), (1, 0), []), ((1, 0), (2, 0), []))
  } else { () }
  graph(
    top
      + (
        ((2, 0), $E$),
        ((3, 0), $G$),
        ((4, 0), $1$),
        ((0, 1), $1$),
        ((1, 1), $K^bullet 1_M$),
        ((2, 1), $op("GL")(M)$),
        ((3, 1), $op("PGL")(M)$),
        ((4, 1), $1$),
      ),
    arrows
      + (
        ((2, 0), (3, 0), $pi$),
        ((3, 0), (4, 0), []),
        ((0, 1), (1, 1), []),
        ((1, 1), (2, 1), []),
        ((2, 1), (3, 1), $omega$, right),
        ((3, 1), (4, 1), []),
        ((2, 0), (2, 1), $lambda$, right),
        ((3, 0), (3, 1), $tau$, right),
      ),
    spacing: (18mm, 13mm),
  )
}
#let projective-lifting = view(lifting-graph())
#let projective-lifting-full = view(lifting-graph(full: true))

#let universal-extension = view(graph(
  (
    ((2, 0), $E$),
    ((3, 0), $G$),
    ((4, 0), $1$),
    ((0, 1), $1$),
    ((1, 1), $B$),
    ((2, 1), $E^*$),
    ((3, 1), $G^*$),
    ((4, 1), $1$),
  ),
  (
    ((2, 0), (3, 0), $pi$),
    ((3, 0), (4, 0), []),
    ((0, 1), (1, 1), []),
    ((1, 1), (2, 1), []),
    ((2, 1), (3, 1), $pi^*$, right),
    ((3, 1), (4, 1), []),
    ((2, 0), (2, 1), $lambda$, right),
    ((3, 0), (3, 1), $theta$, right),
  ),
  spacing: (16mm, 12mm),
))

#let identity-extension-graph(kernel-map: false) = graph(
  (
    ((0, 0), $1$),
    ((1, 0), $A$),
    ((2, 0), $E$),
    ((3, 0), $G$),
    ((4, 0), $1$),
    ((0, 1), $1$),
    ((1, 1), $B$),
    ((2, 1), $E^*$),
    ((3, 1), $G$),
    ((4, 1), $1$),
  ),
  (
    ((0, 0), (1, 0), []),
    ((1, 0), (2, 0), []),
    ((2, 0), (3, 0), if kernel-map { [] } else { $pi$ }),
    ((3, 0), (4, 0), []),
    ((0, 1), (1, 1), []),
    ((1, 1), (2, 1), []),
    ((2, 1), (3, 1), if kernel-map { [] } else { $pi^*$ }, right),
    ((3, 1), (4, 1), []),
    ((2, 0), (2, 1), $lambda$, right),
    ((3, 0), (3, 1), $1$, right),
  )
    + if kernel-map { (((1, 0), (1, 1), $phi$, right),) } else { () },
  spacing: (14mm, 12mm),
)
#let universal-identity-lift = view(identity-extension-graph())
#let universal-kernel-lift = view(identity-extension-graph(kernel-map: true))

#let hochschild-serre-sequence = view(graph(
  (
    ((0, 0), $1$),
    ((1, 0), $op("Hom")(G,B)$),
    ((2, 0), $op("Hom")(E,B)$),
    ((3, 0), $op("Hom")(A,B)$),
    ((4, 0), $H^2(G,B)$),
    ((5, 0), $H^2(E,B)$),
  ),
  (
    ((0, 0), (1, 0), []),
    ((1, 0), (2, 0), $op("inf")$),
    ((2, 0), (3, 0), $op("res")$),
    ((3, 0), (4, 0), $t$),
    ((4, 0), (5, 0), $op("inf")$),
  ),
  spacing: (8mm, 10mm),
))
