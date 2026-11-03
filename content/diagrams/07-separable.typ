#import "@preview/fletcher:0.5.8": diagram, edge, node

// Physical174: four objects, three solid right arrows. All labels above.
// The initial superscript-sigma T is the name of the whole composite.
#let galois-conjugate-representation-diagram = block(
  align(center, [
    $attach(bold(T), tl: sigma):$
    #diagram(
      spacing: (17mm, 12mm),
      node((0, 0), $A^E$),
      node((1, 0), $A^E$),
      node((2, 0), $M_n lr((E))$),
      node((3, 0), $M_n lr((E))$),
      edge((0, 0), (1, 0), $sigma^(-1) times.o 1$, "-|>"),
      edge((1, 0), (2, 0), $bold(T)$, "-|>"),
      edge((2, 0), (3, 0), $sigma$, "-|>"),
    ),
  ]),
)
