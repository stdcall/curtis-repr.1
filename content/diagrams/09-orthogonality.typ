#import "@preview/fletcher:0.5.8": diagram, edge, node

// Physical223/printed201. Four nodes and four edges; theta is dashed.
#let frobenius-injective-hull-diagram = block(
  width: 100%,
  align(center, diagram(
    spacing: (23mm, 14mm),
    node-inset: 2pt,
    node-defocus: 0,
    node((-1, 0), $0$),
    node((0, 0), $M$),
    node((1, 0), $E$),
    node((0, 1), $A e$),
    edge((-1, 0), (0, 0), "-|>"),
    edge((0, 0), (1, 0), $j$, "-|>", label-side: left),
    edge((0, 0), (0, 1), $i$, "-|>", label-side: right),
    edge((1, 0), (0, 1), $theta$, "--|>", label-side: right),
  )),
)

// Physical235/printed213. Character-table schematic, author row/column
// labels retained. Native matrix augmentation draws the two rules.
#let character-table-diagram = $
  bold(Z)=mat(
    delim: #none,
    augment: #(hline: 1, vline: 1),
    "", frak(C)_1, dots.c, frak(C)_j, dots.c, frak(C)_s;
    zeta^((1)), "", "", dots.v, "", "";
    dots.v, "", "", dots.v, "", "";
    zeta^((i)), dots.c, dots.c, zeta_j^((i)), dots.c, dots.c;
    dots.v, "", "", dots.v, "", "";
    zeta^((s)), "", "", dots.v, "", "" ;
  )
$

// Physical242/printed220, six native character tables. The S3 final entry
// is corrected from the printed 2 to -1.
#let s3-character-table = $
  S_3:mat(
    delim: #none, augment: #(hline: 1, vline: 1),
    "", x_1, x_2, x_3;
    zeta^1, 1, 1, 1;
    zeta^2, 1, -1, 1;
    zeta^3, 2, 0, -1;
  )
$

#let d4-character-table = $
  D_4:mat(
    delim: #none, augment: #(hline: 1, vline: 1),
    "", x_1, x_2, x_3, x_4, x_5;
    zeta^1, 1, 1, 1, 1, 1;
    zeta^2, 1, -1, 1, -1, 1;
    zeta^3, 1, 1, -1, -1, 1;
    zeta^4, 1, -1, -1, 1, 1;
    zeta^5, 2, 0, 0, 0, -2;
  )
$

#let a4-character-table = $
  A_4:mat(
    delim: #none, augment: #(hline: 1, vline: 1),
    "", x_1, x_2, x_3, x_4;
    zeta^1, 1, 1, 1, 1;
    zeta^2, 3, -1, 0, 0;
    zeta^3, 1, 1, epsilon, epsilon^2;
    zeta^4, 1, 1, epsilon^2, epsilon;
  )
$

#let s4-character-table = $
  S_4:mat(
    delim: #none, augment: #(hline: 1, vline: 1),
    "", x_1, x_2, x_3, x_4, x_5;
    zeta^1, 1, 1, 1, 1, 1;
    zeta^2, 1, -1, 1, -1, 1;
    zeta^3, 2, 0, -1, 0, 2;
    zeta^4, 3, 1, 0, -1, -1;
    zeta^5, 3, -1, 0, 1, -1;
  )
$

#let cube-rotation-character-table = [
  $Gamma$, the group of rotations of the cube:
  $
    mat(
      delim: #none, augment: #(hline: 1, vline: 1),
      "", x_1, x_2, x_3, x_4, x_5;
      zeta^1, 1, 1, 1, 1, 1;
      zeta^2, 1, 1, 1, -1, -1;
      zeta^3, 3, -1, 0, 1, -1;
      zeta^4, 2, 2, -1, 0, 0;
      zeta^5, 3, -1, 0, -1, 1;
    )
  $
]

#let s5-character-table = $
  S_5:mat(
    delim: #none, augment: #(hline: 1, vline: 1),
    "", x_1, x_2, x_3, x_4, x_5, x_6, x_7;
    zeta^1, 1, 1, 1, 1, 1, 1, 1;
    zeta^2, 1, -1, 1, 1, -1, -1, 1;
    zeta^3, 4, 2, 1, 0, 0, -1, -1;
    zeta^4, 4, -2, 1, 0, 0, 1, -1;
    zeta^5, 5, 1, -1, 1, -1, 1, 0;
    zeta^6, 5, -1, -1, 1, 1, -1, 0;
    zeta^7, 6, 0, 0, -2, 0, 0, 1;
  )
$
