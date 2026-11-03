#import "@preview/fletcher:0.5.8": diagram, edge, node

#let trace-base-change-diagram() = diagram(
  spacing: (43mm, 16mm),
  node-inset: 2pt,
  node-defocus: 0,
  node((0, 0), $E(M)$),
  node((1, 0), $E(Gamma times.o_Lambda M)$),
  node((0, 1), $Lambda^ast$),
  node((1, 1), $Gamma^ast$),
  edge((0, 0), (1, 0), "-|>"),
  edge((0, 0), (0, 1), $T$, "-|>", label-side: right),
  edge((1, 0), (1, 1), $T'$, "-|>", label-side: right),
  edge((0, 1), (1, 1), $phi^ast$, "-|>", label-side: left),
)

#let projective-induction-diagram() = block(width: 100%, align(center, diagram(
  spacing: (46mm, 17mm),
  node-inset: 2pt,
  node-defocus: 0,
  node((0, 0), $K_0(R H_i)$),
  node((1, 0), $op("ch")K H_i$),
  node((0, 1), $K_0(R G)$),
  node((1, 1), $op("ch")K G$),
  edge((0, 0), (1, 0), $tau_i$, "-|>", label-side: left),
  edge((0, 1), (1, 1), $tau$, "-|>", label-side: left),
  edge((0, 0), (0, 1), $op("ind")_(H_i)^G$, "-|>", label-side: right),
  edge((1, 0), (1, 1), $op("ind")_(H_i)^G$, "-|>", label-side: left),
)))

#let projective-completion-diagram() = block(width: 100%, align(center, diagram(
  spacing: (44mm, 17mm),
  node-inset: 2pt,
  node-defocus: 0,
  node((0, 0), $K_0(R G)$),
  node((1, 0), $K_0(K G)$),
  node((0, 1), $K_0(hat(R) G)$),
  node((1, 1), $K_0(hat(K) G)$),
  edge((0, 0), (1, 0), $tau$, "-|>", label-side: left),
  edge((0, 1), (1, 1), $hat(tau)$, "-|>", label-side: left),
  edge((0, 0), (0, 1), "-|>"),
  edge((1, 0), (1, 1), "-|>"),
)))

#let projective-extension-diagram() = block(width: 100%, align(center, diagram(
  spacing: (45mm, 17mm),
  node-inset: 2pt,
  node-defocus: 0,
  node((0, 0), $K_0(R G)$),
  node((1, 0), $op("ch")K G$),
  node((0, 1), $K_0(S G)$),
  node((1, 1), $op("ch")K' G$),
  edge((0, 0), (1, 0), $tau$, "-|>", label-side: left),
  edge((0, 1), (1, 1), $tau'$, "-|>", label-side: left),
  edge((0, 0), (0, 1), $alpha$, "-|>", label-side: right),
  edge((1, 0), (1, 1), $beta$, "-|>", label-side: right),
)))

#let projective-reduction-diagram() = block(width: 100%, align(center, diagram(
  spacing: (39mm, 17mm),
  node-inset: 2pt,
  node-defocus: 0,
  node((0, 0), $K_0(R G)$),
  node((1, 0), $K_0(overline(R) G)$),
  node((2, 0), $K_0(overline(R) G slash op("rad") overline(R) G)$),
  node((0, 1), $K_0(S G)$),
  node((1, 1), $K_0(overline(S) G)$),
  node((2, 1), $K_0(overline(S) G slash op("rad") overline(S) G)$),
  edge((0, 0), (1, 0), "-|>"),
  edge((1, 0), (2, 0), "-|>"),
  edge((0, 1), (1, 1), "-|>"),
  edge((1, 1), (2, 1), "-|>"),
  edge((0, 0), (0, 1), $alpha$, "-|>", label-side: right),
  edge((1, 0), (1, 1), "-|>"),
  edge((2, 0), (2, 1), $overline(alpha)$, "-|>", label-side: right),
)))
