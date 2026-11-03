#import "main-defs.typ": *
#import "statements.typ": *
#import "diagrams/08-ext-tor.typ": *

== Ext, Tor; Cohomology of Groups <sec:ext-tor-cohomology>

=== Ext, Tor <ss:ext-tor>

In this section we shall give the definitions of the groups $op("Ext")^n$ and
$op("Tor")_n$, and shall list some of their most important properties. For
proofs and details, the reader may consult the references listed at the end of
@sec:hom-tensor-projective-injective-flat before the exercises.

Let $A$ be a ring; until further notice, all $A$-modules are assumed to be left
$A$-modules. Given any $A$-module, $N$, choose a surjection $phi_0: F_0 -> N$
with $F_0$ free. Then choose a surjection $phi_1: F_1 -> ker phi_0$, with $F_1$
free, etc. This yields a _free resolution_#idx("free resolution") of $N$:
$ dots -> F_2 arrow.r^(phi_2) F_1 arrow.r^(phi_1) F_0 arrow.r^(phi_0) N -> 0, $
#source(194)
namely, an exact sequence in which each $F_j$ is free. It is often desirable to
work instead with a more general concept: a _projective resolution_#idx(
  "projective resolution",
) of $N$ is an exact sequence
$
  dots -> P_2 arrow.r^(phi_2) P_1 arrow.r^(phi_1) P_0 arrow.r^(phi_0) N -> 0
$ <eq:projective-resolution>
in which each $P_i$ is projective. It should be remarked that if the ring $A$ is
left noetherian, and $N$ is f.g., then we may choose the resolution
@eq:projective-resolution so that each $P_i$ is f.g.

Now let $L$ be any other $A$-module, and form the sequence of additive groups
$
  0 -> Hom(P_0, L) arrow.r^(phi_1^*) Hom(P_1, L)
  arrow.r^(phi_2^*) Hom(P_2, L) -> dots,
$ <eq:hom-projective-resolution>
where the $phi_i^*$ are defined as in @eq:hom-contravariant-map, and where $Hom$
means $Hom_A$. Then
$ phi_(i+1)^* phi_i^* = (phi_i phi_(i+1))^* = 0, i >= 1, $
so
$ im phi_i^* subset.eq ker phi_(i+1)^*, i >= 1. $
We define
$
  op("Ext")_A^n lr((N,L)) = frac(ker phi_(n+1)^*, im phi_n^*), n >= 1.
$ <eq:ext-definition>
#idx("Ext", target: [@eq:ext-definition])
This yields a family of additive groups $op("Ext")_A^1 lr((N,L))$,
$op("Ext")_A^2 lr((N,L))$, and so on. Below we shall give an interpretation of
$op("Ext")^1$ in terms of extensions of modules. For the moment, however, there
are a number of comments which must be made.

#remarks[
  #enum(
    numbering: "(i)",
    [Up to natural isomorphisms, the groups $op("Ext")_A^n lr((N,L))$ depend
      only upon the modules $N$ and $L$, and not upon the choice of the
      projective resolution of $N$.],
    [We could have defined $op("Ext")_A^0 lr((N,L))$ as $ker phi_1^*$. However,
      $
        0 -> Hom(N, L) arrow.r^(phi_0^*) Hom(P_0, L)
        arrow.r^(phi_1^*) Hom(P_1, L)
      $
      is exact by @prop:hom-left-exact, whence
      $ker phi_1^* tilde.equiv Hom(N, L)$. It is customary to identify
      $op("Ext")_A^0 lr((N,L))$ with $Hom_A lr((N,L))$.],
    [The groups $op("Ext")_A^n lr((N,L))$ can also be computed by using an
      injective resolution of $L$. Specifically, let $psi_0: L -> Q_0$ be an
      embedding of $L$ in the
      #source(195)
      injective module $Q_0$. Then let $psi_1: "cok" psi_0 -> Q_1$ embed the
      cokernel of $psi_0$ in an injective module $Q_1$, and so on. We obtain an
      exact sequence
      $
        0 -> L arrow.r^(psi_0) Q_0 arrow.r^(psi_1) Q_1
        arrow.r^(psi_2) Q_2 -> dots
      $ <eq:injective-resolution>
      in which each $Q_i$ is injective; this sequence is called an _injective
      resolution_#idx("injective resolution") of $L$.

      Now apply $Hom_A lr((N,ast))$, obtaining a new sequence
      $
        0 -> Hom(N, Q_0) arrow.r^((psi_1)_*) Hom(N, Q_1)
        arrow.r^((psi_2)_*) Hom(N, Q_2) -> dots
      $
      in which $(psi_(i+1))_* (psi_i)_* = 0$ for $i >= 1$. It turns out that
      $
        op("Ext")_A^n lr((N,L)) tilde.equiv
        frac(ker (psi_(n+1))_*, im (psi_n)_*), n >= 1,
      $
      and that $ker (psi_1)_* tilde.equiv Hom_A lr((N,L))$.],
    [The groups $op("Ext")^n lr((N,L))$, $n >= 1$, have many of the same
      properties as $Hom(N, L)$. For example, $op("Ext")^n$ is additive in each
      variable separately, and is contravariant in the first variable and
      covariant in the second variable. Thus, each $f in Hom(N, N')$ induces
      additive homomorphisms
      $ (f_n)^*: op("Ext")_A^n lr((N',L)) -> op("Ext")_A^n lr((N,L)), n >= 1, $
      and likewise for $g: L -> L'$.],
    [If $N$ is a projective module, then $0 -> N -> N -> 0$ is a projective
      resolution of $N$. From Definition @eq:ext-definition we conclude that
      $op("Ext")_A^n lr((N,ast))=0$ for $n >= 1$, that is,
      $op("Ext")_A^n lr((N,L))=0$ for all $L$ and all $n >= 1$. Conversely, it
      is easily shown that if $op("Ext")^1 lr((N,ast))=0$ then $N$ is
      projective.

      Analogously, if $L$ is injective then $op("Ext")^n lr((ast,L))=0$ for
      $n >= 1$. Conversely, if $op("Ext")^1 lr((ast,L))=0$ then $L$ is
      injective.],
  )
] <rem:ext-properties>

One of the most important properties of $op("Ext")$, and one of the most useful
for purposes of calculation, is the following:

#theorem(title: [Long exact sequence for Ext])[
  Let
  $ 0 -> L arrow.r^f M arrow.r^g N -> 0 $ <eq:ext-short-exact-sequence>
  be any short exact sequence of left $A$-modules, and let $X$ be any left
  $A$-module.
  #source(196)
  Then there is a long exact sequence of additive groups
  $
    0 -> Hom(N, X) arrow.r^(g^*) Hom(M, X) arrow.r^(f^*) Hom(L, X)
    arrow.r^∂ op("Ext")^1 lr((N,X)) \
    arrow.r^(g^*) op("Ext")^1 lr((M,X)) arrow.r^(f^*) op("Ext")^1 lr((L,X))
    arrow.r^∂ op("Ext")^2 lr((N,X)) \
    arrow.r^(g^*) op("Ext")^2 lr((M,X)) arrow.r^(f^*) op("Ext")^2 lr((L,X))
    arrow.r^∂ op("Ext")^3 lr((N,X)) -> dots.
  $ <eq:ext-long-exact-first-variable>
] <th:ext-long-exact-sequence>
#idx("long exact sequence for Ext", target: [@th:ext-long-exact-sequence])

#remarks[
  #enum(
    numbering: "(i)",
    [We have written $Hom$, $op("Ext")$ in place of $Hom_A$, $op("Ext")_A$, for
      brevity. We have omitted the subscripts on the various maps $f^*$, $g^*$,
      $∂$.],
    [This result should be compared with Prop. @prop:hom-left-exact. Given the
      exact sequence @eq:ext-short-exact-sequence, Proposition
      @prop:hom-left-exact asserts the exactness of the part of
      @eq:ext-long-exact-first-variable up to the first $op("Ext")$ term. The
      present theorem may be viewed as an extension of Prop.
      @prop:hom-left-exact.],
    [If $M$ is projective then $op("Ext")^1 lr((M,X))=0$, and we obtain
      $
        op("Ext")^1 lr((N,X)) tilde.equiv
        frac(Hom_A lr((L,X)), f^* {Hom_A lr((M,X))}).
      $
      We shall give below another interpretation of this formula, and thereby
      explain the significance of the “connecting homomorphism”#idx(
        "connecting homomorphism",
      )
      $ ∂_0: Hom_A lr((L,X)) -> op("Ext")_A^1 lr((N,X)). $
      Corresponding interpretations of the higher $∂$'s are less easily given,
      and we do not attempt this here.],
    [Let $Y$ be any left $A$-module, and let @eq:ext-short-exact-sequence be
      exact. Then there is a long exact sequence of additive groups
      $
        0 -> Hom(Y, L) arrow.r^(f_*) Hom(Y, M) arrow.r^(g_*) Hom(Y, N)
        arrow.r^∂ op("Ext")^1 lr((Y,L)) \
        arrow.r^(f_*) op("Ext")^1 lr((Y,M)) arrow.r^(g_*) op("Ext")^1 lr((Y,N))
        arrow.r^∂ op("Ext")^2 lr((Y,L)) -> dots.
      $ <eq:ext-long-exact-second-variable>],
  )
] <rem:ext-long-exact-sequence>

We conclude this informal discussion with a theorem on finite generation of
extension groups. Let $R$ be a commutative ring, and let $A$ be an $R$-algebra;
then $A$ itself, and all $A$-modules, can be viewed as $R$-modules. If
$L,M,dots$ are $A$-modules, then all of the additive groups $Hom_A lr((L,M))$,
$op("Ext")_A^n lr((L,M))$, $n >= 1$, are $R$-modules, and all of the maps
mentioned above are $R$-homomorphisms.

#source(197)
In particular, let $R$ be a noetherian commutative ring and let $A$ be an
$R$-algebra which is finitely generated as $R$-module. For any $A$-module $N$
which is f.g. over $R$, all of the $A$-modules occurring in a projective
$A$-resolution of $N$ may be chosen f.g. over $R$. From this one easily obtains
(see references for details):

#proposition[
  Let $A$ be an $R$-algebra, f.g. as module over the commutative noetherian ring
  $R$. Let $L,M$ be left $A$-modules which are f.g. over $R$ (or, equivalently,
  over $A$). Then the $R$-modules
  $ Hom_A lr((L,M)), op("Ext")_A^n lr((L,M)), n >= 1, $
  are also f.g. over $R$.
] <prop:ext-finite-generation>

Let us now give an intuitive discussion of $op("Ext")^1$ (for details, see
Rotman @bib:Rotman1979). Let $A$ be an arbitrary ring, and let $L,M,dots$ be
left $A$-modules. An $A$-exact sequence $0 -> L -> X -> N -> 0$ is called an
_extension of $N$ by $L$_#idx("extension of modules")\; sometimes the module $X$
itself is referred to as the extension. Two extensions are _equivalent_#idx(
  "equivalent extensions",
) if there exists a commutative diagram
#equivalent-module-extensions
(The map $theta$ is necessarily an $A$-isomorphism.)

Now let $phi: P -> N$ be a surjection, where $P$ is $A$-projective, and let
$K=ker phi$. Then there is an exact sequence of $A$-modules
$ 0 -> K arrow.r^i P arrow.r^phi N -> 0. $
Hence for each $A$-module $L$, we have an exact sequence
$
  Hom(P, L) arrow.r^(i^*) Hom(K, L) arrow.r^∂ op("Ext")_A^1 lr((N,L)) -> 0.
$ <eq:extension-connecting-hom>
We shall describe $∂$ explicitly. Given any $sigma in Hom(K, L)$, we may form
the pushout $X$ of the pair of maps $\{i,sigma\}$, thereby obtaining a
commutative diagram
#extension-pushout-square

#source(198)
By Exercise @exc:pushout-cokernel we know that $i'$ is injective, and that
$"cok" i tilde.equiv "cok" i'$. Hence we obtain a commutative diagram with exact
rows: #numbered-block(extension-pushout-rows) <eq:extension-pushout-rows>
Thus each $sigma$ determines an extension of $N$ by $L$, namely, the bottom row
of the above diagram. Further, it is easily shown that $sigma$ and $sigma'$
determine equivalent extensions if and only if
$sigma-sigma' in i^* {Hom(P, L)}$. Hence it follows from
@eq:extension-connecting-hom that each element of $op("Ext")_A^1 lr((N,L))$
uniquely determines an equivalence class of extensions of $N$ by $L$.

On the other hand, consider a given extension $0 -> L -> X -> N -> 0$ of $N$ by
$L$. Then in the diagram
#extension-projective-lift
we can choose $tau$ making the right hand square commute, since $P$ is
projective. It is easily seen that $tau$ induces a map $sigma: K -> L$, and we
obtain a commutative diagram as in @eq:extension-pushout-rows. This shows that
_every_ extension of $N$ by $L$ arises by means of the construction in
@eq:extension-pushout-rows. Further, the equivalence class of the extension
determines $sigma$ modulo the image $i^* {Hom(P, L)}$, and we thus obtain a
bijection between $op("Ext")_A^1 lr((N,L))$ and the set of equivalence classes
of extensions of $N$ by $L$.

In terms of the above interpretation of $op("Ext")^1$, we may give an explicit
description of the connecting homomorphism#idx("connecting homomorphism")
$ ∂: Hom_A lr((L,X)) -> op("Ext")_A^1 lr((N,X)) $
occurring in @eq:ext-long-exact-first-variable. Starting with the exact sequence
@eq:ext-short-exact-sequence, and any $nu in Hom_A lr((L,X))$, $∂ nu$ is simply
the equivalence class of the extension of $N$ by $X$ occurring as the bottom row
of the commutative diagram with exact rows:
#connecting-pushout
(Here, $M'$ is the pushout of the pair of maps $\{f,nu\}$).

#source(199)
A brief discussion of the torsion groups $\{op("Tor")_n\}$ is desirable. Let
@eq:projective-resolution be a projective resolution of the left $A$-module $N$,
and let $L$ be any _right_ $A$-module. We form the sequence of additive groups
$
  dots -> L times.o_A P_2 arrow.r^(1 times.o phi_2) L times.o_A P_1
  arrow.r^(1 times.o phi_1) L times.o_A P_0 -> 0.
$
Since $(1 times.o phi_i)(1 times.o phi_(i+1))=1 times.o phi_i phi_(i+1)=0$ for
$i >= 1$, it follows that $im(1 times.o phi_(i+1)) subset.eq
ker(1 times.o phi_i)$ for $i >= 1$. We now define
$
  op("Tor")_n^A lr((L,N)) =
  frac(ker(1 times.o phi_n), im(1 times.o phi_(n+1))), n >= 1.
$
#idx("Tor")
This yields a family of additive groups $\{op("Tor")_n^A lr((L,N)), n >= 1\}$,
about which we note the following:

#remarks[
  #enum(
    numbering: "(i)",
    [Up to natural isomorphisms, the groups $op("Tor")_n^A lr((L,N))$ depend
      only upon the modules $N$ and $L$, and not upon the choice of the
      projective resolution of $N$.],
    [We could have defined $op("Tor")_0^A lr((L,N))$ as
      $"cok"(1 times.o phi_1)$. However, by @prop:tensor-right-exact we find
      that $"cok"(1 times.o phi_1) tilde.equiv L times.o_A N$. It is customary
      to identify $op("Tor")_0^A lr((L,N))$ with $L times.o_A N$.],
    [The groups $op("Tor")_n^A lr((L,N))$ could also be computed using a
      projective resolution of $L$.],
    [The torsion groups $op("Tor")_n^A lr((L,N))$ have many of the properties of
      $L times.o_A N$. For example, $op("Tor")_n$ is covariant and additive in
      each variable. Each $f: L -> L'$ induces maps
      $(f_n)_*: op("Tor")_n lr((L,N)) -> op("Tor")_n lr((L',N))$, and likewise
      for maps $g: N -> N'$.],
    [If $L$ or $N$ is projective, then $op("Tor")_n^A lr((L,N))=0$ for $n >= 1$.
      Indeed, this holds if either $L$ or $N$ is a flat $A$-module. Conversely,
      if $op("Tor")_1^A lr((L,ast))=0$ then $L$ is flat, while if
      $op("Tor")_1^A lr((ast,N))=0$ then $N$ is flat.],
  )
] <rem:tor-properties>

The analogue of @th:ext-long-exact-sequence holds true:

#theorem(title: [Long Exact Sequence for Tor])[
  Let
  $ 0 -> L -> M -> N -> 0 $
  be any short exact sequence of right $A$-modules, and let $X$ be any left
  $A$-module. Then there is a long exact sequence of additive groups
  $
    dots -> op("Tor")_3 lr((N,X)) -> op("Tor")_2 lr((L,X))
    -> op("Tor")_2 lr((M,X)) -> op("Tor")_2 lr((N,X)) \
    -> op("Tor")_1 lr((L,X)) -> op("Tor")_1 lr((M,X))
    -> op("Tor")_1 lr((N,X)) \
    -> L times.o X -> M times.o X -> N times.o X -> 0.
  $
] <th:tor-long-exact-sequence>
#idx("long exact sequence for Tor", target: [@th:tor-long-exact-sequence])

#source(200)
In the above, we have written $times.o$, $op("Tor")$ in place of $times.o_A$,
$op("Tor")^A$, for brevity. This result should be compared with Prop.
@prop:tensor-right-exact, and may be regarded as an extension thereof. Finally,
we note that the analogue of Prop. @prop:ext-finite-generation holds for
$L times.o_A N$ and $op("Tor")_n^A lr((L,N))$, $n >= 1$.

To end this section, we state a “Change of Rings” Theorem for $op("Ext")$ and
$op("Tor")$, which may be viewed as a generalization of the analogous Theorem
@th:change-of-rings for $Hom$. The hypotheses of @th:change-of-rings must be
strengthened slightly, though this causes no difficulty in practice. We have
(see @bib:Reiner1975[MO §~2e] for proof):

#theorem(name: "Change of Rings Theorem")[
  Let $A$ and $B$ be $R$-algebras, where $R$ is a commutative ring. Suppose that
  $A$ is left noetherian and $B$ is $R$-flat. Let $M$ be a finitely generated
  left $A$-module, and $N$ any left $A$-module. Set
  $ A'=B times.o_R A, M'=B times.o_R M, N'=B times.o_R N. $
  Then the two-sided $B$-isomorphism $alpha$ given in @eq:change-of-rings-map is
  the first of a family of two-sided $B$-isomorphisms
  $
    B times.o_R op("Ext")_A^n lr((M,N)) tilde.equiv
    op("Ext")_(A')^n lr((M',N')), n >= 0.
  $ <eq:ext-flat-base-change>
  An analogous result holds with $op("Ext")^n$ replaced by $op("Tor")_n$, with
  $M$ now chosen to be a right $A$-module.
] <th:ext-flat-change-of-rings>
#idx("Change of Rings Theorem", target: [@th:ext-flat-change-of-rings])

We shall often apply @th:ext-flat-change-of-rings to the special case where $B$
is itself a commutative ring $R'$ containing $R$. For example, if $R$ is a
commutative ring and $R'=S^(-1) R$, a ring of quotients of $R$, then $R'$ is
necessarily $R$-flat (see @bib:Reiner1975[MO §~3c]). Thus we obtain:

#corollary[
  Let $A$ be a left noetherian $R$-algebra, where $R$ is a commutative ring. Let
  $M,N$ be left $A$-modules, with $M$ f.g./$A$. Let $S$ be a multiplicative
  subset of $R$. Then
  $
    S^(-1) R times.o_R op("Ext")_A^n lr((M,N)) tilde.equiv
    op("Ext")_(S^(-1) A)^n lr((S^(-1) M,S^(-1) N)), n >= 0.
  $
  If $L$ is a f.g. right $A$-module, then
  $
    S^(-1) R times.o_R op("Tor")_n^A lr((L,N)) tilde.equiv
    op("Tor")_n^(S^(-1) A) lr((S^(-1) L,S^(-1) N)), n >= 0.
  $
] <cor:ext-tor-localization>

We shall use repeatedly the following consequence of the above:

#proposition[
  Let $A$ be a left noetherian $R$-algebra, where $R$ is a commutative ring, and
  let $M$ be a f.g. left $A$-module. For each maximal ideal $P$ of $R$, let the
  subscript $P$ denote localization at $P$. Then $M$ is a projective $A$-module
  if and only if for each $P$, $M_P$ is a projective $A_P$-module.
] <prop:projectivity-localization>

#proof[
  #source(201)
  If $M$ is $A$-projective, then $M$ is a direct summand of a free $A$-module.
  It follows at once that $M_P$ is a direct summand of a free $A_P$-module, and
  is therefore $A_P$-projective. Conversely, if $M_P$ is projective for each
  $P$, then $op("Ext")_A^1 lr((M,ast))=0$ by @cor:ext-tor-localization and
  @prop:localization-criteria, so $M$ is projective by @rem:ext-properties(v).
]

=== Cohomology of Groups <ss:cohomology-groups>

Here we shall define the _cohomology groups_ $H^n lr((G,A))$, and the _homology
groups_ $H_n lr((G,A))$, $n >= 0$, where $G$ is a group acting from the left on
a module $A$. To begin with, let $ZZ G$ denote the integral group ring
consisting of all formal finite sums
$\{sum_(x in G) alpha_x x: alpha_x in ZZ\}$, with addition and multiplication
defined by the formulas
$
  (sum alpha_x x)+(sum beta_x x)=sum(alpha_x+beta_x)x, \
  (sum alpha_x x)(sum beta_y y)=sum_(x,y)(alpha_x beta_y)x y.
$
Let $A$ be a left $G$-module, that is, $A$ is an additive group on which the
elements of $G$ act from the left as additive homomorphisms, such that
$ x(y a)=(x y)a, 1_G a=a "for all" x,y in G, a in A. $
Then we may make $A$ into a left $ZZ G$-module, by defining
$ (sum alpha_x x)a=sum alpha_x lr((x a)), a in A. $
Conversely, every left $ZZ G$-module may also be viewed as a $G$-module.

In the definitions below, a special role is played by the _trivial $G$-module_
$ZZ$; this is the additive group $ZZ$ on which $G$ acts trivially, that is,
$g z=z$ for all $g in G$, $z in ZZ$. For a left $G$-module $A$, we define
$
  H^n lr((G,A))=op("Ext")_(ZZ G)^n lr((ZZ,A)),
  H_n lr((G,A))=op("Tor")_n^(ZZ G) lr((ZZ,A)), n >= 0.
$
To make these definitions more explicit, we shall use a free resolution of the
left $ZZ G$-module $ZZ$. We now proceed to give such a resolution.

For $n >= 0$, let $F_n$ be the free left $ZZ G$-module with free basis
consisting of all ordered $n$-tuples $\{(x_1,dots,x_n): x_i in G\}$. For $n=0$,
we interpret $F_0$ as the free $ZZ G$-module with a single basis element which
is the “empty parentheses” denoted by the symbol $(thin)$; thus
$F_0=ZZ G dot (thin) tilde.equiv ZZ G$. Elements of $F_n$ are finite sums of
terms of the form $xi(x_1, dots, x_n)$, with $xi in ZZ G$, and each $x_i in G$.

Now consider the sequence
$
  dots -> F_n arrow.r^(d_n) F_(n-1) arrow.r^(d_(n-1)) dots
  -> F_1 arrow.r^(d_1) F_0 arrow.r^(d_0) ZZ -> 0,
$ <eq:bar-resolution>
#source(202)
where each $d_n$ is a left $ZZ G$-homomorphism whose action on the given free
basis of $F_n$ is specified as follows:
$
  cases(
    d_0 lr((thin))=1\,,
    d_1 lr((x))=x(thin)-(thin)=(x-1)(thin)\,,
    d_2 lr((x,y))=x(y)-(x y)+(x)\,,
    dots,
    d_n lr((x_1,dots,x_n))=x_1 lr((x_2,dots,x_n))\,,
    quad + sum_(i=1)^(n-1) lr((-1))^i
    lr((x_1,dots,x_(i-1),x_i x_(i+1),dots,x_n))\,,
    quad + (-1)^n lr((x_1,dots,x_(n-1))).
  )
$
It can be verified (see references) that @eq:bar-resolution is an exact sequence
of left $ZZ G$-modules, and hence gives a free $ZZ G$-resolution of the trivial
$G$-module $ZZ$. We now proceed to form $op("Ext")_(ZZ G)^n lr((ZZ,A))$, where
$A$ is any left $ZZ G$-module. To be explicit, we consider the sequence of
additive groups
$
  0 -> Hom_(ZZ G) lr((F_0,A)) arrow.r^((d_1)^*) Hom_(ZZ G) lr((F_1,A))
  arrow.r^((d_2)^*) Hom_(ZZ G) lr((F_2,A)) -> dots.
$
Then $im(d_n)^* subset.eq ker(d_(n+1))^*$, $n >= 1$, and we define
$
  cases(
    H^n lr((G,A))=frac(ker(d_(n+1))^*, im(d_n)^*)
    =op("Ext")_(ZZ G)^n lr((ZZ,A)) quad n >= 1\,,
    H^0 lr((G,A))=ker(d_1)^* tilde.equiv Hom_(ZZ G) lr((ZZ,A)).
  )
$ <eq:group-cohomology-definition>
#idx("cohomology group", target: [@eq:group-cohomology-definition])
We call $H^n lr((G,A))$ the _nth cohomology group of $G$ with coefficients in
the module $A$_.

We shall describe these groups $H^n lr((G,A))$ more concretely. Each
$f in Hom_(ZZ G) lr((F_n,A))$ is completely determined by the images
$\{f(x_1,dots,x_n): x_i in G\}$, that is, by its action on a free $ZZ G$-basis
of $F_n$. Hence we may identify $Hom_(ZZ G) lr((F_n,A))$ with the set of all
functions from $G times dots times G$ into $A$, where the factor $G$ occurs $n$
times. Given a function $f: G times dots times G -> A$, we have
$ d_(n+1)^* f=f d_(n+1) in Hom_(ZZ G) lr((F_(n+1),A)), n >= 0, $
#source(203)
by definition of $d_(n+1)^*$ (see @eq:hom-contravariant-map). Explicitly, we
obtain
$
  cases(
    (d_1^* f)(x)=f d_1 lr((x))=f{(x-1)(thin)}=(x-1)f(thin)\,,
    (d_2^* f)(x,y)=f d_2 lr((x,y))=x f(y)-f(x y)+f(x)\,,
    (d_3^* f)(x,y,z)=x f(y,z)-f(x y,z)+f(x,y z)-f(x,y)\,,
    (d_(n+1)^* f)(x_1,dots,x_(n+1))=x_1 f(x_2,dots,x_(n+1))\,,
    quad +sum_(i=1)^n lr((-1))^i f(x_1,dots,x_(i-1),x_i x_(i+1),dots,x_(n+1))\,,
    quad +(-1)^(n+1)f(x_1,dots,x_n).
  )
$ <eq:cochain-coboundary>
In these formulas, the symbols $x,x_i,y,z$ denote arbitrary elements of the
group $G$, while $f$ ranges over all elements of $Hom_(ZZ G) lr((F_n,A))$ for
various values of $n$.

In particular, $ker d_2^*$ consists of all functions $f: G -> A$ such that
$ f(x y)=x f(y)+f(x) "for all" x,y in G. $ <eq:derivation-condition>
Such functions are called _derivations_#idx("derivation") (or _crossed
homomorphisms_#idx("crossed homomorphism")) from $G$ to $A$. On the other hand,
those functions in $im d_1^*$ are called _principal derivations_#idx(
  "derivation",
  "principal",
)#idx("principal derivation")\; each $g in Hom_(ZZ G) lr((F_0,A))$ determines a
principal derivation $f=d_1^* g$, given by
$ f(x)=(x-1)g(thin), x in G. $
If we set $g(thin)=a in A$, then we have simply
$ f(x)=(x-1)a, x in G. $ <eq:principal-derivation>
Then by definition,
$
  H^1 lr((G,A))=frac("derivations from" G "to" A, "principal derivations").
$ <eq:first-cohomology-derivations>
Later in this book, we shall meet various interpretations of this concept. For
the moment, however, we merely remark that the elements of $H^1 lr((G,A))$
correspond bijectively with classes of those automorphisms of the semidirect
product $A ⋊ G$ which fix $A$ pointwise and induce the identity on the quotient
$G$, modulo inner automorphisms induced by elements of $A$ (see Rotman
@bib:Rotman1979, Theorem~5.11).

Turning next to the group $H^2 lr((G,A))$, we note first that $ker d_3^*$
consists of all functions $f: G times G -> A$ such that
$ x f(y,z)-f(x y,z)+f(x,y z)-f(x,y)=0 $ <eq:factor-set-condition>
#source(204)
for all $x,y,z in G$. Such an $f$ is called a _factor set_#idx("factor set")
from $G$ to $A$. Those factor sets in $im d_2^*$ are called _principal factor
sets_#idx("principal factor set"). Each function $g: G -> A$ determines a
principal factor set $f=d_2^* g$, given by the formula
$ f(x,y)=x g(y)-g(x y)+g(x), forall x,y in G. $ <eq:principal-factor-set>
Then by definition,
$
  H^2 lr((G,A))=frac("factor sets from" G "to" A, "principal factor sets").
$ <eq:second-cohomology-factor-sets>

#example[
  Let $A$ be a $G$-module, written multiplicatively, and consider an exact
  sequence of groups
  $ 1 -> A -> E arrow.r^pi G -> 1. $ <eq:group-extension>
  Thus $A$ is an abelian normal subgroup of $E$, with factor group isomorphic to
  $G$. Let $u: G -> E$ be a $pi$-_section_#idx("section")#footnote[
    $u$ is not necessarily a homomorphism of groups.
  ], that is, $pi(u_x)=x$ for all $x in G$. Since $A lt.closed.eq E$, we have
  $u_x A u_x^(-1)=A$ for all $x in G$. We restrict our attention to those
  extensions @eq:group-extension for which
  $ u_x a u_x^(-1)=x dot a, x in G, a in A, $ <eq:extension-module-action>
  where $x dot a$ indicates the action of $x$ on the element $a$ of the
  $G$-module $A$. (In this case, we shall say that the extension
  @eq:group-extension “respects the $G$-module structure of $A$”.) It should be
  pointed out that if $u': G -> E$ is another section of $pi$, then for each
  $x in G$, $u_x$ and $u'_x$ differ by a factor from $A$; since $A$ is abelian
  by hypothesis, we obtain
  $ u_x a u_x^(-1)=u'_x a (u'_x)^(-1), x in G, a in A, $
  so condition @eq:extension-module-action is independent of the choice of the
  $pi$-section.

  Each element of the group $E$ is uniquely expressible in the form $a u_x$,
  $a in A$, $x in G$, and we have
  $ (a u_x)(b u_y)=(a(x dot b))u_x u_y, a,b in A, x,y in G. $
  Hence the structure of $E$ is completely determined once we know how to
  compute the products $u_x u_y$. It is easily seen that
  $ u_x u_y=f(x,y)u_(x y), x,y in G, $ <eq:extension-factor-set>
  where $f: G times G -> A$. The condition, that multiplication in $E$ be
  associative,
  #source(205)
  turns out to be equivalent to the condition that $f$ be a factor set from $G$
  to $A$. Furthermore, if a section $u'$ is used in place of $u$, we obtain a
  new factor set $f'$, which differs from $f$ by a principal factor set. In this
  manner, each extension @eq:group-extension which respects the module structure
  of $A$ gives rise to a class in $H^2 lr((G,A))$.

  Now introduce the concept of equivalence of extensions: two extensions
  $1 -> A -> E -> G -> 1$, $1 -> A -> E' -> G -> 1$, are called
  _equivalent_#idx("equivalent extensions") if there exists an isomorphism
  $theta: E tilde.equiv E'$ for which the diagram
  #equivalent-group-extensions
  is commutative. It turns out (see Rotman @bib:Rotman1979, Theorem~10.24) that
  there is a bijection between $H^2 lr((G,A))$ and the set of equivalence
  classes of extensions @eq:group-extension which respect the $G$-module
  structure of $A$. This bijection assigns to the class of @eq:group-extension
  the class of the factor set $f$ in $H^2 lr((G,A))$, as described above.
] <exm:group-extensions-second-cohomology>

#examples[
  #enum(
    numbering: "(i)",
    [Let $K$ be a field, and let $L$ be a finite Galois extension of $K$ with
      Galois group $G$, so we may view $L$ as a left $G$-module. We shall define
      an algebra $B=∐_(sigma in G) L u_sigma$, having as $L$-basis a set of
      symbols $\{u_sigma: sigma in G\}$, which are to be manipulated according
      to the formulas
      $
        u_sigma dot l=sigma(l)u_sigma, u_sigma u_tau=f(sigma,tau)u_(sigma tau),
        l in L, sigma,tau in G,
      $
      where each $f(sigma,tau) in L^dot$. (Here, $L^dot$ denotes the
      multiplicative group of nonzero elements of $L$.) The $K$-algebra $B$ will
      be associative if and only if $f$ is a factor set from $G$ to $L^dot$. For
      such a factor set $f$, the algebra $B$ is called a _crossed-product
      algebra_#idx(
        "crossed-product algebra",
      ), and is denoted by $(L slash K,f)$. The isomorphism class of $B$ depends
      only upon the cohomology class of $f$ in $H^2 lr((G,L^dot))$. (See
      @bib:Reiner1975[MO p.~242]).],
    [Let $G$ be a finite group, and $R$ any commutative ring. Let
      $f: G times G -> R^dot$ be a factor set from $G$ into the group of units
      of $R$. We define an $R$-algebra $(R G)_f$, called the _twisted group
      algebra_#idx("twisted group algebra") (of $G$ relative to the factor set
      $f$) as follows:
      $ (R G)_f=plus.o.big_(x in G) R u_x, $
      with multiplication defined by
      $
        u_x alpha=alpha u_x, u_x u_y=f(x,y)u_(x y), forall alpha in R,
        forall x,y in G.
      $
      The terminology “twisted group algebra” is sometimes used in a different
      sense (see @exm:dihedral-group-algebra-reduced-norm and
      @sec:twisted-group-rings).],
  )
] <exm:crossed-products-twisted-group-algebras>

#source(206)
We finally consider $H^0 lr((G,A))$; we have already remarked that
$H^0 lr((G,A)) tilde.equiv Hom_(ZZ G) lr((ZZ,A))$, an obvious consequence of
@rem:ext-properties(ii). Now an element $g in Hom_(ZZ G) lr((ZZ,A))$ is
completely determined by the image $g(1) in A$. Since $ZZ$ is the trivial
$G$-module#idx("trivial G-module"), the image $g(1)$ must also be $G$-trivial.
We set#footnote[
  Later, the $G$-trivial submodule of $A$ will be denoted by $op("inv")_G A$, to
  avoid confusion with the notation for induced modules.
]
$ A^G={a in A: x a=a "for all" x in G}, $
the _$G$-trivial submodule_#idx("trivial submodule")#idx("invariant (G-)") of
$A$. The above remarks show that $Hom_(ZZ G) lr((ZZ,A)) tilde.equiv A^G$ as
additive groups. We now give another proof that $H^0 lr((G,A)) tilde.equiv A^G$.
By definition,
$ H^0 lr((G,A))={f in Hom_(ZZ G) lr((F_0,A)): d_1^* f=0}. $
We identify $Hom_(ZZ G) lr((F_0,A))$ with $A$, by letting $f$ correspond to
$f(thin)=a in A$. We have $d_1^* f=0$ if and only if $(x-1)a=0$ for all
$x in G$, that is, if and only if $a in A^G$. This proves that
$ H^0 lr((G,A)) tilde.equiv A^G tilde.equiv Hom_(ZZ G) lr((ZZ,A)), $
as claimed.

From the properties of $op("Ext")$, we may read off properties of the cohomology
groups. For example, we have
$ H^n lr((G,A))=0 "for" n >= 1 $
for every injective $ZZ G$-module $A$. As another example, we obtain from
@eq:ext-long-exact-second-variable the following:

#proposition[
  For any $G$-module $A$, let $A^G$ denote the $G$-trivial submodule of $A$.
  Then for each exact sequence
  $ 0 -> A -> B -> C -> 0 $
  of left $ZZ G$-modules, there is a long exact sequence of additive groups
  $
    0 -> A^G -> B^G -> C^G -> H^1 lr((G,A)) -> H^1 lr((G,B))
    -> H^1 lr((G,C)) -> H^2 lr((G,A)) -> dots.
  $
] <prop:group-cohomology-long-exact-sequence>

=== The Schur Criterion for Split Extensions <ss:schur-split-extensions>

We shall apply the theory of extensions and $H^2 lr((G,A))$, discussed in
@exm:group-extensions-second-cohomology, to prove a basic result in finite group
theory, attributed to Schur (see Zassenhaus @bib:Zassenhaus1949).

#theorem[
  #source(207)
  Let $H$ be a normal subgroup of a finite group $E$ such that the order
  $abs(H)$ and the index $abs(E":"H)$ are relatively prime. Then there exists a
  subgroup $S <= E$ of order $abs(E":"H)$, and $E$ is a semidirect product
  $H ⋊ S$.
] <th:schur-zassenhaus>
#idx("Schur-Zassenhaus Theorem", target: [@th:schur-zassenhaus])

Before beginning the proof, we remark that in case either $H$ or $E slash H$ is
solvable, Zassenhaus proved @bib:Zassenhaus1949 that any two subgroups of order
$abs(E":"H)$ are conjugate in $E$. This result, together with Theorem
@th:schur-zassenhaus, is usually referred to as the _Schur-Zassenhaus Theorem_.
For later use, we require only the existence theorem @th:schur-zassenhaus. For a
proof of the conjugacy result, see Zassenhaus @bib:Zassenhaus1949, p.~132,
Gorenstein @bib:Gorenstein1968, p.~221 or Huppert @bib:Huppert1967, p.~128.

We begin the proof of Theorem @th:schur-zassenhaus with some preliminary remarks
about extensions. Let
$ 1 -> A -> E arrow.r^pi G -> 1 $ <eq:schur-group-extension>
be a group extension as in @eq:group-extension, where $A$ is an abelian
multiplicative group. A $pi$-_section_#idx("section") is a map $u: G -> E$ such
that $pi(u_x)=x$ for all $x in G$. Each $pi$-section determines an action of $G$
on $A$ by means of the formula
$ x dot a=u_x a u_x^(-1), x in G, a in A, $
and we may then view $A$ as a $ZZ G$-module. Let $f: G times G -> A$ be the
factor set associated with the extension, defined as in
@eq:extension-factor-set:
$ u_x u_y=f(x,y)u_(x y), "where" f(x,y) in A, "for all" x,y in G. $
Condition @eq:factor-set-condition, in multiplicative form, becomes
$
  {x dot f(y,z)}f(x,y z)=f(x y,z)f(x,y) "for all" x,y,z in G,
$ <eq:multiplicative-factor-set>
and is equivalent to the requirement that multiplication of the elements
$\{u_x: x in G\}$ be associative.

We say that the action of $G$ on $A$ is _trivial_ if $x dot a=a$ for all
$x in G$, $a in A$. This occurs if and only if $E$ is a _central extension_#idx(
  "central extension",
) of $G$, which means that the kernel $A$ of the extension
@eq:schur-group-extension is contained in the center of $E$. (For a more
extensive discussion of central extensions, see @ss:central-extensions.)

Another observation is that the extension @eq:schur-group-extension splits if
and only if the factor set $f$ is equivalent to 1 (notation: $f tilde 1$), that
is, the image of $f$ in $H^2 lr((G,A))$ is the identity. By the Definition
@eq:second-cohomology-factor-sets of $H^2 lr((G,A))$, $f tilde 1$ if and only if
$f$ is a principal factor set. By @eq:principal-factor-set, this means that
there exists a map $g: G -> A$ such that
$
  f(x,y)={x dot g(y)}g(x y)^(-1)g(x) "for all" x,y in G.
$ <eq:multiplicative-principal-factor-set>

#source(208)
Moreover, the extension @eq:schur-group-extension splits if and only if there
exists a $pi$-section $v: G -> E$ which is a homomorphism: $v_(x y)=v_x v_y$ for
all $x,y in G$. Using the fact that any two $pi$-sections define the same action
of $G$ on $A$, it is easily verified that a $pi$-section $v$ is a splitting
homomorphism if and only if the map $g: G -> A$ defined by $g(x)=u_x v_x^(-1)$,
$x in G$, satisfies condition @eq:multiplicative-principal-factor-set. It can
also be seen that the condition $f tilde 1$ is equivalent to the splitting of
the extension, as a consequence of the correspondence in @ss:cohomology-groups
between equivalence classes of extensions and elements of $H^2 lr((G,A))$.

#lemma[
  Let $G$ be a finite group acting on a finite abelian multiplicative group $A$.
  Then every element of $H^2 lr((G,A))$ has order dividing both $abs(G)$ and the
  exponent of $A$.
] <lem:second-cohomology-order-exponent>

#proof[
  Let $f: G times G -> A$ be a factor set. Fix $x,y in G$, and define a map
  $g: G -> A$ by
  $ g(y)=product_(z in G) f(y,z). $
  Upon multiplying @eq:multiplicative-factor-set over $z in G$, and rearranging
  terms since $A$ is abelian, we have
  $
    {product_(z in G) x dot f(y,z)}{product_(z in G) f(x,y z)}
    ={product_(z in G) f(x y,z)}{product_(z in G) f(x,y)}.
  $
  Since $y z$ ranges over $G$ as $z$ does, the above formula becomes
  $ {x dot g(y)}g(x)=g(x y)f(x,y)^n, "where" n=abs(G). $
  By @eq:multiplicative-principal-factor-set, this implies that $f(x,y)^n$ is a
  principal factor set, hence every element of $H^2 lr((G,A))$ has order
  dividing $abs(G)$. On the other hand, since $f$ has values in $A$, we clearly
  have $f^m=1$, where $m$ is the exponent of $A$, and the result follows.
]

#corollary[
  Every extension
  $ 1 -> A -> E -> G -> 1 $
  of a finite group $G$ by an abelian group $A$, such that the orders of $A$ and
  $G$ are relatively prime, is a split extension.
] <cor:coprime-abelian-extension-splits>

#proof[
  By Lemma @lem:second-cohomology-order-exponent, in this case we have
  $H^2 lr((G,A))=1$. By the remarks preceding
  @lem:second-cohomology-order-exponent, it follows that the extension splits,
  completing the proof.
]

We are now ready to finish the proof of Theorem @th:schur-zassenhaus. Let
$H lt.closed.eq E$, $G=E slash H$, and assume that the orders $m$ of $H$ and $n$
of $G$ are relatively prime.
#source(209)
It is clearly sufficient to prove that $E$ has a subgroup $S$ of order $n$,
because then $abs(S H)$ will necessarily coincide with $abs(E)$, so that $E$
will be a semidirect product $H ⋊ S$, as in the statement of the theorem.

We use induction on $m$, the theorem being trivial if $m=1$. Assume $m>1$, and
let $p$ be a prime dividing $m$. We note that all Sylow $p$-subgroups of $E$ are
contained in $H$; for $H$ contains at least one, so by normality of $H$ and
Sylow's Theorem, $H$ contains all others. Hence the number of Sylow
$p$-subgroups in $H$ is the same as the number in $E$, and if $P$ is one of
them, we again apply the Sylow theorems (see @bib:CurtisReiner1962[CR (6.7)]) to
obtain
$ abs(E":"N_E lr((P)))=abs(H":"N_H lr((P))). $
Hence
$ abs(N_E lr((P))":"N_H lr((P)))=abs(E":"H)=n. $
Moreover, $N_H lr((P))=H inter N_E lr((P))$, and is normal in $N_E lr((P))$ by
an isomorphism theorem (@bib:CurtisReiner1962[CR (2.8)]). Thus, if $N_E lr((P))$
is properly contained in $E$, we can use the induction hypothesis to conclude
that $N_E lr((P))$, and hence $E$, contains a subgroup of order $n$.

Thus we may now assume that $E=N_E lr((P))$, so that $P$ is normal in $E$, and
hence in $H$. If $P$ is properly contained in $H$, then by induction $E$
contains a subgroup $S$ of order $abs(E":"P)$ isomorphic to $E slash P$. In this
case we also have $abs(H":"P)<m$, and $H slash P$ is a normal subgroup of
$E slash P$ whose order and index are relatively prime. By a second application
of the induction hypothesis, the subgroup $S tilde.equiv
E slash P$ contains a subgroup of order $abs((E slash P) slash (H slash P))
=abs(E":"H)=n$, proving the theorem in this situation.

Finally, we are reduced to the case where $H=P$. If $P$ is abelian, the
extension $E$ of $G$ by $P$ splits, by Corollary
@cor:coprime-abelian-extension-splits. If $P$ is not abelian, its center $Z$ is
nontrivial, is properly contained in $P$, and is a characteristic subgroup of
$P$. Hence $Z$ is normal in $E$. By the induction hypothesis, $E slash Z$
contains a subgroup $U slash Z$ of order $n$, for some proper subgroup $U$ of
$E$. By induction once again, it follows that $U$, and hence $E$, contains a
subgroup of order $n$, and the proof of Theorem @th:schur-zassenhaus is
complete.

=== Tate Cohomology Groups <ss:tate-cohomology>

When $G$ is a finite group, it is sometimes desirable to use the _Tate
cohomology groups_#idx("Tate cohomology group")#idx("cohomology group")
$hat(H)^n lr((G,A))$, $n >= 0$, in place of the usual groups $H^n lr((G,A))$.
The groups $hat(H)^n$ may be defined thus: we set
$ N_G=sum_(x in G) x in ZZ G. $ <eq:group-norm-element>
Then $y N_G=N_G$ for each $y in G$, and indeed $ZZ dot N_G$ is the $G$-trivial
submodule of
#source(210)
$ZZ G$. For any left $G$-module $A$, we define
$
  hat(H)^n lr((G,A))=cases(
    H^n lr((G,A)) quad & n>0, A^G slash N_G A quad & n=0.
  )
$ <eq:tate-nonnegative-definition>
#idx("Tate cohomology group", target: [@eq:tate-nonnegative-definition])
For any $a in A^G$, we have $N_G a=abs(G)a$; therefore the group order $abs(G)$
annihilates $hat(H)^0 lr((G,A))$. This same result holds for $hat(H)^n$, as we
see from the following result, which generalizes Maschke's Theorem @th:maschke,
as well as Lemma @lem:second-cohomology-order-exponent:

#proposition[
  Let $G$ be a finite group of order $abs(G)$, and let $A$ be any left
  $ZZ G$-module. Then
  $ abs(G) dot hat(H)^n lr((G,A))=0, n >= 0. $
] <prop:group-order-annihilates-tate>

#proof[
  We have already established the result for $n=0$, so now let $n >= 1$, and let
  $ f: underbrace(G times dots times G, n) -> A $
  be a representative of a cohomology class in $H^n lr((G,A))$. Then
  $d_(n+1)^* f=0$, and thus
  $
    0=x_1 f(x_2,dots,x_(n+1))
    +sum_(i=1)^(n-1) lr((-1))^i f(x_1,dots,x_i x_(i+1),dots,x_(n+1)) \
    +(-1)^n f(x_1,dots,x_n x_(n+1))+(-1)^(n+1)f(x_1,dots,x_n)
  $
  for all $x_i in G$. Sum over all $x_(n+1) in G$, and set
  $ g(x_1,dots,x_(n-1))=sum_(x in G) f(x_1,dots,x_(n-1),x). $
  Then we obtain
  $
    0=x_1 g(x_2,dots,x_n)+sum_(i=1)^(n-1) lr((-1))^i
    g(x_1,dots,x_i x_(i+1),dots,x_n) \
    +(-1)^n g(x_1,dots,x_(n-1))+(-1)^(n+1)abs(G) dot f(x_1,dots,x_n)
  $
  for all $x_i in G$. This gives
  $ 0=d_n^* g+(-1)^(n+1)abs(G)f, $
  whence $abs(G) dot f in im d_n^*$. This proves that $abs(G)$ annihilates
  $hat(H)^n lr((G,A))$, as claimed.
]

#source(211)
Let us turn next to a brief description of the homology groups $H_n lr((G,A))$,
$n >= 0$, where $A$ is a left $ZZ G$-module and $G$ is an arbitrary group (not
necessarily finite). By slightly modifying the construction @eq:bar-resolution,
we may obtain a free $ZZ G$-resolution
$ dots -> X_2 arrow.r^(d_2) X_1 arrow.r^(d_1) X_0 arrow.r^(d_0) ZZ -> 0 $
of the trivial _right_ $G$-module $ZZ$. Now let $A$ be any left $ZZ G$-module;
to construct the groups $op("Tor")_n^(ZZ G) lr((ZZ,A))$, we form the sequence of
additive groups
$
  dots -> X_2 times.o_(ZZ G) A arrow.r^(d_2 times.o 1) X_1 times.o_(ZZ G) A
  arrow.r^(d_1 times.o 1) X_0 times.o_(ZZ G) A -> 0.
$
Then we have (by definition)
$
  H_n lr((G,A))=op("Tor")_n^(ZZ G) lr((ZZ,A))
  =frac(ker(d_n times.o 1), im(d_(n+1) times.o 1)), n >= 1,
$
#idx("homology groups")
and
$ H_0 lr((G,A))=op("Tor")_0^(ZZ G) lr((ZZ,A)) tilde.equiv ZZ times.o_(ZZ G) A. $
We shall calculate $H_0 lr((G,A))$ explicitly. Let $epsilon: ZZ G -> ZZ$ be the
_augmentation map_#idx("augmentation map"), that is, $epsilon$ is the ring
homomorphism given by
$ epsilon(sum_(x in G) alpha_x x)=sum alpha_x. $ <eq:augmentation-map>
The kernel of $epsilon$ is the _augmentation ideal_#idx("augmentation ideal")
$I_G$ of $ZZ G$; clearly $I_G$ is a two-sided ideal of $ZZ G$, and it is easily
seen that
$ I_G=plus.o.big_(x in G, x != 1) ZZ dot (x-1). $ <eq:augmentation-ideal-basis>
There is an exact sequence of right $ZZ G$-modules
$ 0 -> I_G -> ZZ G -> ZZ -> 0, $ <eq:augmentation-exact-sequence>
where $ZZ$ is the trivial $G$-module. Hence by @prop:tensor-right-exact the
sequence
$ I_G times.o A -> ZZ G times.o A -> ZZ times.o A -> 0 $
is exact, where $times.o$ means $times.o_(ZZ G)$. But under the isomorphism
$ZZ G times.o A tilde.equiv A$ (see @eq:tensor-regular-module), the image of
$I_G times.o A$ is precisely
$ I_G A={sum_(x in G)(x-1)a_x: a_x in A}, $
#source(212)
where only finite sums are intended. Hence we have
$ ZZ times.o_(ZZ G) A tilde.equiv A slash I_G A. $
(In fact, $A slash I_G A$ is the largest $G$-trivial quotient of the left
$G$-module $A$.) This gives
$ H_0 lr((G,A)) tilde.equiv A slash I_G A. $
We shall not give explicit formulas for $H_n lr((G,A))$ for $n >= 1$, since
these are rather complicated.

Properties of the homology groups $H_n lr((G,A))$ may be read off from those of
the torsion groups $op("Tor")_n$. Thus we have
$ H_n lr((G,A))=0 "for" n >= 1, $
if $A$ is any projective $ZZ G$-module (or more generally, if $A$ is flat).
Likewise, an exact sequence $0 -> A -> B -> C -> 0$ of left $ZZ G$-modules
yields a long exact sequence of homology groups (see
@th:tor-long-exact-sequence)
$
  dots -> H_2 lr((G,C)) -> H_1 lr((G,A)) -> H_1 lr((G,B)) -> H_1 lr((G,C)) \
  -> A slash I_G A -> B slash I_G B -> C slash I_G C -> 0.
$
When $G$ is finite, one introduces the Tate cohomology groups
$hat(H)^n lr((G,A))$, $n <= -1$, as follows: for a left $ZZ G$-module $A$, let
$ attach(A, bl: N_G)={a in A: N_G a=0}, $ <eq:norm-kernel>
where $N_G$ is given in @eq:group-norm-element. We now put
$
  hat(H)^n lr((G,A))=cases(
    H_(-n-1) lr((G,A)) quad & n <= -2,
    attach(A, bl: N_G) slash I_G A quad & n=-1.
  )
$ <eq:tate-negative-definition>
#idx("Tate cohomology group", target: [@eq:tate-negative-definition])
Thus $hat(H)^(-1) lr((G,A))$ is a submodule of $H_0 lr((G,A))$. The assertion in
@prop:group-order-annihilates-tate remains valid for $n<0$, though we shall not
prove it here.

Suppose now that $G$ is a finite cyclic group, with generator $x$ of order $m$.
Let
$ D=x-1, N=x^(m-1)+x^(m-2)+dots+x+1, $
viewed as left multiplications on the integral group ring $ZZ G$. It is easily
found that the sequence of left $ZZ G$-modules
$
  dots -> ZZ G arrow.r^D ZZ G arrow.r^N ZZ G arrow.r^D dots
  arrow.r^N ZZ G arrow.r^D ZZ G arrow.r^epsilon ZZ -> 0
$
#source(213)
is exact, where $epsilon$ is the augmentation map. This sequence yields a free
resolution of the trivial $G$-module $ZZ$; we may use it to compute the groups
$H^n lr((G,A))$ for any left $G$-module $A$. Specifically, we form the sequence
$
  0 -> Hom_(ZZ G) lr((ZZ G,A)) arrow.r^(D^*) Hom_(ZZ G) lr((ZZ G,A))
  arrow.r^(N^*) Hom_(ZZ G) lr((ZZ G,A)) arrow.r^(D^*) dots.
$
Identify each $Hom_(ZZ G) lr((ZZ G,A))$ with $A$; since $ZZ G$ is commutative,
the maps $D^*$, $N^*$ are left $ZZ G$-homomorphisms. Then
$
  ker D^* tilde.equiv {a in A: D a=0}=A^G,
  ker N^* tilde.equiv {a in A: N a=0}=attach(A, bl: N), \
  im D^*=(x-1)A=I_G A, im N^*=N A.
$
We obtain
$
  cases(
    hat(H)^1 lr((G,A)) tilde.equiv hat(H)^3 lr((G,A)) tilde.equiv dots
    tilde.equiv attach(A, bl: N) slash I_G A\,,
    hat(H)^2 lr((G,A)) tilde.equiv hat(H)^4 lr((G,A)) tilde.equiv dots
    tilde.equiv A^G slash N A.
  )
$ <eq:cyclic-tate-periodicity>
It is easily checked that for all $n in ZZ$,
$
  hat(H)^(2n+1) lr((G,A)) tilde.equiv attach(A, bl: N) slash I_G A,
  hat(H)^(2n) lr((G,A)) tilde.equiv A^G slash N A.
$
Throughout the rest of the discussion, let $G$ be a finite group. Given a left
$ZZ G$-module $A$, we have defined the Tate cohomology groups
$hat(H)^i lr((G,A))$ for each $i in ZZ$. For $i>0$, we saw that $hat(H)^i$
coincides with the usual cohomology group $H^i$ (see
@eq:tate-nonnegative-definition), while for $i <= -2$, $hat(H)^i$ is a homology
group (see @eq:tate-negative-definition). The modifications introduced for the
values $i=0,-1$ seem at first to be rather arbitrary. However, these
modifications permit us to establish a close relationship between
$\{hat(H)^i,i >= 0\}$ and $\{hat(H)^i,i <= 0\}$; this relationship is vital in
many applications.

We state without proof a number of basic results (see Weiss @bib:Weiss1969 for
proofs):

#proposition[
  Let $A=ZZ G times.o_ZZ X$, where $X$ is any $ZZ$-module (call $A$
  “$G$-induced”). Then
  $ hat(H)^n lr((G,A))=0 "for all" n in ZZ. $
] <prop:induced-tate-acyclic>
#idx("G-induced module", target: [@prop:induced-tate-acyclic])
#idx("induced module", target: [@prop:induced-tate-acyclic])

#proposition(title: [Long Exact Sequence])[
  Let
  $ 0 -> A -> B -> C -> 0 $
  be an exact sequence of $ZZ G$-modules. Then there is a long exact sequence of
  #source(214)
  additive groups
  $
    dots -> hat(H)^(-2) lr((G,A)) -> hat(H)^(-2) lr((G,B))
    -> hat(H)^(-2) lr((G,C)) \
    -> hat(H)^(-1) lr((G,A)) -> hat(H)^(-1) lr((G,B)) -> hat(H)^(-1) lr((G,C)) \
    -> hat(H)^0 lr((G,A)) -> hat(H)^0 lr((G,B)) -> hat(H)^0 lr((G,C)) \
    -> hat(H)^1 lr((G,A)) -> hat(H)^1 lr((G,B)) -> hat(H)^1 lr((G,C))
    -> hat(H)^2 lr((G,A)) -> dots.
  $
] <prop:tate-long-exact-sequence>
#idx(
  "long exact sequence for Tate cohomology groups",
  target: [@prop:tate-long-exact-sequence],
)

#corollary(title: [Dimension shifting])[
  Let $0 -> A -> B -> C -> 0$ be a $ZZ G$-exact sequence, in which $B$ is
  $G$-induced. Then
  $ hat(H)^i lr((G,C)) tilde.equiv hat(H)^(i+1) lr((G,A)), i in ZZ. $
] <cor:tate-dimension-shifting>
#idx("dimension shifting", target: [@cor:tate-dimension-shifting])

In particular, let $I_G$ be the augmentation ideal of $ZZ G$, so there is an
exact sequence of left $ZZ G$-modules given by @eq:augmentation-exact-sequence.
Then we obtain from @cor:tate-dimension-shifting
$ hat(H)^i lr((G,ZZ)) tilde.equiv hat(H)^(i+1) lr((G,I_G)), i in ZZ. $
Now every element of $I_G$ is annihilated by $N_G$ (see @eq:group-norm-element),
so we have by @eq:tate-negative-definition:
$
  hat(H)^(-1) lr((G,I_G)) tilde.equiv I_G slash I_G^2.
$ <eq:tate-augmentation-ideal>
On the other hand, letting $G'$ denote the commutator subgroup of $G$, there is
an isomorphism
$ G slash G' tilde.equiv I_G slash I_G^2, $
defined by sending $x G'$ onto $x-1+I_G^2$, $x in G$. Thus we have
$
  hat(H)^(-2) lr((G,ZZ)) tilde.equiv hat(H)^(-1) lr((G,I_G))
  tilde.equiv G slash G'.
$ <eq:tate-abelianization>
This result is of fundamental importance in the cohomological approach to class
field theory.

As an illustration of the above techniques, we prove the following result,
(Borevich-Faddeev @bib:Borevich1956, Gruenberg-Roggenkamp @bib:Gruenberg1975)
which is rather complicated to verify directly:

#proposition[
  The augmentation ideal $I_G$ is a cyclic $ZZ G$-module if and only if $G$ is a
  cyclic group.
] <prop:cyclic-augmentation-ideal>

#proof[
  If $G=⟨x⟩$ is cyclic, then clearly $I_G=ZZ G dot (x-1)$, so $I_G$ has a single
  generator as $ZZ G$-module. Conversely, assume that $I_G$ is a cyclic module;
  then there exists a $ZZ G$-exact sequence
  $ 0 -> A -> ZZ G -> I_G -> 0. $
  #source(215)
  Tensoring with $QQ$, we obtain
  $ QQ G tilde.equiv QQ A plus.o QQ I_G. $
  On the other hand, tensoring @eq:augmentation-exact-sequence with $QQ$ yields
  $ QQ G tilde.equiv QQ I_G plus.o QQ, $
  where $G$ acts trivially on the second summand $QQ$. Therefore
  $QQ A tilde.equiv QQ$, which implies at once that $A tilde.equiv ZZ$ (with
  trivial $G$-action). Hence the sequence
  $ 0 -> ZZ -> ZZ G -> I_G -> 0 $
  is exact. Therefore by @cor:tate-dimension-shifting
  $ hat(H)^(-1) lr((G,I_G)) tilde.equiv hat(H)^0 lr((G,ZZ)). $
  But $hat(H)^0 lr((G,ZZ)) tilde.equiv ZZ slash n ZZ$ by
  @eq:tate-nonnegative-definition, where $n=abs(G)$. Combining this result with
  @eq:tate-abelianization, we obtain
  $ G slash G' tilde.equiv ZZ slash n ZZ. $
  But $abs(G)=n$, so this isomorphism implies first that $G'=1$, and secondly
  that $G tilde.equiv ZZ slash n ZZ$. We have thus shown that if $I_G$ is a
  cyclic module, then $G$ is a cyclic group. This completes the proof.
]

#remark(numbered: false)[
  Let $G$ be a group of order $n$, and define the ring
  $ ZZ'={a slash b: a,b in ZZ, (b,n)=1}, $
  so $ZZ'$ is a semi-localization of $ZZ$; the nonzero prime ideals of $ZZ'$ are
  of the form $p ZZ'$, where $p$ is a prime divisor of $n$. If $T$ is any f.g.
  $ZZ$-module such that $n T=0$, then we have
  $ ZZ' times.o_ZZ T tilde.equiv T. $
  Now $ZZ'$ is $ZZ$-flat, since $ZZ'$ is a ring of quotients of $ZZ$. Hence
  $ZZ' times.o_ZZ dot$ preserves exactness, and we obtain an exact sequence
  $ 0 -> ZZ' times.o_ZZ I_G -> ZZ' G -> ZZ' -> 0. $
  Here, $ZZ' times.o I_G$ is just the augmentation ideal of $ZZ' G$. Further,
  $ ZZ' G=ZZ G times.o_ZZ ZZ', $
  so $ZZ' G$ is $G$-induced. Thence we have, setting $I'_G=ZZ' times.o_ZZ I_G$,
  $ hat(H)^i lr((G,ZZ')) tilde.equiv hat(H)^(i+1) lr((G,I'_G)). $
  #source(216)
  In particular,
  $
    hat(H)^(-2) lr((G,ZZ')) tilde.equiv hat(H)^(-1) lr((G,I'_G))
    tilde.equiv I'_G slash I_G dot I'_G.
  $
  But
  $
    I'_G slash I_G I'_G tilde.equiv ZZ' times.o_ZZ {I_G slash I_G^2}
    tilde.equiv ZZ' times.o_ZZ (G slash G') tilde.equiv G slash G',
  $
  since $G slash G'$ is annihilated by $n$ (i.e., $(x G')^n=1$ for each
  $x in G$).

  If $G$ is cyclic, then of course $I'_G$ is a cyclic module. The converse also
  holds:
  _If $I'_G$ is a cyclic module, then $G$ is a cyclic group._

  Indeed, if $I'_G$ is a cyclic module, then as in the proof of
  @prop:cyclic-augmentation-ideal we find that
  $
    hat(H)^(-1) lr((G,I'_G)) tilde.equiv hat(H)^0 lr((G,ZZ'))
    tilde.equiv ZZ' slash n ZZ' tilde.equiv ZZ slash n ZZ.
  $
  Thus we obtain $G slash G' tilde.equiv ZZ slash n ZZ$ as before, so $G$ is
  cyclic of order $n$.
]

#exercises-heading

#exercise[
  Let $G$ be an arbitrary group, $I_G$ the augmentation ideal of $ZZ G$, and
  $ZZ$ the trivial $G$-module. Show that
  $ H_1 lr((G,ZZ)) tilde.equiv I_G slash I_G^2 tilde.equiv G slash G'. $

  #hint([@exc:first-homology-abelianization])[
    From @eq:augmentation-exact-sequence we obtain a long exact sequence
    $
      0 -> H_1 lr((G,ZZ)) -> H_0 lr((G,I_G)) -> H_0 lr((G,ZZ G))
      arrow.r^(epsilon_*) H_0 lr((G,ZZ)) -> 0.
    $
    Since $epsilon_*$ is an isomorphism, we get
    $H_1 lr((G,ZZ)) tilde.equiv H_0 lr((G,I_G)) tilde.equiv I_G slash I_G^2$.
    The map $x in G ↦ x-1 in I_G$, yields an isomorphism from the multiplicative
    group $G slash G'$ onto the additive group $I_G slash I_G^2$.
  ]
] <exc:first-homology-abelianization>

#exercise[
  Let $R$ and $S$ be Dedekind domains with quotient fields $K$ and $L$,
  respectively, and suppose that
  $ R subset.eq S, R=S inter K. $
  Show that for each $R$-module $M$, the map $M -> S times.o_R M$ (given by
  $m ↦ 1 times.o m$) is an $R$-monomorphism.

  #hint([@exc:dedekind-extension-tensor-injective])[
    The hypotheses imply that $S slash R$ is $R$-torsionfree, hence $R$-flat by
    Exercise @exc:dedekind-torsionfree-flat. The $R$-exact sequence
    $ 0 -> R -> S -> S slash R -> 0 $
    yields an $R$-exact sequence
    $ op("Tor")_1^R lr((S slash R,M)) -> R times.o_R M -> S times.o_R M, $
    in which the first term is 0.
  ]
] <exc:dedekind-extension-tensor-injective>
